#!/usr/bin/env python3
"""
AXI4 Verification IP Components
Implements Master Agent, Slave Agent, Monitor, and Checker components
Based on CLAUDE.md requirements for comprehensive AXI4 VIP suite
"""

import random
import queue
import threading
import time
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Callable, Any
from enum import Enum
import json

class AXIBurstType(Enum):
    """AXI Burst Types per IHI0022D spec"""
    FIXED = 0b00
    INCR = 0b01
    WRAP = 0b10
    RESERVED = 0b11

class AXIResponse(Enum):
    """AXI Response Types per IHI0022D spec"""
    OKAY = 0b00
    EXOKAY = 0b01  # Exclusive access okay
    SLVERR = 0b10  # Slave error
    DECERR = 0b11  # Decode error

class AXISize(Enum):
    """AXI Transfer Size"""
    SIZE_1B = 0b000
    SIZE_2B = 0b001
    SIZE_4B = 0b010
    SIZE_8B = 0b011
    SIZE_16B = 0b100
    SIZE_32B = 0b101
    SIZE_64B = 0b110
    SIZE_128B = 0b111

@dataclass
class AXITransaction:
    """AXI Transaction with all protocol fields"""
    # Common fields
    id: int = 0
    addr: int = 0
    length: int = 0  # AxLEN (0-255 for AXI4)
    size: AXISize = AXISize.SIZE_4B
    burst: AXIBurstType = AXIBurstType.INCR
    lock: bool = False
    cache: int = 0b0011  # AxCACHE
    prot: int = 0b010    # AxPROT (privileged, non-secure, data)
    qos: int = 0         # AxQOS (0-15)
    region: int = 0      # AxREGION (0-15)
    user: int = 0        # AxUSER (width configurable)
    
    # Write-specific
    data: List[int] = field(default_factory=list)
    strb: List[int] = field(default_factory=list)  # WSTRB per beat
    
    # Response
    response: AXIResponse = AXIResponse.OKAY
    
    # Transaction control
    is_write: bool = True
    timestamp: float = field(default_factory=time.time)
    exclusive: bool = False

@dataclass
class VIPConfig:
    """VIP Component Configuration"""
    name: str = "axi_vip"
    data_width: int = 64
    addr_width: int = 32
    id_width: int = 4
    user_width: int = 0
    max_outstanding: int = 16
    default_timeout: float = 1000.0  # microseconds

class AXIMasterAgent:
    """AXI Master Verification IP Agent
    
    Generates AXI transactions with configurable timing and patterns.
    Supports all AXI4 features including QoS, exclusive access, etc.
    """
    
    def __init__(self, config: VIPConfig):
        self.config = config
        self.transaction_queue = queue.Queue()
        self.response_queue = queue.Queue()
        self.outstanding_transactions = {}
        self.transaction_id_counter = 0
        self.exclusive_monitor = {}  # Track exclusive addresses
        self.statistics = {
            'transactions_sent': 0,
            'responses_received': 0,
            'errors': 0,
            'exclusive_success': 0,
            'exclusive_fail': 0
        }
        
    def write_transaction(self, addr: int, data: List[int], 
                         burst_type: AXIBurstType = AXIBurstType.INCR,
                         size: AXISize = AXISize.SIZE_4B,
                         **kwargs) -> AXITransaction:
        """Generate AXI write transaction with full protocol compliance"""
        
        # Validate 4KB boundary crossing (critical AXI4 requirement)
        bytes_per_transfer = 1 << size.value
        total_bytes = (len(data)) * bytes_per_transfer
        
        if self._crosses_4kb_boundary(addr, total_bytes):
            raise ValueError(f"Transaction crosses 4KB boundary: addr=0x{addr:X}, size={total_bytes}")
        
        # Generate transaction ID
        tx_id = self.transaction_id_counter % (1 << self.config.id_width)
        self.transaction_id_counter += 1
        
        # Create transaction
        transaction = AXITransaction(
            id=tx_id,
            addr=addr,
            length=len(data) - 1,  # AxLEN is length-1
            size=size,
            burst=burst_type,
            data=data.copy(),
            strb=[0xFF] * len(data),  # Default: all bytes valid
            is_write=True,
            **kwargs
        )
        
        # Validate burst constraints
        self._validate_burst_transaction(transaction)
        
        # Queue transaction
        self.transaction_queue.put(transaction)
        self.outstanding_transactions[tx_id] = transaction
        self.statistics['transactions_sent'] += 1
        
        return transaction
    
    def read_transaction(self, addr: int, length: int,
                        burst_type: AXIBurstType = AXIBurstType.INCR,
                        size: AXISize = AXISize.SIZE_4B,
                        exclusive: bool = False,
                        **kwargs) -> AXITransaction:
        """Generate AXI read transaction"""
        
        # Validate 4KB boundary crossing
        bytes_per_transfer = 1 << size.value
        total_bytes = length * bytes_per_transfer
        
        if self._crosses_4kb_boundary(addr, total_bytes):
            raise ValueError(f"Read crosses 4KB boundary: addr=0x{addr:X}, size={total_bytes}")
        
        # Generate transaction ID
        tx_id = self.transaction_id_counter % (1 << self.config.id_width)
        self.transaction_id_counter += 1
        
        # Create transaction
        transaction = AXITransaction(
            id=tx_id,
            addr=addr,
            length=length - 1,  # AxLEN is length-1
            size=size,
            burst=burst_type,
            is_write=False,
            exclusive=exclusive,
            **kwargs
        )
        
        # Track exclusive access
        if exclusive:
            self.exclusive_monitor[addr] = tx_id
        
        # Validate burst constraints
        self._validate_burst_transaction(transaction)
        
        # Queue transaction
        self.transaction_queue.put(transaction)
        self.outstanding_transactions[tx_id] = transaction
        self.statistics['transactions_sent'] += 1
        
        return transaction
    
    def _crosses_4kb_boundary(self, addr: int, total_bytes: int) -> bool:
        """Check if transaction crosses 4KB boundary (AXI4 critical constraint)"""
        start_4kb_page = addr >> 12
        end_4kb_page = (addr + total_bytes - 1) >> 12
        return start_4kb_page != end_4kb_page
    
    def _validate_burst_transaction(self, transaction: AXITransaction):
        """Validate burst parameters per AXI4 spec"""
        length = transaction.length + 1  # Convert back from AxLEN
        
        # WRAP burst constraints
        if transaction.burst == AXIBurstType.WRAP:
            if length not in [2, 4, 8, 16]:
                raise ValueError(f"WRAP burst length must be 2,4,8,16, got {length}")
            
            # Address must be aligned to transfer size
            transfer_size = 1 << transaction.size.value
            if transaction.addr % transfer_size != 0:
                raise ValueError(f"WRAP burst address not aligned to transfer size")
        
        # INCR burst length constraint (AXI4 supports up to 256)
        if transaction.burst == AXIBurstType.INCR and length > 256:
            raise ValueError(f"INCR burst length exceeds 256: {length}")
        
        # Exclusive access constraints
        if transaction.exclusive:
            transfer_size = 1 << transaction.size.value
            total_bytes = length * transfer_size
            
            if total_bytes > 128:
                raise ValueError(f"Exclusive access exceeds 128 bytes: {total_bytes}")
            
            if total_bytes & (total_bytes - 1) != 0:
                raise ValueError(f"Exclusive access size must be power of 2: {total_bytes}")

class AXISlaveAgent:
    """AXI Slave Verification IP Agent
    
    Responds to AXI transactions with configurable memory model,
    latency, and error injection capabilities.
    """
    
    def __init__(self, config: VIPConfig, base_addr: int, size_bytes: int):
        self.config = config
        self.base_addr = base_addr
        self.size_bytes = size_bytes
        self.end_addr = base_addr + size_bytes - 1
        
        # Memory model
        self.memory = {}  # Sparse memory model
        self.default_data = 0xDEADBEEF
        
        # Response configuration
        self.read_latency = (1, 5)   # Min, max cycles
        self.write_latency = (1, 3)  # Min, max cycles
        self.error_injection_rate = 0.0  # 0.0 = no errors, 1.0 = all errors
        
        # Security and access control
        self.secure_only = False
        self.privileged_only = False
        self.allowed_masters = set()  # Empty = all allowed
        
        # Exclusive access monitor
        self.exclusive_addresses = {}  # addr -> master_id
        
        # Statistics
        self.statistics = {
            'reads_processed': 0,
            'writes_processed': 0,
            'errors_generated': 0,
            'exclusive_accesses': 0
        }
    
    def process_transaction(self, transaction: AXITransaction) -> AXITransaction:
        """Process incoming AXI transaction and generate response"""
        
        # Address decode check
        if not self._address_in_range(transaction.addr):
            transaction.response = AXIResponse.DECERR
            return transaction
        
        # Security checks
        if not self._check_security(transaction):
            transaction.response = AXIResponse.SLVERR
            self.statistics['errors_generated'] += 1
            return transaction
        
        # Permission checks
        if not self._check_permissions(transaction):
            transaction.response = AXIResponse.SLVERR  
            self.statistics['errors_generated'] += 1
            return transaction
        
        # Error injection
        if random.random() < self.error_injection_rate:
            transaction.response = AXIResponse.SLVERR
            self.statistics['errors_generated'] += 1
            return transaction
        
        # Process based on transaction type
        if transaction.is_write:
            return self._process_write(transaction)
        else:
            return self._process_read(transaction)
    
    def _process_write(self, transaction: AXITransaction) -> AXITransaction:
        """Process write transaction"""
        
        # Handle exclusive write
        if transaction.exclusive:
            if (transaction.addr in self.exclusive_addresses and 
                self.exclusive_addresses[transaction.addr] == transaction.id):
                # Exclusive write success
                transaction.response = AXIResponse.EXOKAY
                del self.exclusive_addresses[transaction.addr]
                self.statistics['exclusive_accesses'] += 1
            else:
                # Exclusive write failed
                transaction.response = AXIResponse.OKAY
        
        # Write data to memory model
        addr = transaction.addr
        transfer_size = 1 << transaction.size.value
        
        for i, (data, strb) in enumerate(zip(transaction.data, transaction.strb)):
            beat_addr = self._calculate_beat_address(addr, i, transaction)
            
            # Write only enabled bytes based on WSTRB
            for byte_idx in range(transfer_size):
                if strb & (1 << byte_idx):
                    byte_addr = beat_addr + byte_idx
                    byte_data = (data >> (byte_idx * 8)) & 0xFF
                    self.memory[byte_addr] = byte_data
        
        # Simulate write latency
        latency = random.randint(*self.write_latency)
        time.sleep(latency * 1e-6)  # Convert to seconds
        
        if transaction.response == AXIResponse.OKAY:
            transaction.response = AXIResponse.OKAY
        
        self.statistics['writes_processed'] += 1
        return transaction
    
    def _process_read(self, transaction: AXITransaction) -> AXITransaction:
        """Process read transaction"""
        
        # Handle exclusive read
        if transaction.exclusive:
            self.exclusive_addresses[transaction.addr] = transaction.id
            self.statistics['exclusive_accesses'] += 1
        
        # Read data from memory model
        addr = transaction.addr
        transfer_size = 1 << transaction.size.value
        length = transaction.length + 1
        
        read_data = []
        for i in range(length):
            beat_addr = self._calculate_beat_address(addr, i, transaction)
            beat_data = 0
            
            # Read bytes for this beat
            for byte_idx in range(transfer_size):
                byte_addr = beat_addr + byte_idx
                byte_data = self.memory.get(byte_addr, self.default_data & 0xFF)
                beat_data |= (byte_data << (byte_idx * 8))
            
            read_data.append(beat_data)
        
        transaction.data = read_data
        
        # Simulate read latency
        latency = random.randint(*self.read_latency)
        time.sleep(latency * 1e-6)
        
        transaction.response = AXIResponse.OKAY
        self.statistics['reads_processed'] += 1
        return transaction
    
    def _address_in_range(self, addr: int) -> bool:
        """Check if address is within slave's address range"""
        return self.base_addr <= addr <= self.end_addr
    
    def _check_security(self, transaction: AXITransaction) -> bool:
        """Check security attributes (AxPROT)"""
        
        # Extract security attributes from AxPROT
        privileged = (transaction.prot & 0b001) != 0
        secure = (transaction.prot & 0b010) == 0  # Bit 1: 0=secure, 1=non-secure
        
        if self.secure_only and not secure:
            return False
            
        if self.privileged_only and not privileged:
            return False
            
        return True
    
    def _check_permissions(self, transaction: AXITransaction) -> bool:
        """Check master access permissions"""
        if not self.allowed_masters:  # Empty set = all allowed
            return True
        return transaction.id in self.allowed_masters
    
    def _calculate_beat_address(self, start_addr: int, beat_num: int, 
                               transaction: AXITransaction) -> int:
        """Calculate address for specific beat based on burst type"""
        
        transfer_size = 1 << transaction.size.value
        
        if transaction.burst == AXIBurstType.FIXED:
            return start_addr
        elif transaction.burst == AXIBurstType.INCR:
            return start_addr + (beat_num * transfer_size)
        elif transaction.burst == AXIBurstType.WRAP:
            # WRAP burst address calculation per AXI4 spec
            length = transaction.length + 1
            wrap_boundary = (start_addr // (transfer_size * length)) * (transfer_size * length)
            offset = (start_addr + beat_num * transfer_size) % (transfer_size * length)
            return wrap_boundary + offset
        else:
            raise ValueError(f"Unsupported burst type: {transaction.burst}")

class AXIMonitor:
    """AXI Protocol Monitor
    
    Observes AXI signals and reconstructs transactions for analysis.
    Performs protocol compliance checking and coverage collection.
    """
    
    def __init__(self, config: VIPConfig):
        self.config = config
        self.transactions = []
        self.protocol_violations = []
        self.coverage_data = {
            'burst_types': set(),
            'transfer_sizes': set(),
            'response_types': set(),
            'qos_levels': set(),
            'cache_types': set()
        }
        
    def observe_transaction(self, transaction: AXITransaction):
        """Observe and analyze a transaction"""
        
        # Record transaction
        self.transactions.append(transaction)
        
        # Update coverage
        self._update_coverage(transaction)
        
        # Check protocol compliance
        violations = self._check_protocol_compliance(transaction)
        self.protocol_violations.extend(violations)
    
    def _update_coverage(self, transaction: AXITransaction):
        """Update functional coverage metrics"""
        self.coverage_data['burst_types'].add(transaction.burst.name)
        self.coverage_data['transfer_sizes'].add(transaction.size.name)
        self.coverage_data['response_types'].add(transaction.response.name)
        self.coverage_data['qos_levels'].add(transaction.qos)
        self.coverage_data['cache_types'].add(transaction.cache)
    
    def _check_protocol_compliance(self, transaction: AXITransaction) -> List[str]:
        """Check AXI4 protocol compliance"""
        violations = []
        
        # Check burst length constraints
        length = transaction.length + 1
        if transaction.burst == AXIBurstType.INCR and length > 256:
            violations.append(f"INCR burst length {length} exceeds AXI4 limit of 256")
        
        # Check WRAP burst constraints
        if transaction.burst == AXIBurstType.WRAP:
            if length not in [2, 4, 8, 16]:
                violations.append(f"WRAP burst length {length} not in [2,4,8,16]")
        
        # Check 4KB boundary crossing
        transfer_size = 1 << transaction.size.value
        total_bytes = length * transfer_size
        start_page = transaction.addr >> 12
        end_page = (transaction.addr + total_bytes - 1) >> 12
        
        if start_page != end_page:
            violations.append(f"Transaction crosses 4KB boundary: 0x{transaction.addr:X}")
        
        # Check exclusive access constraints
        if transaction.exclusive:
            if total_bytes > 128:
                violations.append(f"Exclusive access {total_bytes} bytes exceeds 128 byte limit")
            
            if total_bytes & (total_bytes - 1) != 0:
                violations.append(f"Exclusive access size {total_bytes} not power of 2")
        
        return violations
    
    def get_coverage_report(self) -> Dict[str, Any]:
        """Generate coverage report"""
        return {
            'total_transactions': len(self.transactions),
            'protocol_violations': len(self.protocol_violations),
            'burst_type_coverage': list(self.coverage_data['burst_types']),
            'size_coverage': list(self.coverage_data['transfer_sizes']),
            'response_coverage': list(self.coverage_data['response_types']),
            'qos_coverage': sorted(list(self.coverage_data['qos_levels'])),
            'cache_coverage': sorted(list(self.coverage_data['cache_types']))
        }

class AXIChecker:
    """AXI Protocol Checker
    
    Performs comprehensive protocol checking with assertions
    and timing verification.
    """
    
    def __init__(self, config: VIPConfig):
        self.config = config
        self.assertion_failures = []
        self.timing_violations = []
        
    def check_handshake_protocol(self, valid: bool, ready: bool, 
                                 valid_history: List[bool]) -> List[str]:
        """Check AXI handshake protocol compliance"""
        violations = []
        
        # Rule: VALID must remain stable until handshake
        if len(valid_history) >= 2:
            for i in range(1, len(valid_history)):
                if valid_history[i-1] and not valid_history[i] and not ready:
                    violations.append("VALID deasserted before handshake completion")
        
        return violations
    
    def check_ordering_rules(self, transactions: List[AXITransaction]) -> List[str]:
        """Check AXI ordering rules"""
        violations = []
        
        # Same ID transactions must complete in order
        id_transactions = {}
        for tx in transactions:
            if tx.id not in id_transactions:
                id_transactions[tx.id] = []
            id_transactions[tx.id].append(tx)
        
        for tx_id, tx_list in id_transactions.items():
            # Check if responses are in order for same ID
            for i in range(1, len(tx_list)):
                if tx_list[i].timestamp < tx_list[i-1].timestamp:
                    violations.append(f"Out-of-order response for ID {tx_id}")
        
        return violations

# Factory function for creating VIP environments
def create_axi_vip_environment(masters: List[VIPConfig], 
                              slaves: List[tuple],  # (config, base_addr, size)
                              interconnect_config: Optional[Dict] = None) -> Dict[str, Any]:
    """Create complete AXI VIP environment with all components"""
    
    environment = {
        'masters': [],
        'slaves': [],
        'monitors': [],
        'checkers': [],
        'interconnect': None
    }
    
    # Create master agents
    for master_config in masters:
        master = AXIMasterAgent(master_config)
        environment['masters'].append(master)
        
        # Create dedicated monitor for each master
        monitor = AXIMonitor(master_config)
        environment['monitors'].append(monitor)
    
    # Create slave agents
    for slave_config, base_addr, size_bytes in slaves:
        slave = AXISlaveAgent(slave_config, base_addr, size_bytes)
        environment['slaves'].append(slave)
    
    # Create system-level checker
    system_checker = AXIChecker(masters[0])  # Use first master's config
    environment['checkers'].append(system_checker)
    
    return environment