#!/usr/bin/env python3
"""
AXI4 Test Sequence Generator
Generates comprehensive test sequences for AXI4 VIP validation
Based on CLAUDE.md requirements for test sequence development
"""

import random
import math
from typing import List, Dict, Generator, Tuple, Optional
from dataclasses import dataclass
from axi_vip_components import (
    AXITransaction, AXIBurstType, AXIResponse, AXISize, 
    AXIMasterAgent, AXISlaveAgent, VIPConfig
)

@dataclass
class TestScenarioConfig:
    """Configuration for test scenarios"""
    name: str
    description: str
    num_transactions: int = 100
    address_range: Tuple[int, int] = (0x80000000, 0x8FFFFFFF)
    data_patterns: List[str] = None
    error_injection: bool = False
    stress_level: int = 1  # 1=normal, 5=maximum stress
    
    def __post_init__(self):
        if self.data_patterns is None:
            self.data_patterns = ['random', 'walking_ones', 'alternating']

class AXITestSequenceGenerator:
    """Generate comprehensive AXI4 test sequences"""
    
    def __init__(self, master: AXIMasterAgent, config: TestScenarioConfig):
        self.master = master
        self.config = config
        self.transaction_history = []
        
        # Data pattern generators
        self.pattern_generators = {
            'random': self._generate_random_data,
            'walking_ones': self._generate_walking_ones,
            'walking_zeros': self._generate_walking_zeros,
            'alternating': self._generate_alternating_pattern,
            'address_pattern': self._generate_address_pattern,
            'incremental': self._generate_incremental_pattern
        }
    
    def generate_basic_sequences(self) -> List[AXITransaction]:
        """Generate basic transaction sequences (CLAUDE.md requirement)"""
        sequences = []
        
        print(f"Generating basic sequences for {self.config.name}...")
        
        # Single read/write operations
        sequences.extend(self._generate_single_transactions())
        
        # All burst type sequences
        sequences.extend(self._generate_burst_type_sequences())
        
        # Data width and WSTRB combinations
        sequences.extend(self._generate_strb_variations())
        
        return sequences
    
    def generate_advanced_sequences(self) -> List[AXITransaction]:
        """Generate advanced feature sequences (CLAUDE.md requirement)"""
        sequences = []
        
        print(f"Generating advanced sequences for {self.config.name}...")
        
        # Out-of-order transaction tests
        sequences.extend(self._generate_out_of_order_tests())
        
        # Same-ID ordering tests
        sequences.extend(self._generate_same_id_ordering_tests())
        
        # Exclusive access scenarios
        sequences.extend(self._generate_exclusive_access_tests())
        
        # QoS/PROT/REGION variations
        sequences.extend(self._generate_attribute_variations())
        
        return sequences
    
    def generate_error_injection_sequences(self) -> List[AXITransaction]:
        """Generate error injection sequences (CLAUDE.md requirement)"""
        sequences = []
        
        print(f"Generating error injection sequences for {self.config.name}...")
        
        # SLVERR trigger scenarios
        sequences.extend(self._generate_slverr_scenarios())
        
        # DECERR trigger scenarios  
        sequences.extend(self._generate_decerr_scenarios())
        
        # Illegal burst generation
        sequences.extend(self._generate_illegal_burst_tests())
        
        # Protocol violation tests
        sequences.extend(self._generate_protocol_violation_tests())
        
        return sequences
    
    def generate_stress_test_sequences(self) -> List[AXITransaction]:
        """Generate stress test scenarios (CLAUDE.md requirement)"""
        sequences = []
        
        print(f"Generating stress test sequences for {self.config.name}...")
        
        # High throughput tests
        sequences.extend(self._generate_high_throughput_tests())
        
        # Fully randomized scenarios
        sequences.extend(self._generate_randomized_scenarios())
        
        # Multi-master contention (if applicable)
        sequences.extend(self._generate_contention_scenarios())
        
        # Corner case coverage
        sequences.extend(self._generate_corner_cases())
        
        return sequences
    
    def _generate_single_transactions(self) -> List[AXITransaction]:
        """Generate single read/write operations"""
        transactions = []
        base_addr = self.config.address_range[0]
        
        for i in range(10):  # 10 single transactions
            addr = base_addr + (i * 64)  # 64-byte spacing
            
            # Single write
            data = [self._get_pattern_data('random', i, 1)[0]]
            tx_write = self.master.write_transaction(
                addr=addr,
                data=data,
                burst_type=AXIBurstType.INCR,
                size=AXISize.SIZE_4B
            )
            transactions.append(tx_write)
            
            # Single read
            tx_read = self.master.read_transaction(
                addr=addr,
                length=1,
                burst_type=AXIBurstType.INCR,
                size=AXISize.SIZE_4B
            )
            transactions.append(tx_read)
        
        return transactions
    
    def _generate_burst_type_sequences(self) -> List[AXITransaction]:
        """Test all burst types with various lengths"""
        transactions = []
        base_addr = self.config.address_range[0] + 0x1000
        
        # INCR bursts (1, 2, 4, 8, 16, 32, 64, 128, 256)
        for length in [1, 2, 4, 8, 16, 32, 64, 128, 256]:
            addr = base_addr + (length * 0x100)
            data = self._get_pattern_data('incremental', 0, length)
            
            tx = self.master.write_transaction(
                addr=addr,
                data=data,
                burst_type=AXIBurstType.INCR,
                size=AXISize.SIZE_4B
            )
            transactions.append(tx)
        
        # WRAP bursts (2, 4, 8, 16 only)
        for length in [2, 4, 8, 16]:
            # Ensure proper alignment for WRAP
            alignment = length * 4  # 4 bytes per transfer
            addr = (base_addr + 0x10000) & ~(alignment - 1)
            
            data = self._get_pattern_data('walking_ones', 0, length)
            
            tx = self.master.write_transaction(
                addr=addr,
                data=data,
                burst_type=AXIBurstType.WRAP,
                size=AXISize.SIZE_4B
            )
            transactions.append(tx)
        
        # FIXED bursts
        for length in [1, 4, 8]:
            addr = base_addr + 0x20000
            data = self._get_pattern_data('alternating', 0, length)
            
            tx = self.master.write_transaction(
                addr=addr,
                data=data,
                burst_type=AXIBurstType.FIXED,
                size=AXISize.SIZE_4B
            )
            transactions.append(tx)
        
        return transactions
    
    def _generate_strb_variations(self) -> List[AXITransaction]:
        """Test different WSTRB patterns for unaligned transfers"""
        transactions = []
        base_addr = self.config.address_range[0] + 0x30000
        
        # Test various WSTRB patterns
        strb_patterns = [
            0x0F,  # Lower 4 bytes
            0xF0,  # Upper 4 bytes  
            0x33,  # Alternate bytes
            0xCC,  # Alternate bytes (inverted)
            0x01,  # Single byte
            0x80,  # Single byte (MSB)
            0xFF   # All bytes
        ]
        
        for i, strb in enumerate(strb_patterns):
            addr = base_addr + (i * 16)
            data = [0x12345678]
            
            tx = self.master.write_transaction(
                addr=addr,
                data=data,
                burst_type=AXIBurstType.INCR,
                size=AXISize.SIZE_8B
            )
            # Override default WSTRB
            tx.strb = [strb]
            transactions.append(tx)
        
        return transactions
    
    def _generate_out_of_order_tests(self) -> List[AXITransaction]:
        """Generate transactions that can complete out-of-order"""
        transactions = []
        base_addr = self.config.address_range[0] + 0x40000
        
        # Create transactions with different IDs (can complete out-of-order)
        for i in range(8):
            addr = base_addr + (i * 0x1000)
            
            # Long read (should take longer)
            long_read = self.master.read_transaction(
                addr=addr,
                length=64,  # Long burst
                burst_type=AXIBurstType.INCR,
                size=AXISize.SIZE_4B
            )
            long_read.id = i  # Different ID
            transactions.append(long_read)
            
            # Short read (should complete faster)
            short_read = self.master.read_transaction(
                addr=addr + 0x100,
                length=1,  # Single transfer
                burst_type=AXIBurstType.INCR,
                size=AXISize.SIZE_4B
            )
            short_read.id = i + 8  # Different ID
            transactions.append(short_read)
        
        return transactions
    
    def _generate_same_id_ordering_tests(self) -> List[AXITransaction]:
        """Generate transactions with same ID (must complete in-order)"""
        transactions = []
        base_addr = self.config.address_range[0] + 0x50000
        
        # All transactions use same ID - must complete in order
        same_id = 5
        
        for i in range(10):
            addr = base_addr + (i * 0x100)
            
            tx = self.master.read_transaction(
                addr=addr,
                length=random.randint(1, 16),
                burst_type=AXIBurstType.INCR,
                size=AXISize.SIZE_4B
            )
            tx.id = same_id  # Force same ID
            transactions.append(tx)
        
        return transactions
    
    def _generate_exclusive_access_tests(self) -> List[AXITransaction]:
        """Generate exclusive access test scenarios"""
        transactions = []
        base_addr = self.config.address_range[0] + 0x60000
        
        # Successful exclusive access sequence
        for i in range(5):
            addr = base_addr + (i * 0x100)
            
            # Exclusive read
            ex_read = self.master.read_transaction(
                addr=addr,
                length=1,
                burst_type=AXIBurstType.INCR,
                size=AXISize.SIZE_4B,
                exclusive=True
            )
            transactions.append(ex_read)
            
            # Exclusive write (should succeed)
            ex_write = self.master.write_transaction(
                addr=addr,
                data=[0xEFC1051E],  # Marker data (EXCLUSIVE in hex-like)
                burst_type=AXIBurstType.INCR,
                size=AXISize.SIZE_4B,
                exclusive=True
            )
            ex_write.id = ex_read.id  # Same ID for pairing
            transactions.append(ex_write)
        
        # Failed exclusive access (intervening write)
        fail_addr = base_addr + 0x1000
        
        # Exclusive read
        ex_read_fail = self.master.read_transaction(
            addr=fail_addr,
            length=1,
            exclusive=True
        )
        transactions.append(ex_read_fail)
        
        # Intervening normal write (breaks exclusive)
        intervening_write = self.master.write_transaction(
            addr=fail_addr,
            data=[0x1EEDCAFE],  # Intervening write marker
        )
        intervening_write.id = ex_read_fail.id + 1  # Different ID
        transactions.append(intervening_write)
        
        # Exclusive write (should fail)
        ex_write_fail = self.master.write_transaction(
            addr=fail_addr,
            data=[0x5D0F41],  # Should fail marker
            exclusive=True
        )
        ex_write_fail.id = ex_read_fail.id  # Same as read
        transactions.append(ex_write_fail)
        
        return transactions
    
    def _generate_attribute_variations(self) -> List[AXITransaction]:
        """Test QoS, PROT, REGION, CACHE variations"""
        transactions = []
        base_addr = self.config.address_range[0] + 0x70000
        
        # QoS variations (0-15)
        for qos in range(16):
            addr = base_addr + (qos * 0x100)
            
            tx = self.master.write_transaction(
                addr=addr,
                data=[qos << 24 | qos << 16 | qos << 8 | qos],
                qos=qos
            )
            transactions.append(tx)
        
        # PROT variations
        prot_configs = [
            0b000,  # Unprivileged, non-secure, data
            0b001,  # Privileged, non-secure, data
            0b010,  # Unprivileged, secure, data
            0b011,  # Privileged, secure, data
            0b100,  # Unprivileged, non-secure, instruction
            0b101,  # Privileged, non-secure, instruction
            0b110,  # Unprivileged, secure, instruction
            0b111,  # Privileged, secure, instruction
        ]
        
        for i, prot in enumerate(prot_configs):
            addr = base_addr + 0x2000 + (i * 0x100)
            
            tx = self.master.read_transaction(
                addr=addr,
                length=1,
                prot=prot
            )
            transactions.append(tx)
        
        # REGION variations (0-15)
        for region in range(16):
            addr = base_addr + 0x3000 + (region * 0x100)
            
            tx = self.master.read_transaction(
                addr=addr,
                length=1,
                region=region
            )
            transactions.append(tx)
        
        # CACHE variations
        cache_configs = [
            0b0000,  # Non-cacheable, non-bufferable
            0b0001,  # Bufferable only
            0b0010,  # Cacheable, non-bufferable
            0b0011,  # Cacheable, bufferable
            0b1111,  # Write-back, write-allocate
        ]
        
        for i, cache in enumerate(cache_configs):
            addr = base_addr + 0x4000 + (i * 0x100)
            
            tx = self.master.write_transaction(
                addr=addr,
                data=[cache << 28 | 0x1234567],
                cache=cache
            )
            transactions.append(tx)
        
        return transactions
    
    def _generate_slverr_scenarios(self) -> List[AXITransaction]:
        """Generate scenarios to trigger SLVERR responses"""
        transactions = []
        
        # Access to secure region without proper PROT
        secure_addr = 0x90000000  # Assume secure region
        
        tx_insecure = self.master.read_transaction(
            addr=secure_addr,
            length=1,
            prot=0b001  # Non-secure access to secure region
        )
        transactions.append(tx_insecure)
        
        # Access beyond slave size
        large_addr = self.config.address_range[1] + 0x1000
        # Align to 4KB boundary to avoid crossing issues
        large_addr = large_addr & ~0xFFF
        
        tx_overrange = self.master.read_transaction(
            addr=large_addr,
            length=1
        )
        transactions.append(tx_overrange)
        
        return transactions
    
    def _generate_decerr_scenarios(self) -> List[AXITransaction]:
        """Generate scenarios to trigger DECERR responses"""
        transactions = []
        
        # Access to completely unmapped address
        unmapped_addr = 0xDEAD0000
        
        tx_unmapped = self.master.write_transaction(
            addr=unmapped_addr,
            data=[0xDEADBEEF]
        )
        transactions.append(tx_unmapped)
        
        return transactions
    
    def _generate_illegal_burst_tests(self) -> List[AXITransaction]:
        """Generate illegal burst patterns (should be caught)"""
        transactions = []
        
        # These should be caught by validation, but included for completeness
        try:
            # WRAP burst with invalid length
            invalid_wrap = AXITransaction(
                addr=0x80000000,
                length=6,  # Invalid for WRAP (should be 2,4,8,16)
                burst=AXIBurstType.WRAP,
                size=AXISize.SIZE_4B,
                data=[0x12345678] * 7
            )
            transactions.append(invalid_wrap)
        except ValueError:
            pass  # Expected to fail validation
        
        return transactions
    
    def _generate_protocol_violation_tests(self) -> List[AXITransaction]:
        """Generate protocol violation scenarios"""
        transactions = []
        
        # 4KB boundary crossing (should be caught)
        try:
            crossing_addr = 0x80000FF0  # Near 4KB boundary
            large_burst = self.master.read_transaction(
                addr=crossing_addr,
                length=32,  # Will cross boundary
                size=AXISize.SIZE_4B
            )
            transactions.append(large_burst)
        except ValueError:
            pass  # Expected to fail validation
        
        return transactions
    
    def _generate_high_throughput_tests(self) -> List[AXITransaction]:
        """Generate high throughput test patterns"""
        transactions = []
        base_addr = self.config.address_range[0] + 0x80000
        
        # Back-to-back maximum length bursts
        for i in range(20):
            addr = base_addr + (i * 0x1000)
            
            # Maximum length INCR burst
            data = self._get_pattern_data('random', i, 256)
            
            tx = self.master.write_transaction(
                addr=addr,
                data=data,
                burst_type=AXIBurstType.INCR,
                size=AXISize.SIZE_4B
            )
            transactions.append(tx)
        
        return transactions
        
    def _generate_randomized_scenarios(self) -> List[AXITransaction]:
        """Generate fully randomized test scenarios"""
        transactions = []
        
        for i in range(self.config.num_transactions):
            # Random parameters with 4KB boundary protection
            burst_type = random.choice([AXIBurstType.INCR, AXIBurstType.FIXED])
            size = random.choice(list(AXISize))
            length = random.randint(1, 16)  # Moderate length for random
            
            # Calculate max transfer size and ensure it doesn't cross 4KB
            transfer_size = 1 << size.value
            total_bytes = length * transfer_size
            
            # Ensure address alignment for the transfer size and 4KB boundary safety
            addr_mask = ~(transfer_size - 1)  # Align to transfer size
            addr = random.randint(*self.config.address_range) & addr_mask
            
            # Check if this would cross 4KB boundary, if so, align to 4KB
            if (addr & 0xFFF) + total_bytes > 4096:
                addr = addr & ~0xFFF  # Align to 4KB boundary
            
            is_write = random.choice([True, False])
            
            if is_write:
                pattern = random.choice(self.config.data_patterns)
                data = self._get_pattern_data(pattern, i, length)
                
                tx = self.master.write_transaction(
                    addr=addr,
                    data=data,
                    burst_type=burst_type,
                    size=size,
                    qos=random.randint(0, 15),
                    prot=random.randint(0, 7),
                    region=random.randint(0, 15)
                )
            else:
                tx = self.master.read_transaction(
                    addr=addr,
                    length=length,
                    burst_type=burst_type,
                    size=size,
                    qos=random.randint(0, 15),
                    prot=random.randint(0, 7),
                    region=random.randint(0, 15)
                )
            
            transactions.append(tx)
        
        return transactions
    
    def _generate_contention_scenarios(self) -> List[AXITransaction]:
        """Generate multi-master contention scenarios"""
        transactions = []
        
        # Multiple masters accessing same address
        contention_addr = self.config.address_range[0] + 0x90000
        
        for master_id in range(4):  # Simulate 4 masters
            tx = self.master.read_transaction(
                addr=contention_addr,
                length=1
            )
            tx.id = master_id  # Different master IDs
            transactions.append(tx)
        
        return transactions
    
    def _generate_corner_cases(self) -> List[AXITransaction]:
        """Generate corner case scenarios"""
        transactions = []
        base_addr = self.config.address_range[0] + 0xA0000
        
        # Minimum and maximum transfer sizes
        sizes = [AXISize.SIZE_1B, AXISize.SIZE_128B]
        
        for size in sizes:
            addr = base_addr + (size.value * 0x1000)
            
            tx = self.master.write_transaction(
                addr=addr,
                data=[0xC0ABECA5E],  # Corner case marker
                size=size
            )
            transactions.append(tx)
        
        # Edge addresses (start and end of range)
        # Ensure edge addresses don't cross 4KB boundaries
        start_addr = self.config.address_range[0]
        end_addr = self.config.address_range[1] - 4
        
        # Align end address to avoid 4KB boundary crossing
        end_addr = end_addr & ~0xFFF  # Align to 4KB boundary
        
        edge_addresses = [start_addr, end_addr]
        
        for addr in edge_addresses:
            tx = self.master.read_transaction(
                addr=addr,
                length=1
            )
            transactions.append(tx)
        
        return transactions
    
    def _get_pattern_data(self, pattern: str, seed: int, length: int) -> List[int]:
        """Get data based on specified pattern"""
        if pattern in self.pattern_generators:
            return self.pattern_generators[pattern](seed, length)
        else:
            return self._generate_random_data(seed, length)
    
    def _generate_random_data(self, seed: int, length: int) -> List[int]:
        """Generate random data pattern"""
        random.seed(seed)
        return [random.randint(0, 0xFFFFFFFF) for _ in range(length)]
    
    def _generate_walking_ones(self, seed: int, length: int) -> List[int]:
        """Generate walking ones pattern"""
        data = []
        for i in range(length):
            bit_pos = (seed + i) % 32
            data.append(1 << bit_pos)
        return data
    
    def _generate_walking_zeros(self, seed: int, length: int) -> List[int]:
        """Generate walking zeros pattern"""
        data = []
        for i in range(length):
            bit_pos = (seed + i) % 32
            data.append(0xFFFFFFFF ^ (1 << bit_pos))
        return data
    
    def _generate_alternating_pattern(self, seed: int, length: int) -> List[int]:
        """Generate alternating pattern"""
        patterns = [0xAAAAAAAA, 0x55555555]
        return [patterns[(seed + i) % 2] for i in range(length)]
    
    def _generate_address_pattern(self, seed: int, length: int) -> List[int]:
        """Generate address-based pattern"""
        base = seed * 0x1000
        return [base + (i * 4) for i in range(length)]
    
    def _generate_incremental_pattern(self, seed: int, length: int) -> List[int]:
        """Generate incremental pattern"""
        return [seed + i for i in range(length)]

def create_comprehensive_test_suite(master: AXIMasterAgent) -> Dict[str, List[AXITransaction]]:
    """Create comprehensive test suite covering all CLAUDE.md requirements"""
    
    test_suite = {}
    
    # Basic sequences
    basic_config = TestScenarioConfig(
        name="Basic Transactions",
        description="Single read/write, all burst types, WSTRB variations",
        num_transactions=50
    )
    basic_gen = AXITestSequenceGenerator(master, basic_config)
    test_suite['basic'] = basic_gen.generate_basic_sequences()
    
    # Advanced sequences
    advanced_config = TestScenarioConfig(
        name="Advanced Features",
        description="Out-of-order, same-ID ordering, exclusive access, attribute variations",
        num_transactions=100
    )
    advanced_gen = AXITestSequenceGenerator(master, advanced_config)
    test_suite['advanced'] = advanced_gen.generate_advanced_sequences()
    
    # Error injection
    error_config = TestScenarioConfig(
        name="Error Injection",
        description="SLVERR, DECERR, illegal bursts, protocol violations",
        num_transactions=50,
        error_injection=True
    )
    error_gen = AXITestSequenceGenerator(master, error_config)
    test_suite['error_injection'] = error_gen.generate_error_injection_sequences()
    
    # Stress tests
    stress_config = TestScenarioConfig(
        name="Stress Tests",
        description="High throughput, randomized, contention, corner cases",
        num_transactions=200,
        stress_level=5
    )
    stress_gen = AXITestSequenceGenerator(master, stress_config)
    test_suite['stress'] = stress_gen.generate_stress_test_sequences()
    
    return test_suite