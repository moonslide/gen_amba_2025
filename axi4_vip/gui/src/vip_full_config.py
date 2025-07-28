#!/usr/bin/env python3
"""
Full VIP Configuration Module
Implements comprehensive configuration for all tim_axi4_vip features
"""

from dataclasses import dataclass, field
from typing import List, Dict, Optional
from enum import Enum

# Enums for VIP configurations
class QoSMode(Enum):
    DISABLE = "DISABLE"
    READ_ONLY = "READ_ONLY"
    WRITE_READ = "WRITE_READ"
    WRITE_ONLY = "WRITE_ONLY"

class ResponseMode(Enum):
    IN_ORDER = "IN_ORDER"
    READ_OUT_OF_ORDER = "READ_OUT_OF_ORDER"
    WRITE_READ_OUT_OF_ORDER = "WRITE_READ_OUT_OF_ORDER"
    WRITE_OUT_OF_ORDER = "WRITE_OUT_OF_ORDER"

class ReadDataMode(Enum):
    RANDOM = "RANDOM"
    SLAVE_MEM = "SLAVE_MEM"
    USER_DATA = "USER_DATA"
    SLAVE_ERR_RESP = "SLAVE_ERR_RESP"

class BusMatrixMode(Enum):
    NONE = "NONE"
    BASE_BUS_MATRIX = "BASE_BUS_MATRIX"
    BUS_ENHANCED_MATRIX = "BUS_ENHANCED_MATRIX"

class SlaveType(Enum):
    DDR_MEMORY = "DDR_MEMORY"
    BOOT_ROM = "BOOT_ROM"
    GPU_DEVICE = "GPU_DEVICE"
    SECURITY_POLICY_MANAGER = "SECURITY_POLICY_MANAGER"
    SPI_CONTROLLER = "SPI_CONTROLLER"
    USB_CONTROLLER = "USB_CONTROLLER"
    SRAM = "SRAM"
    FIREWALL_CONFIG = "FIREWALL_CONFIG"
    CLOCK_RESET_CONTROL = "CLOCK_RESET_CONTROL"
    INTERRUPT_CONTROLLER = "INTERRUPT_CONTROLLER"
    DMA = "DMA"
    GENERIC = "GENERIC"

@dataclass
class MasterAgentConfig:
    """Comprehensive Master Agent Configuration"""
    name: str
    id: int
    
    # Basic configuration
    active_passive: str = "ACTIVE"
    coverage_enable: bool = True
    addr_width: int = 64
    data_width: int = 64
    id_width: int = 4
    user_width: int = 0
    
    # QoS and priority
    qos_mode: QoSMode = QoSMode.DISABLE
    qos_support: bool = True
    priority: int = 0
    default_qos: int = 0
    
    # Protection and security
    default_prot: int = 0b010  # privileged, non-secure, data
    default_cache: int = 0b0011  # normal, non-cacheable
    default_region: int = 0
    exclusive_support: bool = True
    
    # Performance configuration
    outstanding_read_limit: int = 16
    outstanding_write_limit: int = 16
    aw_wait_cycles: int = 0
    w_wait_cycles: int = 0
    r_wait_cycles: int = 0
    
    # Data modes
    read_data_mode: ReadDataMode = ReadDataMode.RANDOM
    memory_model_enable: bool = True
    memory_size: int = 4096  # KB
    
    # Error injection
    error_injection_enable: bool = False
    error_injection_rate: float = 0.01  # 1% error rate
    
    # Address mapping
    slave_address_ranges: Dict[int, tuple] = field(default_factory=dict)

@dataclass
class SlaveAgentConfig:
    """Comprehensive Slave Agent Configuration"""
    name: str
    id: int
    base_address: int
    size: int  # in KB
    
    # Basic configuration
    active_passive: str = "ACTIVE"
    coverage_enable: bool = True
    slave_type: SlaveType = SlaveType.GENERIC
    
    # Response configuration
    response_mode: ResponseMode = ResponseMode.IN_ORDER
    read_latency: int = 1
    write_latency: int = 1
    b_wait_cycles: int = 0
    r_wait_cycles: int = 0
    
    # Security configuration
    secure_only: bool = False
    privileged_only: bool = False
    allowed_masters: List[int] = field(default_factory=list)
    num_regions: int = 1
    region_config: List[Dict] = field(default_factory=list)
    
    # Memory configuration
    memory_type: str = "Memory"
    memory_model_enable: bool = True
    memory_gap_enable: bool = False
    memory_gaps: List[tuple] = field(default_factory=list)
    
    # QoS configuration
    qos_mode: QoSMode = QoSMode.DISABLE
    min_qos_level: int = 0
    max_qos_level: int = 15
    
    # Error response configuration
    error_response_enable: bool = False
    error_addresses: List[int] = field(default_factory=list)

@dataclass
class TestSequenceConfig:
    """Test Sequence Configuration"""
    name: str
    enabled: bool = True
    
    # Basic sequences
    single_read_write: bool = True
    burst_types: List[str] = field(default_factory=lambda: ["FIXED", "INCR", "WRAP"])
    transfer_sizes: List[int] = field(default_factory=lambda: [1, 2, 4, 8, 16, 32, 64, 128])
    
    # Advanced sequences
    out_of_order_enable: bool = True
    same_id_ordering_test: bool = True
    exclusive_access_test: bool = True
    qos_variation_test: bool = True
    
    # Error injection
    slverr_scenarios: bool = True
    decerr_scenarios: bool = True
    illegal_burst_test: bool = True
    protocol_violation_test: bool = True
    
    # Stress testing
    stress_level: int = 1  # 1-5
    num_transactions: int = 100
    concurrent_masters: bool = True
    
    # Coverage goals
    coverage_goal: int = 95
    functional_coverage: bool = True
    code_coverage: bool = True

@dataclass
class AssertionConfig:
    """Assertion and Coverage Configuration"""
    # Protocol assertions
    channel_handshake_check: bool = True
    signal_stability_check: bool = True
    id_matching_check: bool = True
    burst_boundary_check: bool = True
    response_timing_check: bool = True
    exclusive_access_check: bool = True
    
    # Coverage collection
    transaction_coverage: bool = True
    burst_coverage: bool = True
    response_coverage: bool = True
    address_coverage: bool = True
    error_coverage: bool = True
    performance_coverage: bool = True
    
    # Scoreboard configuration
    scoreboard_enable: bool = True
    compare_mode: str = "TRANSACTION"  # TRANSACTION, CYCLE_ACCURATE
    
    # Monitor configuration
    monitor_enable: bool = True
    monitor_level: str = "FULL"  # MINIMAL, NORMAL, FULL

@dataclass
class BusMatrixConfig:
    """Bus Matrix Configuration"""
    mode: BusMatrixMode = BusMatrixMode.BASE_BUS_MATRIX
    matrix_size: tuple = (4, 4)  # (masters, slaves)
    
    # Interconnect configuration
    smart_interconnect: bool = True
    or_based_routing: bool = True
    bfm_address_filtering: bool = True
    race_condition_prevention: bool = True
    
    # Arbitration
    arbitration_scheme: str = "QOS"  # FIXED, RR, QOS, WRR
    qos_enable: bool = True
    weighted_round_robin: bool = False
    weights: Dict[int, int] = field(default_factory=dict)
    
    # ID mapping
    id_mapping_enable: bool = True
    dynamic_id_mapping: bool = True
    id_width_per_master: Dict[int, int] = field(default_factory=dict)

@dataclass
class VIPFullConfig:
    """Complete VIP Configuration"""
    # Basic configuration
    project_name: str
    bus_type: str  # AXI4, AXI3
    data_width: int = 64
    addr_width: int = 64
    
    # Components
    masters: List[MasterAgentConfig] = field(default_factory=list)
    slaves: List[SlaveAgentConfig] = field(default_factory=list)
    
    # Bus matrix
    bus_matrix: BusMatrixConfig = field(default_factory=BusMatrixConfig)
    
    # Test configuration
    test_sequences: TestSequenceConfig = field(default_factory=TestSequenceConfig)
    
    # Assertions and coverage
    assertions: AssertionConfig = field(default_factory=AssertionConfig)
    
    # Protocol features
    protocol_version: str = "AXI4"
    exclusive_access_enable: bool = True
    qos_enable: bool = True
    region_enable: bool = True
    user_signal_enable: bool = True
    user_signal_width: int = 1
    
    # 4KB boundary handling
    boundary_crossing_check: bool = True
    unaligned_transfer_support: bool = True
    
    # Debug features
    debug_enable: bool = True
    waveform_dump: bool = True
    transaction_recording: bool = True
    performance_monitoring: bool = True
    
    def validate(self) -> List[str]:
        """Validate configuration and return list of errors"""
        errors = []
        
        # Check matrix size limits
        if self.bus_matrix.matrix_size[0] > 64 or self.bus_matrix.matrix_size[1] > 64:
            errors.append("Matrix size cannot exceed 64x64")
        
        # Check master/slave count matches matrix
        if len(self.masters) != self.bus_matrix.matrix_size[0]:
            errors.append(f"Master count ({len(self.masters)}) doesn't match matrix size ({self.bus_matrix.matrix_size[0]})")
        
        if len(self.slaves) != self.bus_matrix.matrix_size[1]:
            errors.append(f"Slave count ({len(self.slaves)}) doesn't match matrix size ({self.bus_matrix.matrix_size[1]})")
        
        # Check address overlaps
        for i, slave1 in enumerate(self.slaves):
            for j, slave2 in enumerate(self.slaves[i+1:], i+1):
                end1 = slave1.base_address + (slave1.size * 1024) - 1
                end2 = slave2.base_address + (slave2.size * 1024) - 1
                
                if (slave1.base_address <= slave2.base_address <= end1 or
                    slave2.base_address <= slave1.base_address <= end2):
                    errors.append(f"Address overlap between {slave1.name} and {slave2.name}")
        
        # Check 4KB boundaries for slaves
        for slave in self.slaves:
            if slave.base_address % 4096 != 0:
                errors.append(f"{slave.name} base address not aligned to 4KB boundary")
        
        return errors