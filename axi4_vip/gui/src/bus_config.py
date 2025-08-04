#!/usr/bin/env python3
"""
Bus configuration classes for AMBA bus matrix
"""

from dataclasses import dataclass
from typing import List, Optional

@dataclass
class Master:
    """Bus master configuration"""
    name: str
    x: float = 0
    y: float = 0
    # AXI parameters
    id_width: int = 4
    user_width: int = 0
    priority: int = 0
    qos_support: bool = True
    exclusive_support: bool = True
    default_prot: int = 0b010
    default_cache: int = 0b0011
    default_region: int = 0

@dataclass
class Slave:
    """Bus slave configuration"""
    name: str
    base_address: int
    size: int  # in KB
    x: float = 0
    y: float = 0
    # Additional parameters
    memory_type: str = "Memory"
    read_latency: int = 1
    write_latency: int = 1
    num_regions: int = 1
    secure_only: bool = False
    privileged_only: bool = False
    allowed_masters: List[int] = None
    
    def __post_init__(self):
        if self.allowed_masters is None:
            self.allowed_masters = []
    
    def get_end_address(self):
        """Calculate end address from base and size"""
        return self.base_address + (self.size * 1024) - 1

class BusConfig:
    """Main bus configuration container"""
    def __init__(self):
        self.masters: List[Master] = []
        self.slaves: List[Slave] = []
        self.bus_type: str = "AXI4"
        self.data_width: int = 64
        self.addr_width: int = 32
        self.arbitration: str = "QOS"
        # AXI4 feature enables
        self.has_qos: bool = True
        self.has_cache: bool = True
        self.has_prot: bool = True
        self.has_region: bool = False
        self.has_user: bool = False
        
    def add_master(self, master: Master):
        """Add a master to the configuration"""
        self.masters.append(master)
        
    def add_slave(self, slave: Slave):
        """Add a slave to the configuration"""
        self.slaves.append(slave)
        
    def remove_master(self, index: int):
        """Remove a master by index"""
        if 0 <= index < len(self.masters):
            del self.masters[index]
            
    def remove_slave(self, index: int):
        """Remove a slave by index"""
        if 0 <= index < len(self.slaves):
            del self.slaves[index]
            
    def clear(self):
        """Clear all configuration"""
        self.masters.clear()
        self.slaves.clear()
        
    def validate(self):
        """Validate the configuration"""
        errors = []
        
        # Check for at least one master and slave
        if not self.masters:
            errors.append("At least one master is required")
        if not self.slaves:
            errors.append("At least one slave is required")
            
        # Check for address overlaps
        for i, slave1 in enumerate(self.slaves):
            for j, slave2 in enumerate(self.slaves[i+1:], i+1):
                if (slave1.base_address <= slave2.base_address <= slave1.get_end_address() or
                    slave2.base_address <= slave1.base_address <= slave2.get_end_address()):
                    errors.append(f"Address overlap between {slave1.name} and {slave2.name}")
                    
        return errors