#!/usr/bin/env python3
"""
Bus Configuration Data Models
Based on gui_build.md v3 specification
"""

from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple
import json
import yaml

@dataclass
class QoSConfig:
    """Per-channel QoS configuration"""
    aw: int = 0  # AWQoS (0-15)
    ar: int = 0  # ARQoS (0-15)
    
    def validate(self):
        """Validate QoS values are in range"""
        if not (0 <= self.aw <= 15):
            raise ValueError(f"AWQoS must be 0-15, got {self.aw}")
        if not (0 <= self.ar <= 15):
            raise ValueError(f"ARQoS must be 0-15, got {self.ar}")

@dataclass
class MasterNode:
    """Master node configuration"""
    name: str
    m_index: int
    qos_default: Optional[QoSConfig] = None
    cache_default: str = "0b1111"
    prot_default: str = "NS PRIV DATA"
    region_default: int = 0
    outstanding: Dict[str, int] = field(default_factory=lambda: {"read": 8, "write": 8})
    
    # Visual position for GUI
    x: float = 0
    y: float = 0
    
    def __post_init__(self):
        if self.qos_default is None:
            self.qos_default = QoSConfig()
        elif isinstance(self.qos_default, dict):
            self.qos_default = QoSConfig(**self.qos_default)

@dataclass
class SlaveNode:
    """Slave node configuration"""
    name: str
    s_index: int
    base: int  # Base address
    size: int  # Size in bytes
    attributes: Dict[str, bool] = field(default_factory=lambda: {"cacheable": True, "bufferable": True})
    qos_accept: bool = True
    priority: Dict = field(default_factory=dict)  # {"type": "fixed", "order": ["M0", "M1", ...]}
    region_mask: int = 0xF
    
    # Visual position for GUI
    x: float = 0
    y: float = 0
    
    def get_end_address(self) -> int:
        """Calculate end address"""
        return self.base + self.size - 1

@dataclass
class EdgeConfig:
    """Edge configuration between nodes"""
    from_node: str
    to_node: str
    qos: Optional[QoSConfig] = None
    cache: Optional[str] = None
    prot: Optional[str] = None
    region: Optional[int] = None
    
    def __post_init__(self):
        if self.qos and isinstance(self.qos, dict):
            self.qos = QoSConfig(**self.qos)

@dataclass
class BusConfig:
    """Main bus configuration"""
    addr_width: int = 32  # 8-64 bits
    data_width: int = 64  # 8,16,32,64,128,256,512,1024 bits
    id_width: int = 4
    user_width: int = 0
    qos: bool = True
    cache: bool = True
    prot: bool = True
    region: bool = True
    qos_default: QoSConfig = field(default_factory=QoSConfig)
    
    # Arbitration type: "fixed", "rr" (round-robin), "qos"
    arbitration: str = "qos"
    
    def __post_init__(self):
        if isinstance(self.qos_default, dict):
            self.qos_default = QoSConfig(**self.qos_default)
        self.validate()
    
    def validate(self):
        """Validate bus configuration"""
        # Check data width
        valid_data_widths = [8, 16, 32, 64, 128, 256, 512, 1024]
        if self.data_width not in valid_data_widths:
            raise ValueError(f"data_width must be one of {valid_data_widths}, got {self.data_width}")
        
        # Check address width
        if not (8 <= self.addr_width <= 64):
            raise ValueError(f"addr_width must be 8-64, got {self.addr_width}")
        
        # Check arbitration type
        if self.arbitration not in ["fixed", "rr", "qos"]:
            raise ValueError(f"arbitration must be 'fixed', 'rr', or 'qos', got {self.arbitration}")

@dataclass
class ViewPreferences:
    """GUI view preferences"""
    show_qos: bool = True
    show_priority: bool = True
    show_cache: bool = False
    show_prot: bool = False
    show_region: bool = False
    
    # Layout preferences
    auto_layout: bool = True
    grid_snap: bool = True
    grid_size: int = 20

@dataclass
class Project:
    """Complete project configuration"""
    name: str = "untitled"
    bus: BusConfig = field(default_factory=BusConfig)
    masters: List[MasterNode] = field(default_factory=list)
    slaves: List[SlaveNode] = field(default_factory=list)
    edges: List[EdgeConfig] = field(default_factory=list)
    preferences: ViewPreferences = field(default_factory=ViewPreferences)
    
    def add_master(self, name: str) -> MasterNode:
        """Add a new master"""
        m_index = len(self.masters)
        master = MasterNode(name=name, m_index=m_index)
        self.masters.append(master)
        return master
    
    def add_slave(self, name: str, base: int = None, size: int = 0x10000) -> SlaveNode:
        """Add a new slave with auto address allocation"""
        s_index = len(self.slaves)
        
        # Auto-allocate base address if not provided
        if base is None:
            if self.slaves:
                # Find the next available address
                last_slave = max(self.slaves, key=lambda s: s.base + s.size)
                base = last_slave.base + last_slave.size
                # Align to 64KB boundary
                base = ((base + 0xFFFF) // 0x10000) * 0x10000
            else:
                base = 0x00000000
        
        slave = SlaveNode(name=name, s_index=s_index, base=base, size=size)
        self.slaves.append(slave)
        return slave
    
    def delete_master(self, m_index: int):
        """Delete a master and reindex"""
        if 0 <= m_index < len(self.masters):
            del self.masters[m_index]
            # Reindex remaining masters
            for i, master in enumerate(self.masters):
                master.m_index = i
            # Remove affected edges
            self.edges = [e for e in self.edges if f"M{m_index}" not in [e.from_node, e.to_node]]
    
    def delete_slave(self, s_index: int):
        """Delete a slave and reindex"""
        if 0 <= s_index < len(self.slaves):
            del self.slaves[s_index]
            # Reindex remaining slaves
            for i, slave in enumerate(self.slaves):
                slave.s_index = i
            # Remove affected edges
            self.edges = [e for e in self.edges if f"S{s_index}" not in [e.from_node, e.to_node]]
    
    def resolve_qos(self, from_node: str, to_node: str, channel: str = "aw") -> int:
        """Resolve QoS value with priority: Edge > Node > Bus"""
        # Check edge override
        for edge in self.edges:
            if edge.from_node == from_node and edge.to_node == to_node:
                if edge.qos:
                    return getattr(edge.qos, channel)
        
        # Check node default
        if from_node.startswith("M"):
            idx = int(from_node[1:])
            if 0 <= idx < len(self.masters):
                master = self.masters[idx]
                if master.qos_default:
                    return getattr(master.qos_default, channel)
        
        # Use bus default
        return getattr(self.bus.qos_default, channel)
    
    def save_json(self, filename: str):
        """Save project to JSON file"""
        with open(filename, 'w') as f:
            json.dump(self.to_dict(), f, indent=2)
    
    @classmethod
    def load_json(cls, filename: str) -> 'Project':
        """Load project from JSON file"""
        with open(filename) as f:
            data = json.load(f)
        return cls.from_dict(data)
    
    def to_dict(self) -> dict:
        """Convert project to dictionary"""
        data = {
            "project": self.name,
            "bus": {
                "addr_width": self.bus.addr_width,
                "data_width": self.bus.data_width,
                "id_width": self.bus.id_width,
                "user_width": self.bus.user_width,
                "qos": self.bus.qos,
                "cache": self.bus.cache,
                "prot": self.bus.prot,
                "region": self.bus.region,
                "qos_default": {"aw": self.bus.qos_default.aw, "ar": self.bus.qos_default.ar},
                "arbitration": self.bus.arbitration
            },
            "masters": [],
            "slaves": [],
            "edges": []
        }
        
        # Add masters
        for master in self.masters:
            m_data = {
                "name": master.name,
                "m_index": master.m_index,
                "qos_default": {"aw": master.qos_default.aw, "ar": master.qos_default.ar},
                "cache_default": master.cache_default,
                "prot_default": master.prot_default,
                "region_default": master.region_default,
                "outstanding": master.outstanding,
                "x": master.x,
                "y": master.y
            }
            data["masters"].append(m_data)
        
        # Add slaves
        for slave in self.slaves:
            s_data = {
                "name": slave.name,
                "s_index": slave.s_index,
                "base": slave.base,
                "size": slave.size,
                "attributes": slave.attributes,
                "qos_accept": slave.qos_accept,
                "priority": slave.priority,
                "region_mask": slave.region_mask,
                "x": slave.x,
                "y": slave.y
            }
            data["slaves"].append(s_data)
        
        # Add edges
        for edge in self.edges:
            e_data = {
                "from": edge.from_node,
                "to": edge.to_node
            }
            if edge.qos:
                e_data["qos"] = {"aw": edge.qos.aw, "ar": edge.qos.ar}
            data["edges"].append(e_data)
        
        return data
    
    @classmethod
    def from_dict(cls, data: dict) -> 'Project':
        """Create project from dictionary"""
        # Create project
        project = cls(name=data.get("project", "untitled"))
        
        # Load bus config
        bus_data = data.get("bus", {})
        project.bus = BusConfig(
            addr_width=bus_data.get("addr_width", 32),
            data_width=bus_data.get("data_width", 64),
            id_width=bus_data.get("id_width", 4),
            user_width=bus_data.get("user_width", 0),
            qos=bus_data.get("qos", True),
            cache=bus_data.get("cache", True),
            prot=bus_data.get("prot", True),
            region=bus_data.get("region", True),
            qos_default=QoSConfig(**bus_data.get("qos_default", {})),
            arbitration=bus_data.get("arbitration", "qos")
        )
        
        # Load masters
        for m_data in data.get("masters", []):
            master = MasterNode(
                name=m_data["name"],
                m_index=m_data["m_index"],
                qos_default=QoSConfig(**m_data.get("qos_default", {})),
                cache_default=m_data.get("cache_default", "0b1111"),
                prot_default=m_data.get("prot_default", "NS PRIV DATA"),
                region_default=m_data.get("region_default", 0),
                outstanding=m_data.get("outstanding", {"read": 8, "write": 8}),
                x=m_data.get("x", 0),
                y=m_data.get("y", 0)
            )
            project.masters.append(master)
        
        # Load slaves
        for s_data in data.get("slaves", []):
            slave = SlaveNode(
                name=s_data["name"],
                s_index=s_data["s_index"],
                base=s_data["base"],
                size=s_data["size"],
                attributes=s_data.get("attributes", {"cacheable": True, "bufferable": True}),
                qos_accept=s_data.get("qos_accept", True),
                priority=s_data.get("priority", {}),
                region_mask=s_data.get("region_mask", 0xF),
                x=s_data.get("x", 0),
                y=s_data.get("y", 0)
            )
            project.slaves.append(slave)
        
        # Load edges
        for e_data in data.get("edges", []):
            edge = EdgeConfig(
                from_node=e_data["from"],
                to_node=e_data["to"],
                qos=QoSConfig(**e_data["qos"]) if "qos" in e_data else None
            )
            project.edges.append(edge)
        
        return project
    
    def to_yaml(self) -> str:
        """Export to YAML format"""
        data = {
            "project": self.name,
            "bus": {
                "addr_width": self.bus.addr_width,
                "data_width": self.bus.data_width,
                "id_width": self.bus.id_width,
                "user_width": self.bus.user_width,
                "qos": self.bus.qos,
                "cache": self.bus.cache,
                "prot": self.bus.prot,
                "region": self.bus.region,
                "qos_default": {"aw": self.bus.qos_default.aw, "ar": self.bus.qos_default.ar},
                "arbitration": self.bus.arbitration
            },
            "masters": [],
            "slaves": [],
            "edges": []
        }
        
        # Add masters
        for master in self.masters:
            m_data = {
                "name": master.name,
                "m_index": master.m_index,
                "qos_default": {"aw": master.qos_default.aw, "ar": master.qos_default.ar},
                "cache_default": master.cache_default,
                "prot_default": master.prot_default,
                "region_default": master.region_default,
                "outstanding": master.outstanding
            }
            data["masters"].append(m_data)
        
        # Add slaves
        for slave in self.slaves:
            s_data = {
                "name": slave.name,
                "s_index": slave.s_index,
                "base": f"0x{slave.base:08X}",
                "size": f"0x{slave.size:08X}",
                "attributes": slave.attributes,
                "qos_accept": slave.qos_accept,
                "priority": slave.priority,
                "region_mask": slave.region_mask
            }
            data["slaves"].append(s_data)
        
        # Add edges
        for edge in self.edges:
            e_data = {
                "from": edge.from_node,
                "to": edge.to_node
            }
            if edge.qos:
                e_data["qos"] = {"aw": edge.qos.aw, "ar": edge.qos.ar}
            data["edges"].append(e_data)
        
        return yaml.dump(data, default_flow_style=False, sort_keys=False)
    
    @classmethod
    def from_yaml(cls, yaml_str: str) -> 'Project':
        """Load from YAML format"""
        data = yaml.safe_load(yaml_str)
        
        # Create project
        project = cls(name=data.get("project", "untitled"))
        
        # Load bus config
        bus_data = data.get("bus", {})
        project.bus = BusConfig(
            addr_width=bus_data.get("addr_width", 32),
            data_width=bus_data.get("data_width", 64),
            id_width=bus_data.get("id_width", 4),
            user_width=bus_data.get("user_width", 0),
            qos=bus_data.get("qos", True),
            cache=bus_data.get("cache", True),
            prot=bus_data.get("prot", True),
            region=bus_data.get("region", True),
            qos_default=QoSConfig(**bus_data.get("qos_default", {})),
            arbitration=bus_data.get("arbitration", "qos")
        )
        
        # Load masters
        for m_data in data.get("masters", []):
            master = MasterNode(
                name=m_data["name"],
                m_index=m_data["m_index"],
                qos_default=QoSConfig(**m_data.get("qos_default", {})),
                cache_default=m_data.get("cache_default", "0b1111"),
                prot_default=m_data.get("prot_default", "NS PRIV DATA"),
                region_default=m_data.get("region_default", 0),
                outstanding=m_data.get("outstanding", {"read": 8, "write": 8})
            )
            project.masters.append(master)
        
        # Load slaves
        for s_data in data.get("slaves", []):
            base = s_data["base"]
            if isinstance(base, str):
                base = int(base, 0)  # Handle hex strings
            size = s_data["size"]
            if isinstance(size, str):
                size = int(size, 0)
            
            slave = SlaveNode(
                name=s_data["name"],
                s_index=s_data["s_index"],
                base=base,
                size=size,
                attributes=s_data.get("attributes", {"cacheable": True, "bufferable": True}),
                qos_accept=s_data.get("qos_accept", True),
                priority=s_data.get("priority", {}),
                region_mask=s_data.get("region_mask", 0xF)
            )
            project.slaves.append(slave)
        
        # Load edges
        for e_data in data.get("edges", []):
            edge = EdgeConfig(
                from_node=e_data["from"],
                to_node=e_data["to"],
                qos=QoSConfig(**e_data["qos"]) if "qos" in e_data else None
            )
            project.edges.append(edge)
        
        return project