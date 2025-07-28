#!/usr/bin/env python3
"""
Example: Create a mixed protocol system with AXI4 to APB bridge
Demonstrates hierarchical bus design with protocol conversion
"""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '..', 'src'))

from bus_config import BusConfig, Master, Slave
import json

def create_mixed_protocol_system():
    """Create a system with AXI4 main bus and APB peripheral bus"""
    
    # Main AXI4 bus configuration
    axi_config = BusConfig()
    axi_config.bus_type = "AXI4"
    axi_config.data_width = 128  # High-performance main bus
    axi_config.addr_width = 40   # 1TB address space
    axi_config.arbitration = "QOS"  # QoS-based arbitration
    
    # High-performance masters
    print("Creating AXI4 main bus...")
    
    # Application Processor Cluster
    app_cpu = Master("APP_CPU_Cluster")
    app_cpu.id_width = 8  # Many outstanding transactions
    app_cpu.priority = 15  # Highest priority
    app_cpu.qos_support = True
    app_cpu.exclusive_support = True
    app_cpu.user_width = 4  # Custom sideband signals
    axi_config.masters.append(app_cpu)
    
    # Real-time Processor
    rt_cpu = Master("RT_CPU")
    rt_cpu.id_width = 4
    rt_cpu.priority = 14  # High priority for real-time
    rt_cpu.qos_support = True
    rt_cpu.exclusive_support = True
    rt_cpu.default_cache = 0b0000  # Non-cacheable for determinism
    axi_config.masters.append(rt_cpu)
    
    # Graphics Processor
    gpu = Master("GPU")
    gpu.id_width = 16  # Very high parallelism
    gpu.priority = 10
    gpu.qos_support = True
    gpu.exclusive_support = False
    gpu.user_width = 8  # GPU-specific metadata
    axi_config.masters.append(gpu)
    
    # High-speed slaves
    print("Adding AXI4 slaves...")
    
    # DDR4 Memory Controller
    ddr4 = Slave("DDR4_Controller", 0x0000000000, 8388608)  # 8GB
    ddr4.memory_type = "Memory"
    ddr4.read_latency = 20
    ddr4.write_latency = 10
    ddr4.num_regions = 8  # Multiple security regions
    axi_config.slaves.append(ddr4)
    
    # On-chip SRAM
    sram = Slave("SRAM", 0x200000000, 32768)  # 32MB TCM
    sram.memory_type = "Memory"
    sram.read_latency = 2
    sram.write_latency = 1
    axi_config.slaves.append(sram)
    
    # APB Bridge (connects to peripheral bus)
    apb_bridge = Slave("APB_Bridge", 0x400000000, 262144)  # 256MB space
    apb_bridge.memory_type = "Peripheral"
    apb_bridge.read_latency = 3  # Bridge latency
    apb_bridge.write_latency = 3
    axi_config.slaves.append(apb_bridge)
    
    # APB bus configuration (behind the bridge)
    apb_config = {
        "bus_type": "APB",
        "data_width": 32,  # Lower performance peripheral bus
        "addr_width": 32,
        "bridge_from": "AXI4",
        "peripherals": []
    }
    
    # APB Peripherals
    print("\nCreating APB peripheral bus...")
    
    peripherals = [
        {"name": "UART0", "offset": 0x0000, "size": 4},
        {"name": "UART1", "offset": 0x1000, "size": 4},
        {"name": "SPI0", "offset": 0x2000, "size": 4},
        {"name": "SPI1", "offset": 0x3000, "size": 4},
        {"name": "I2C0", "offset": 0x4000, "size": 4},
        {"name": "I2C1", "offset": 0x5000, "size": 4},
        {"name": "GPIO0", "offset": 0x6000, "size": 4},
        {"name": "GPIO1", "offset": 0x7000, "size": 4},
        {"name": "Timer0", "offset": 0x8000, "size": 4},
        {"name": "Timer1", "offset": 0x9000, "size": 4},
        {"name": "WDT", "offset": 0xA000, "size": 4},
        {"name": "RTC", "offset": 0xB000, "size": 4},
        {"name": "PWM0", "offset": 0xC000, "size": 4},
        {"name": "ADC", "offset": 0xD000, "size": 4},
        {"name": "System_Ctrl", "offset": 0xE000, "size": 4},
    ]
    
    for periph in peripherals:
        apb_config["peripherals"].append({
            "name": periph["name"],
            "base_address": hex(0x400000000 + periph["offset"]),
            "size": periph["size"],
            "prot_support": periph["name"] == "System_Ctrl",  # Only system control is protected
            "strb_support": True  # APB4 features
        })
    
    # Create complete system configuration
    system_config = {
        "name": "Mixed Protocol SoC",
        "description": "High-performance AXI4 main bus with APB peripheral bus",
        "main_bus": {
            "bus_type": axi_config.bus_type,
            "data_width": axi_config.data_width,
            "addr_width": axi_config.addr_width,
            "arbitration": axi_config.arbitration,
            "masters": [],
            "slaves": []
        },
        "peripheral_bus": apb_config
    }
    
    # Convert masters
    for master in axi_config.masters:
        system_config["main_bus"]["masters"].append({
            "name": master.name,
            "id_width": master.id_width,
            "priority": master.priority,
            "qos_support": master.qos_support,
            "exclusive_support": master.exclusive_support,
            "user_width": master.user_width,
            "default_cache": master.default_cache
        })
    
    # Convert slaves
    for slave in axi_config.slaves:
        system_config["main_bus"]["slaves"].append({
            "name": slave.name,
            "base_address": hex(slave.base_address),
            "size": slave.size,
            "memory_type": slave.memory_type,
            "read_latency": slave.read_latency,
            "write_latency": slave.write_latency,
            "num_regions": slave.num_regions
        })
    
    # Save configuration
    config_file = "mixed_protocol_system.json"
    with open(config_file, 'w') as f:
        json.dump(system_config, f, indent=2)
    
    # Print system summary
    print("\n" + "="*70)
    print("MIXED PROTOCOL SYSTEM SUMMARY")
    print("="*70)
    print("\nMAIN BUS (AXI4):")
    print(f"  Data Width: {axi_config.data_width} bits")
    print(f"  Address Width: {axi_config.addr_width} bits")
    print(f"  Arbitration: {axi_config.arbitration}")
    print(f"\n  Masters ({len(axi_config.masters)}):")
    for master in axi_config.masters:
        print(f"    - {master.name}: Priority={master.priority}, ID_WIDTH={master.id_width}")
    print(f"\n  Slaves ({len(axi_config.slaves)}):")
    for slave in axi_config.slaves:
        print(f"    - {slave.name}: 0x{slave.base_address:010X} ({slave.size}KB)")
    
    print(f"\nPERIPHERAL BUS (APB via bridge at 0x{0x400000000:010X}):")
    print(f"  Data Width: {apb_config['data_width']} bits")
    print(f"  Peripherals ({len(apb_config['peripherals'])}):")
    for periph in apb_config['peripherals']:
        print(f"    - {periph['name']}: {periph['base_address']} ({periph['size']}KB)")
    
    print(f"\nConfiguration saved to: {config_file}")
    print("\nThis configuration demonstrates:")
    print("  - High-performance AXI4 main bus (128-bit)")
    print("  - Lower-performance APB peripheral bus (32-bit)")
    print("  - Protocol bridge for efficient peripheral access")
    print("  - Mixed master types (CPU, GPU, RT processor)")
    print("  - Hierarchical memory map")
    
    return system_config

if __name__ == "__main__":
    create_mixed_protocol_system()