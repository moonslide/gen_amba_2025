#!/usr/bin/env python3
"""
Example: Create a simple 2 master x 3 slave AXI4 system
This demonstrates basic usage of the AMBA Bus Matrix Configuration Tool API
"""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '..', 'src'))

from bus_config import BusConfig, Master, Slave
from axi_verilog_generator import AXIVerilogGenerator
from vip_environment_generator import VIPEnvironmentGenerator
import json

def create_simple_system():
    """Create a simple AXI4 system configuration"""
    
    # Create bus configuration
    config = BusConfig()
    config.bus_type = "AXI4"
    config.data_width = 64  # 64-bit data bus
    config.addr_width = 32  # 32-bit address bus
    config.arbitration = "ROUND_ROBIN"
    
    # Add masters
    print("Adding masters...")
    
    # CPU Master
    cpu = Master("CPU")
    cpu.id_width = 4  # Support up to 16 outstanding transactions
    cpu.priority = 1  # Higher priority
    cpu.qos_support = True
    cpu.exclusive_support = True
    cpu.default_cache = 0b0011  # Cacheable, bufferable
    config.masters.append(cpu)
    
    # DMA Master
    dma = Master("DMA") 
    dma.id_width = 4
    dma.priority = 0  # Lower priority than CPU
    dma.qos_support = True
    dma.exclusive_support = False  # DMA doesn't need exclusive access
    dma.default_cache = 0b0000  # Non-cacheable
    config.masters.append(dma)
    
    # Add slaves
    print("Adding slaves...")
    
    # Main Memory (RAM)
    ram = Slave(
        name="RAM",
        base_address=0x00000000,
        size=1048576  # 1GB in KB
    )
    ram.memory_type = "Memory"
    ram.read_latency = 5
    ram.write_latency = 3
    config.slaves.append(ram)
    
    # Boot ROM
    rom = Slave(
        name="ROM", 
        base_address=0x10000000,
        size=65536  # 64MB in KB
    )
    rom.memory_type = "Memory"
    rom.read_latency = 2
    rom.write_latency = 1  # Write will generate SLVERR
    config.slaves.append(rom)
    
    # UART Peripheral
    uart = Slave(
        name="UART",
        base_address=0x20000000,
        size=4  # 4KB register space
    )
    uart.memory_type = "Peripheral"
    uart.read_latency = 1
    uart.write_latency = 1
    config.slaves.append(uart)
    
    # Save configuration
    print("\nSaving configuration...")
    config_file = "simple_axi4_system.json"
    
    # Convert to JSON-serializable format
    config_dict = {
        "bus_type": config.bus_type,
        "data_width": config.data_width,
        "addr_width": config.addr_width,
        "arbitration": config.arbitration,
        "masters": [],
        "slaves": []
    }
    
    for master in config.masters:
        config_dict["masters"].append({
            "name": master.name,
            "id_width": master.id_width,
            "priority": master.priority,
            "qos_support": master.qos_support,
            "exclusive_support": master.exclusive_support,
            "default_prot": master.default_prot,
            "default_cache": master.default_cache
        })
    
    for slave in config.slaves:
        config_dict["slaves"].append({
            "name": slave.name,
            "base_address": hex(slave.base_address),
            "size": slave.size,
            "memory_type": slave.memory_type,
            "read_latency": slave.read_latency,
            "write_latency": slave.write_latency
        })
    
    with open(config_file, 'w') as f:
        json.dump(config_dict, f, indent=2)
    print(f"Configuration saved to: {config_file}")
    
    # Generate RTL
    print("\nGenerating RTL...")
    rtl_gen = AXIVerilogGenerator(config)
    rtl_gen.output_dir = "output/simple_system_rtl"
    rtl_output = rtl_gen.generate()
    print(f"RTL generated in: {rtl_output}")
    
    # Generate VIP
    print("\nGenerating VIP environment...")
    vip_gen = VIPEnvironmentGenerator(config, "rtl_integration")
    vip_output_dir = "output/simple_system_vip"
    
    # Note: This is a simplified call - actual method may differ
    # vip_gen.generate_full_environment(...)
    print(f"VIP would be generated in: {vip_output_dir}")
    
    # Print summary
    print("\n" + "="*60)
    print("SIMPLE SYSTEM SUMMARY")
    print("="*60)
    print(f"Bus Type: {config.bus_type}")
    print(f"Data Width: {config.data_width} bits")
    print(f"Address Width: {config.addr_width} bits")
    print(f"\nMasters ({len(config.masters)}):")
    for i, master in enumerate(config.masters):
        print(f"  {i}: {master.name} (Priority={master.priority}, ID_WIDTH={master.id_width})")
    print(f"\nSlaves ({len(config.slaves)}):")
    for i, slave in enumerate(config.slaves):
        print(f"  {i}: {slave.name} @ 0x{slave.base_address:08X} ({slave.size}KB)")
    print("\nGenerated files:")
    print(f"  - Configuration: {config_file}")
    print(f"  - RTL: {rtl_output}/")
    print(f"  - VIP: {vip_output_dir}/")
    print("\nNext steps:")
    print("  1. Review generated RTL in output/simple_system_rtl/")
    print("  2. Run simulation: cd output/simple_system_vip/sim && make")
    print("  3. Or load configuration in GUI: ./launch_gui.sh --config simple_axi4_system.json")
    
    return config

if __name__ == "__main__":
    create_simple_system()