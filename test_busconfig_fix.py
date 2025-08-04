#!/usr/bin/env python3
"""Test script to verify BusConfig fixes"""

import sys
import os
sys.path.insert(0, '/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src')

# Test both BusConfig classes
print("Testing bus_config.py BusConfig:")
try:
    from bus_config import BusConfig as BusConfig1, Master, Slave
    config1 = BusConfig1()
    print(f"✓ bus_config.BusConfig created successfully")
    print(f"  has_qos: {config1.has_qos}")
    print(f"  has_cache: {config1.has_cache}")
    print(f"  has_prot: {config1.has_prot}")
    print(f"  has_region: {config1.has_region}")
    print(f"  has_user: {config1.has_user}")
except Exception as e:
    print(f"✗ Error creating bus_config.BusConfig: {e}")

print("\nTesting bus_matrix_gui.py BusConfig:")
try:
    from bus_matrix_gui import BusConfig as BusConfig2, MasterConfig, SlaveConfig
    config2 = BusConfig2(
        bus_type="AXI4",
        data_width=64,
        addr_width=32,
        masters=[],
        slaves=[],
        arbitration="QOS"
    )
    print(f"✓ bus_matrix_gui.BusConfig created successfully")
    print(f"  has_qos: {config2.has_qos}")
    print(f"  has_cache: {config2.has_cache}")
    print(f"  has_prot: {config2.has_prot}")
    print(f"  has_region: {config2.has_region}")
    print(f"  has_user: {config2.has_user}")
except Exception as e:
    print(f"✗ Error creating bus_matrix_gui.BusConfig: {e}")

print("\nTesting VIP generator with BusConfig:")
try:
    from vip_environment_generator import VIPEnvironmentGenerator
    
    # Use bus_config.BusConfig (the proper one)
    config = BusConfig1()
    config.add_master(Master("CPU", 4, 8, 8))
    config.add_master(Master("DMA", 4, 8, 8))
    config.add_slave(Slave("DDR", 0x00000000, 1024*1024))
    config.add_slave(Slave("ROM", 0x10000000, 64))
    
    generator = VIPEnvironmentGenerator(config, mode="basic")
    print("✓ VIPEnvironmentGenerator created successfully")
    
    # Test the attributes that were causing the error
    print(f"  Generator accessing config.has_qos: {generator.config.has_qos}")
    print(f"  Generator accessing config.has_cache: {generator.config.has_cache}")
    print(f"  Generator accessing config.has_prot: {generator.config.has_prot}")
    
except Exception as e:
    print(f"✗ Error with VIP generator: {e}")
    import traceback
    traceback.print_exc()

print("\nTest completed!")