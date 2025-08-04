#!/usr/bin/env python3
"""Regenerate VIP environment with compilation fixes for vip_test directory"""

import os
import sys
import shutil
sys.path.insert(0, '/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src')

from bus_config import BusConfig, Master, Slave
from vip_environment_generator import VIPEnvironmentGenerator

# Clean up old environment
output_dir = "/home/timtim01/eda_test/project/gen_amba_2025/vip_test"
if os.path.exists(os.path.join(output_dir, "axi4_vip_env_rtl_integration")):
    shutil.rmtree(os.path.join(output_dir, "axi4_vip_env_rtl_integration"))
    print("Removed old VIP environment")

# Create configuration matching the test environment
config = BusConfig()
config.bus_type = "AXI4"
config.data_width = 128
config.addr_width = 40

# Add 8 masters as configured
masters = [
    ("CPU_Cluster_0", 6, True, True),
    ("CPU_Cluster_1", 6, True, True),
    ("GPU", 8, True, False),
    ("Video_Encoder", 4, True, False),
    ("Video_Decoder", 4, True, False),
    ("DMA_Engine_0", 4, True, False),
    ("DMA_Engine_1", 4, True, False),
    ("PCIe_Controller", 8, True, False)
]

for name, id_width, qos_support, exclusive_support in masters:
    master = Master(
        name=name,
        id_width=id_width,
        qos_support=qos_support,
        exclusive_support=exclusive_support
    )
    config.add_master(master)

# Add 8 slaves as configured
slaves = [
    ("DDR4_Channel_0", 0x0, 8388608, False, False),  # 8GB
    ("DDR4_Channel_1", 0x200000000, 8388608, False, False),  # 8GB
    ("L3_Cache_SRAM", 0x400000000, 16384, False, False),  # 16MB
    ("Boot_ROM", 0x1000000000, 256, False, False),  # 256KB
    ("System_Registers", 0x2000000000, 64, False, True),  # 64KB, privileged
    ("PCIe_Config_Space", 0x4000000000, 65536, False, False),  # 64MB
    ("Crypto_Engine", 0x8000000000, 256, True, True),  # 256KB, secure+privileged
    ("Debug_APB_Bridge", 0x10000000000, 1024, False, True)  # 1MB, privileged
]

for name, base_addr, size_kb, secure_only, privileged_only in slaves:
    slave = Slave(
        name=name,
        base_address=base_addr,
        size=size_kb,
        secure_only=secure_only,
        privileged_only=privileged_only
    )
    config.add_slave(slave)

# Generate new environment with fixes
print("Generating new VIP environment with compilation fixes...")
generator = VIPEnvironmentGenerator(config, mode="rtl_integration", simulator="vcs")
env_path = generator.generate_environment(output_dir)

print(f"\nNew VIP environment generated at: {env_path}")
print("\nTo test compilation:")
print(f"cd {env_path}/sim")
print("make compile")