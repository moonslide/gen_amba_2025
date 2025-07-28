#!/usr/bin/env python3
"""Regenerate VIP environment with compilation fixes"""

import os
import sys
import shutil
sys.path.insert(0, 'src')

from bus_config import BusConfig, Master, Slave
from vip_environment_generator import VIPEnvironmentGenerator

# Clean up old environment
output_dir = "/home/timtim01/eda_test/project/gen_amba_2025/output"
if os.path.exists(os.path.join(output_dir, "axi4_vip_env_rtl_integration")):
    shutil.rmtree(os.path.join(output_dir, "axi4_vip_env_rtl_integration"))
    print("Removed old VIP environment")

# Create configuration from existing setup
config = BusConfig()
config.bus_type = "AXI4"
config.data_width = 32
config.addr_width = 32

# Add masters and slaves
config.masters = [
    Master(name="Master_0", id_width=4, qos_support=True),
    Master(name="Master_1", id_width=4, qos_support=True)
]

config.slaves = [
    Slave(name="Slave_0", base_address=0x0, size=1024),  # 1MB
    Slave(name="Slave_1", base_address=0x100000, size=256), # 256KB
    Slave(name="Slave_2", base_address=0x140000, size=64)   # 64KB
]

# Generate new environment
print("Generating new VIP environment with fixes...")
generator = VIPEnvironmentGenerator(config, mode="rtl_integration", simulator="vcs")
env_path = generator.generate_environment(output_dir)

print(f"\nNew VIP environment generated at: {env_path}")
print("\nTo test compilation:")
print(f"cd {env_path}/sim")
print("make compile")