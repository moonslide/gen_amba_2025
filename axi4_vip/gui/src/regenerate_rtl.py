#!/usr/bin/env python3
"""Quick RTL regeneration script"""

import json
import sys
sys.path.insert(0, '/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src')

from bus_config import BusConfig, Master, Slave
from axi_verilog_generator import AXIVerilogGenerator

# Load configuration
with open('/home/timtim01/eda_test/project/gen_amba_2025/test/axi4_vip_env_rtl_integration/saved_config.json', 'r') as f:
    config_data = json.load(f)

# Recreate configuration object
config = BusConfig(
    protocol="AXI4",
    data_width=config_data['data_width'],
    addr_width=config_data['addr_width']
)

# Add masters
for m in config_data['masters']:
    master = Master(
        name=m['name'],
        id_width=m.get('id_width', 4),
        qos_support=m.get('qos_support', False),
        exclusive_support=m.get('exclusive_support', False)
    )
    config.add_master(master)

# Add slaves
for s in config_data['slaves']:
    slave = Slave(
        name=s['name'],
        base_address=s['base_address'],
        size=s['size'],
        secure_only=s.get('secure_only', False),
        privileged_only=s.get('privileged_only', False)
    )
    if 'allowed_masters' in s and s['allowed_masters']:
        slave.allowed_masters = s['allowed_masters']
    config.add_slave(slave)

# Generate RTL
output_dir = '/home/timtim01/eda_test/project/gen_amba_2025/test/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl'
generator = AXIVerilogGenerator(config, output_dir)
generator.generate_address_decoder()
generator.generate_arbiter()

print("RTL files regenerated successfully!")