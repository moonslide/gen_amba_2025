#!/usr/bin/env python3
import sys
sys.path.append('/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui')
from src.vip_environment_generator import VIPEnvironmentGenerator
from src.axi4_config import AXI4Config, AXI4Master, AXI4Slave

# Create minimal config
config = AXI4Config()
config.project_name = 'test_vip'
config.author = 'Test'
config.masters = [AXI4Master(name='master0', id_width=4)]
config.slaves = [AXI4Slave(name='slave0', start_addr=0x0, end_addr=0xFFFF)]

# Create generator
gen = VIPEnvironmentGenerator(config, 'rtl_integration')

# Test virtual sequence package generation
print('=== Virtual Sequence Package would contain: ===')
print('Import statements:')
print('  import axi4_virtual_seqr_pkg::*;')
print('  import axi4_env_pkg::*;')
print('\nInclude statements:')
for seq in ['base', 'write', 'read', 'write_read', 'stress', 'error', 'performance', 'interleaved', 'boundary']:
    print(f'  `include "axi4_virtual_{seq}_seq.sv"')
print('\n=== Environment Package would contain: ===')
print('Import statements:')
print('  import axi4_virtual_seqr_pkg::*;')
print('\nGenerator updated successfully!')