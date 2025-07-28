#!/usr/bin/env python3
"""Find all hardcoded widths in generated RTL"""

import os
import sys
import re

sys.path.append('src')

from bus_config import BusConfig, Master, Slave  
from axi_verilog_generator import AXIVerilogGenerator

# Create test config
config = BusConfig()
config.data_width = 32
config.addr_width = 32

# Add 8 masters with mixed ID widths
for i in range(8):
    master = Master(f"master{i}")
    master.id_width = 6 if i < 2 else 4
    config.masters.append(master)

# Add 8 slaves
for i in range(8):
    slave = Slave(f"slave{i}", base_address=i*0x10000000, size=262144)
    config.slaves.append(slave)

# Generate
gen = AXIVerilogGenerator(config)
gen.output_dir = "width_check"
os.makedirs(gen.output_dir, exist_ok=True)
gen.generate()

# Find all hardcoded widths
rtl_file = os.path.join(gen.output_dir, "axi4_interconnect_m8s8.v")
if os.path.exists(rtl_file):
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    # Find all [N:0] patterns
    pattern = r'\[(\d+):0\]'
    matches = re.findall(pattern, content)
    
    # Count occurrences
    width_counts = {}
    for match in matches:
        width = int(match) + 1
        width_counts[width] = width_counts.get(width, 0) + 1
    
    print("Hardcoded widths found in generated RTL:")
    print("="*40)
    for width, count in sorted(width_counts.items()):
        print(f"{width}-bit: {count} occurrences")
    
    # Find specific examples
    print("\nExamples of hardcoded widths:")
    print("="*40)
    
    lines = content.split('\n')
    examples_shown = 0
    for i, line in enumerate(lines):
        if examples_shown >= 10:
            break
        match = re.search(r'\[(\d+):0\]', line)
        if match and not any(param in line for param in ['parameter', 'localparam']):
            width = int(match.group(1)) + 1
            if width in [4, 6, 8]:  # Suspicious widths
                print(f"Line {i+1}: {line.strip()}")
                examples_shown += 1

# Cleanup
import shutil
if os.path.exists("width_check"):
    shutil.rmtree("width_check")