#!/usr/bin/env python3
"""Quick check of RTL generation"""

import os
import sys
import re

sys.path.append('src')

from bus_config import BusConfig, Master, Slave
from axi_verilog_generator import AXIVerilogGenerator

# Create config
config = BusConfig()
config.data_width = 32
config.addr_width = 32

# Add masters with different ID widths
master1 = Master("CPU")
master1.id_width = 6
config.masters.append(master1)

master2 = Master("DMA") 
master2.id_width = 8
config.masters.append(master2)

# Add slave
slave = Slave("Memory", base_address=0, size=1024)
config.slaves.append(slave)

# Generate
gen = AXIVerilogGenerator(config)
gen.output_dir = "check_output"
os.makedirs(gen.output_dir, exist_ok=True)
gen.generate()

# Check generated file
rtl_file = os.path.join(gen.output_dir, "axi4_interconnect_m2s1.v")
if os.path.exists(rtl_file):
    with open(rtl_file, 'r') as f:
        lines = f.readlines()
    
    print("Checking master port declarations...")
    print("="*50)
    
    # Find master port lines
    for i, line in enumerate(lines):
        if "_awid," in line or "_bid," in line or "_arid," in line or "_rid," in line:
            print(f"Line {i+1}: {line.strip()}")
            
            # Check if it's using ID_WIDTH
            if "[ID_WIDTH-1:0]" in line:
                print("  ✓ Using ID_WIDTH")
            else:
                # Extract the width
                match = re.search(r'\[(\d+):0\]', line)
                if match:
                    width = int(match.group(1)) + 1
                    print(f"  ❌ Hardcoded to {width} bits")

# Cleanup
import shutil
if os.path.exists("check_output"):
    shutil.rmtree("check_output")