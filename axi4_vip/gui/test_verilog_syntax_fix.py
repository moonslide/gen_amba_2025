#!/usr/bin/env python3
"""Test script to verify Verilog syntax fix"""

import os
import sys
import subprocess

sys.path.append('src')

from axi_verilog_generator import AXIVerilogGenerator
from vip_environment_generator import VIPEnvironmentGenerator

def test_generation():
    """Test RTL and VIP generation with the fixes"""
    print("Testing Verilog syntax fix...")
    
    # Test parameters
    config = {
        'num_masters': 2,
        'num_slaves': 3,
        'data_width': 32,
        'addr_width': 32,
        'id_width': 4,
        'output_dir': 'test_output_syntax',
        'project_name': 'syntax_test'
    }
    
    # Create output directory
    os.makedirs(config['output_dir'], exist_ok=True)
    
    # Test RTL generation
    print("\n1. Testing RTL generation...")
    rtl_gen = AXIVerilogGenerator(config)
    rtl_file = os.path.join(config['output_dir'], 'axi4_interconnect.v')
    tb_file = os.path.join(config['output_dir'], 'tb_axi4_interconnect.v')
    
    # Generate RTL and testbench
    rtl_gen.output_dir = config['output_dir']
    rtl_gen.generate()
    
    # Find generated testbench file
    tb_file = os.path.join(config['output_dir'], f"tb_axi4_interconnect_m{config['num_masters']}s{config['num_slaves']}.v")
    
    # Check for the old incorrect syntax
    print("\n2. Checking for incorrect syntax patterns...")
    with open(tb_file, 'r') as f:
        content = f.read()
        
    # Look for incorrect patterns
    incorrect_patterns = [
        "{ID_WIDTH}'d0",
        "{ADDR_WIDTH}'d0", 
        "{DATA_WIDTH}'d0"
    ]
    
    found_errors = False
    for pattern in incorrect_patterns:
        if pattern in content:
            print(f"ERROR: Found incorrect pattern: {pattern}")
            found_errors = True
            # Find line numbers
            lines = content.split('\n')
            for i, line in enumerate(lines):
                if pattern in line:
                    print(f"  Line {i+1}: {line.strip()}")
    
    if not found_errors:
        print("✓ No incorrect syntax patterns found")
    
    # Check for correct patterns
    print("\n3. Checking for correct syntax patterns...")
    correct_patterns = [
        "{ID_WIDTH{1'b0}}",
        "{ADDR_WIDTH{1'b0}}", 
        "{DATA_WIDTH{1'b0}}"
    ]
    
    found_correct = 0
    for pattern in correct_patterns:
        if pattern in content:
            print(f"✓ Found correct pattern: {pattern}")
            found_correct += 1
    
    print(f"\nFound {found_correct}/{len(correct_patterns)} correct patterns")
    
    # Test VIP generation
    print("\n4. Testing VIP generation...")
    vip_gen = VIPEnvironmentGenerator()
    vip_gen.generate_full_environment(
        config['output_dir'],
        config['project_name'],
        config['num_masters'],
        config['num_slaves'],
        config['data_width'],
        config['addr_width'],
        config['id_width']
    )
    
    # Check Makefile for VCS flags
    makefile_path = os.path.join(config['output_dir'], 'Makefile')
    if os.path.exists(makefile_path):
        with open(makefile_path, 'r') as f:
            makefile_content = f.read()
        
        if "-lca -kdb" in makefile_content:
            print("✓ VCS flags (-lca -kdb) found in Makefile")
        else:
            print("ERROR: VCS flags not found in Makefile")
    
    print("\n5. Compilation test (dry run)...")
    # Show what the generated tie-off looks like
    print("\nSample generated tie-off assignments:")
    lines = content.split('\n')
    for i, line in enumerate(lines):
        if 'Tie off master' in line:
            # Print next 10 lines
            for j in range(i, min(i+10, len(lines))):
                print(f"  {lines[j]}")
            break
    
    print("\nTest complete!")
    
    # Cleanup
    import shutil
    if os.path.exists(config['output_dir']):
        shutil.rmtree(config['output_dir'])
        print(f"\nCleaned up test directory: {config['output_dir']}")

if __name__ == "__main__":
    test_generation()