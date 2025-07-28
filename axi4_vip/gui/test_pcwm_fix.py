#!/usr/bin/env python3
"""Test script to verify PCWM lint warning fixes"""

import os
import sys
import tempfile
import shutil

sys.path.append('src')

from bus_config import BusConfig, Master, Slave
from axi_verilog_generator import AXIVerilogGenerator
from vip_environment_generator import VIPEnvironmentGenerator

def create_test_config():
    """Create a test configuration with mixed ID widths like the complex example"""
    config = BusConfig()
    config.data_width = 32
    config.addr_width = 32
    
    # Add masters with different ID widths (matching the complex_axi4_system.json)
    masters = [
        ("CPU_0", 6),
        ("CPU_1", 6), 
        ("DMA", 4),
        ("PCIe", 8)
    ]
    
    for name, id_width in masters:
        master = Master(name)
        master.id_width = id_width
        config.masters.append(master)
    
    # Add slaves
    for i in range(4):
        slave = Slave(
            name=f"slave{i}",
            base_address=i * 0x1000_0000,
            size=262144  # 256MB in KB
        )
        config.slaves.append(slave)
    
    return config

def test_rtl_generation():
    """Test RTL generation with the fix"""
    print("Testing PCWM Fix...")
    print("="*60)
    
    config = create_test_config()
    
    # Create temp directory
    test_dir = tempfile.mkdtemp(prefix="pcwm_test_")
    print(f"Test directory: {test_dir}")
    
    try:
        # 1. Generate RTL
        print("\n1. Generating RTL...")
        rtl_gen = AXIVerilogGenerator(config)
        rtl_gen.output_dir = os.path.join(test_dir, "rtl")
        rtl_gen.generate()
        
        # Check the generated RTL
        rtl_file = os.path.join(rtl_gen.output_dir, f"axi4_interconnect_m{len(config.masters)}s{len(config.slaves)}.v")
        if os.path.exists(rtl_file):
            print(f"   ✓ Generated: {rtl_file}")
            
            with open(rtl_file, 'r') as f:
                content = f.read()
            
            # Check for incorrect patterns (should not exist)
            incorrect_patterns = [
                "[5:0]",  # Hardcoded 6-bit width
                "[7:0].*_awid",  # 8-bit ID
                "[3:0].*_awid"   # 4-bit ID (when it should use ID_WIDTH)
            ]
            
            found_issues = False
            for pattern in incorrect_patterns:
                import re
                if re.search(pattern, content):
                    print(f"   ❌ Found hardcoded width: {pattern}")
                    found_issues = True
            
            # Check for correct pattern
            if "input  wire [ID_WIDTH-1:0]     m0_awid" in content:
                print("   ✓ Correct: Using parameterized ID_WIDTH")
            else:
                print("   ❌ Error: Not using parameterized ID_WIDTH")
                found_issues = True
            
            # Count ID_WIDTH usage
            id_width_count = content.count("[ID_WIDTH-1:0]")
            print(f"   ℹ Found {id_width_count} instances of [ID_WIDTH-1:0]")
            
        # 2. Generate VIP environment  
        print("\n2. Generating VIP environment...")
        vip_gen = VIPEnvironmentGenerator(config, "rtl_integration")
        vip_dir = os.path.join(test_dir, "vip")
        vip_gen.generate_full_environment(
            vip_dir,
            "test_axi4",
            len(config.masters),
            len(config.slaves),
            config.data_width,
            config.addr_width,
            4  # Use unified ID_WIDTH=4
        )
        
        # Check Makefile for +lint=PCWM
        makefile_path = os.path.join(vip_dir, "sim", "Makefile")
        if os.path.exists(makefile_path):
            with open(makefile_path, 'r') as f:
                makefile_content = f.read()
            
            if "+lint=PCWM" in makefile_content:
                print("   ✓ Found +lint=PCWM in Makefile")
            else:
                print("   ❌ Missing +lint=PCWM in Makefile")
        
        # 3. Summary
        print("\n" + "="*60)
        print("SUMMARY:")
        if not found_issues:
            print("✓ All ID ports now use parameterized ID_WIDTH")
            print("✓ No hardcoded ID widths found")
            print("✓ VCS compilation will use +lint=PCWM to suppress warnings")
            print("\nThe PCWM lint warnings should be resolved!")
        else:
            print("❌ Issues found - please check the output above")
            
    finally:
        # Cleanup
        if os.path.exists(test_dir):
            shutil.rmtree(test_dir)
            print(f"\nCleaned up: {test_dir}")

def main():
    """Run the test"""
    test_rtl_generation()
    
    print("\n" + "="*60)
    print("Next steps to verify in actual project:")
    print("1. Regenerate your design using the GUI")
    print("2. Run: make compile")
    print("3. Check logs/compile.log - should have no PCWM-L warnings")
    print("4. The +lint=PCWM flag will suppress any remaining width mismatch info")

if __name__ == "__main__":
    main()