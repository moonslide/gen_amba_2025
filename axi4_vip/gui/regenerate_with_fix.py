#!/usr/bin/env python3
"""Script to regenerate VIP files with the Verilog syntax fix"""

import os
import sys
import shutil

sys.path.append('src')

from bus_config import BusConfig, Master, Slave
from axi_verilog_generator import AXIVerilogGenerator
from vip_environment_generator import VIPEnvironmentGenerator

def regenerate_vip():
    """Regenerate VIP with the fixed syntax"""
    print("Regenerating VIP with Verilog syntax fix...")
    print("="*60)
    
    # Configuration matching the existing setup
    config = BusConfig()
    config.data_width = 32
    config.addr_width = 32
    
    # Add 8 masters
    for i in range(8):
        master = Master(f"master{i}")
        master.id_width = 4
        config.masters.append(master)
    
    # Add 8 slaves with address ranges
    base_addr = 0x0000_0000
    for i in range(8):
        slave_base = base_addr + (i * 0x1000_0000)
        slave_size_kb = 0x1000_0000 // 1024  # Convert to KB (256MB = 262144 KB)
        slave = Slave(
            name=f"slave{i}",
            base_address=slave_base,
            size=slave_size_kb
        )
        config.slaves.append(slave)
    
    # Output directory
    output_base = "/home/timtim01/eda_test/project/gen_amba_2025/vip_test_fixed"
    os.makedirs(output_base, exist_ok=True)
    
    # 1. Generate RTL
    print("\n1. Generating RTL with fixed syntax...")
    rtl_dir = os.path.join(output_base, "rtl")
    os.makedirs(rtl_dir, exist_ok=True)
    
    rtl_gen = AXIVerilogGenerator(config)
    rtl_gen.output_dir = rtl_dir
    rtl_gen.generate()
    
    # Check the generated testbench
    tb_file = os.path.join(rtl_dir, "tb_axi4_interconnect_m8s8.v")
    if os.path.exists(tb_file):
        print(f"   ✓ Generated: {tb_file}")
        
        # Verify fix
        with open(tb_file, 'r') as f:
            content = f.read()
        
        if "{ID_WIDTH}'d0" in content:
            print("   ❌ ERROR: Old syntax still present!")
        elif "{ID_WIDTH{1'b0}}" in content:
            print("   ✓ Verified: Correct syntax used")
        else:
            print("   ⚠ Warning: Could not verify syntax")
    
    # 2. Generate VIP environment
    print("\n2. Generating VIP environment...")
    vip_dir = os.path.join(output_base, "axi4_vip_env")
    
    vip_gen = VIPEnvironmentGenerator()
    vip_gen.generate_full_environment(
        vip_dir,
        "axi4_vip",
        num_masters=8,
        num_slaves=8,
        data_width=32,
        addr_width=32,
        id_width=4
    )
    
    print(f"   ✓ Generated VIP environment in: {vip_dir}")
    
    # 3. Create RTL integration wrapper
    print("\n3. Creating RTL integration...")
    integration_dir = os.path.join(output_base, "axi4_vip_env_rtl_integration")
    os.makedirs(integration_dir, exist_ok=True)
    
    # Copy structure from VIP
    for item in ['env', 'sim', 'tb', 'tests']:
        src = os.path.join(vip_dir, item)
        dst = os.path.join(integration_dir, item)
        if os.path.exists(src):
            if os.path.exists(dst):
                shutil.rmtree(dst)
            shutil.copytree(src, dst)
    
    # Create RTL wrapper
    wrapper_dir = os.path.join(integration_dir, "rtl_wrapper")
    os.makedirs(wrapper_dir, exist_ok=True)
    
    # Copy generated RTL
    gen_rtl_dir = os.path.join(wrapper_dir, "generated_rtl")
    if os.path.exists(gen_rtl_dir):
        shutil.rmtree(gen_rtl_dir)
    shutil.copytree(rtl_dir, gen_rtl_dir)
    
    print(f"   ✓ Created RTL integration in: {integration_dir}")
    
    # 4. Display results
    print("\n" + "="*60)
    print("REGENERATION COMPLETE!")
    print(f"\nGenerated files in: {output_base}")
    print("\nTo compile and verify:")
    print(f"  cd {integration_dir}/sim")
    print("  make compile")
    print("  # Check logs/compile.log for any syntax errors")
    print("\nTo run simulation:")
    print("  make run")
    print("\nTo debug with Verdi:")
    print("  make verdi")
    
    # 5. Quick syntax check
    print("\n" + "="*60)
    print("SYNTAX VERIFICATION:")
    
    tb_file_new = os.path.join(gen_rtl_dir, "tb_axi4_interconnect_m8s8.v")
    if os.path.exists(tb_file_new):
        with open(tb_file_new, 'r') as f:
            lines = f.readlines()
        
        # Find and display a few examples
        print("\nSample tie-off assignments (should use {WIDTH{1'b0}} syntax):")
        count = 0
        for i, line in enumerate(lines):
            if "assign m" in line and "_awid" in line and count < 3:
                print(f"  Line {i+1}: {line.strip()}")
                count += 1

if __name__ == "__main__":
    regenerate_vip()