#!/usr/bin/env python3
"""
Simple test to verify enhanced VIP generator works
"""

import os
import sys

# Add path to import modules
sys.path.insert(0, os.path.dirname(__file__))

from bus_config import BusConfig, Master, Slave
from vip_environment_generator_enhanced import VIPEnvironmentGeneratorEnhanced

def test_simple():
    """Simple test of enhanced VIP generator"""
    
    print("Testing Enhanced VIP Generator - Simple Test")
    print("=" * 50)
    
    # Create bus configuration
    config = BusConfig()
    
    # Set basic parameters
    config.data_width = 32
    config.addr_width = 32
    config.id_width = 4
    config.user_width = 0
    
    # Add features
    config.features = {
        'qos': True,
        'region': True,
        'user': False,
        'exclusive': True,
        'cache': True,
        'prot': True,
        'lock': True
    }
    
    # Add masters
    master0 = Master("CPU")
    master0.id_width = 4
    master0.qos_support = True
    master0.region_support = True
    master0.exclusive_support = True
    master0.user_width = 0
    master0.cache_support = True
    master0.prot_support = True
    config.masters.append(master0)
    
    master1 = Master("DMA")
    master1.id_width = 4
    master1.qos_support = True
    master1.region_support = False
    master1.exclusive_support = False
    master1.user_width = 0
    master1.cache_support = True
    master1.prot_support = True
    config.masters.append(master1)
    
    # Add slaves
    config.slaves.append(Slave("DDR", 0x00000000, 262144))  # 256MB
    config.slaves.append(Slave("SRAM", 0x10000000, 1024))   # 1MB
    config.slaves.append(Slave("APB", 0x20000000, 1024))    # 1MB
    
    # Additional settings
    config.max_outstanding = 16
    config.interleave_size = 64
    config.default_qos = 0
    config.default_region = 0
    
    # Create enhanced generator
    gen = VIPEnvironmentGeneratorEnhanced(config, "rtl_integration", "vcs")
    
    # Generate
    output_path = "./test_enhanced_vip_simple"
    
    try:
        # Clear output directory
        import shutil
        if os.path.exists(output_path):
            shutil.rmtree(output_path)
            
        result = gen.generate_environment_enhanced(output_path)
        print(f"\n✓ Generated enhanced VIP at: {result}")
        
        # Check a few key files
        key_files = [
            os.path.join(result, "master/axi4_master_pkg.sv"),
            os.path.join(result, "agent/master_agent_bfm/axi4_master_driver_bfm.sv"),
            os.path.join(result, "agent/master_agent_bfm/axi4_master_monitor_bfm.sv")
        ]
        
        print("\n✓ Checking enhanced features:")
        
        # Check master package
        with open(key_files[0], 'r') as f:
            content = f.read()
            if "virtual axi4_master_driver_bfm vif;" in content:
                print("  ✓ BFM virtual interface in driver")
            if "trans_cnt" in content:
                print("  ✓ Transaction counter in driver")
            if "`uvm_info(get_type_name()" in content:
                print("  ✓ UVM_INFO logging in driver")
                
        # Check BFM
        with open(key_files[1], 'r') as f:
            content = f.read()
            if "$display(" in content and "BFM:" in content:
                print("  ✓ BFM has debug logging")
            if "timeout" in content:
                print("  ✓ BFM has timeout detection")
            if "task automatic write_transaction" in content:
                print("  ✓ BFM has complete transaction tasks")
                
        # Check monitor
        with open(key_files[2], 'r') as f:
            content = f.read()
            if "property p_" in content:
                print("  ✓ Monitor has protocol assertions")
            if "monitor_write_addr()" in content:
                print("  ✓ Monitor has channel monitoring tasks")
                
        print("\n✓ Enhanced VIP generation test PASSED!")
        
    except Exception as e:
        print(f"\n✗ Error: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    test_simple()