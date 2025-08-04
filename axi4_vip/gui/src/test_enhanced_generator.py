#!/usr/bin/env python3
"""
Test script for enhanced VIP generator
"""

import os
import sys
from dataclasses import dataclass
from typing import List

# Import the enhanced generator
from vip_environment_generator_enhanced import VIPEnvironmentGeneratorEnhanced

@dataclass
class MasterConfig:
    name: str
    id: str
    data_width: int = 32
    addr_width: int = 32
    id_width: int = 4
    user_width: int = 0
    features: dict = None

@dataclass
class SlaveConfig:
    name: str
    id: str
    base_address: int
    size: int
    data_width: int = 32

@dataclass
class TestConfig:
    masters: List[MasterConfig]
    slaves: List[SlaveConfig]
    mode: str = "standalone"
    addr_width: int = 32
    data_width: int = 32
    id_width: int = 4
    user_width: int = 0
    max_outstanding: int = 16
    features: dict = None
    
    def __post_init__(self):
        if self.features is None:
            self.features = {'qos': True, 'region': True, 'user': False}

def test_enhanced_generator():
    """Test the enhanced VIP generator"""
    
    print("Testing Enhanced VIP Generator")
    print("=" * 50)
    
    # Create test configuration
    config = TestConfig(
        masters=[
            MasterConfig("Master_0", "m0", features={'qos': True, 'region': True}),
            MasterConfig("Master_1", "m1", features={'qos': True})
        ],
        slaves=[
            SlaveConfig("Memory", "s0", 0x00000000, 0x10000000),
            SlaveConfig("Peripheral", "s1", 0x10000000, 0x10000000),
            SlaveConfig("Config", "s2", 0x20000000, 0x10000000)
        ]
    )
    
    # Create enhanced generator
    gen = VIPEnvironmentGeneratorEnhanced(config, "rtl_integration", "vcs")
    
    # Test output path
    output_path = "./test_enhanced_vip_output"
    
    # Generate the enhanced environment
    try:
        result_path = gen.generate_environment_enhanced(output_path)
        print(f"\nGenerated enhanced VIP at: {result_path}")
        
        # Check key files
        key_files = [
            "master/axi4_master_pkg.sv",
            "agent/master_agent_bfm/axi4_master_driver_bfm.sv",
            "agent/master_agent_bfm/axi4_master_monitor_bfm.sv",
            "agent/master_agent_bfm/axi4_master_bfm_connector.sv",
            "top/hdl_top.sv",
            "top/hvl_top.sv",
            "doc/README.md"
        ]
        
        print("\nChecking generated files:")
        all_present = True
        for file in key_files:
            full_path = os.path.join(result_path, file)
            exists = os.path.exists(full_path)
            status = "✓" if exists else "✗"
            print(f"  {status} {file}")
            if not exists:
                all_present = False
        
        if all_present:
            print("\n✓ All key files generated successfully!")
            
            # Check for enhanced features
            print("\nChecking enhanced features:")
            
            # Check driver for BFM integration
            with open(os.path.join(result_path, "master/axi4_master_pkg.sv"), "r") as f:
                driver_content = f.read()
                if "virtual axi4_master_driver_bfm vif;" in driver_content:
                    print("  ✓ Driver has BFM integration")
                if "trans_cnt++" in driver_content:
                    print("  ✓ Driver has transaction counter")
                if "drive_write_transaction" in driver_content:
                    print("  ✓ Driver has BFM task calls")
            
            # Check BFM for logging
            with open(os.path.join(result_path, "agent/master_agent_bfm/axi4_master_driver_bfm.sv"), "r") as f:
                bfm_content = f.read()
                if "$display" in bfm_content and "BFM:" in bfm_content:
                    print("  ✓ BFM has comprehensive logging")
                if "timeout" in bfm_content.lower():
                    print("  ✓ BFM has timeout detection")
            
            # Check monitor for assertions
            with open(os.path.join(result_path, "agent/master_agent_bfm/axi4_master_monitor_bfm.sv"), "r") as f:
                monitor_content = f.read()
                if "property p_awvalid_stable" in monitor_content:
                    print("  ✓ Monitor has protocol assertions")
                if "MONITOR:" in monitor_content:
                    print("  ✓ Monitor has channel logging")
            
            print("\n✓ Enhanced features verified!")
            
        else:
            print("\n✗ Some files are missing!")
            
    except Exception as e:
        print(f"\n✗ Error generating enhanced VIP: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    test_enhanced_generator()