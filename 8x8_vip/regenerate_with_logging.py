#!/usr/bin/env python3
"""
Regenerate the 8x8 VIP environment with enhanced UVM_INFO logging
"""

import sys
import os

# Add parent directory to path to import the generator
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from axi4_vip.gui.src.vip_environment_generator import VIPEnvironmentGenerator

def main():
    # Create minimal config for generator
    class MinimalConfig:
        def __init__(self):
            self.num_masters = 8
            self.num_slaves = 8
            self.output_dir = "/home/timtim01/eda_test/project/gen_amba_2025/vip_test/axi4_vip_env_rtl_integration"
            self.data_width = 32
            self.addr_width = 32
            self.id_width = 8
            self.user_width = 1
            self.strb_width = 4
            # Create master and slave configs
            self.masters = []
            self.slaves = []
            for i in range(8):
                master = type('Master', (), {})()
                master.name = f"master_{i}"
                master.id = i
                master.id_width = 4
                master.user_width = 1
                master.data_width = 32
                master.addr_width = 32
                master.qos_support = True
                master.exclusive_support = True
                master.cache_support = True
                master.prot_support = True
                master.region_support = True
                self.masters.append(master)
            for i in range(8):
                slave = type('Slave', (), {})()
                slave.name = f"slave_{i}"
                slave.id = i
                slave.base_address = i * 0x10000000
                slave.size = 0x10000000
                slave.data_width = 32
                slave.addr_width = 32
                slave.memory_type = "RAM"
                slave.response_delay = 1
                # Add method for end address calculation
                slave.get_end_address = lambda: slave.base_address + slave.size - 1
                self.slaves.append(slave)
    
    config = MinimalConfig()
    
    # Create generator instance
    generator = VIPEnvironmentGenerator(config, 'vip')
    
    # Generate 8x8 VIP environment with enhanced logging
    print("Regenerating 8x8 VIP environment with enhanced UVM_INFO logging...")
    generator.generate_environment(
        output_dir="/home/timtim01/eda_test/project/gen_amba_2025/vip_test/axi4_vip_env_rtl_integration"
    )
    
    print("VIP environment regenerated with comprehensive logging:")
    print("- Master driver: Transaction details and phase logging")
    print("- Master monitor: Channel activity monitoring")
    print("- Interface: Signal-level activity display")
    print("- Tests: Build and run phase logging")
    print("- Sequences: Transaction creation logging")
    print("\nThe enhanced logging will help trace VIP activity in waveforms.")

if __name__ == "__main__":
    main()