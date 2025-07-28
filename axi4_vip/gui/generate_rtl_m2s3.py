#!/usr/bin/env python3
"""
Generate RTL for AXI4 interconnect with 2 masters and 3 slaves
"""

import os
import sys
import json
from datetime import datetime

# Add src directory to path
sys.path.append(os.path.join(os.path.dirname(__file__), 'src'))

from axi_verilog_generator import AXIVerilogGenerator
from bus_config import BusConfig, Master, Slave

def load_config_from_json(json_file):
    """Load bus configuration from JSON file"""
    with open(json_file, 'r') as f:
        data = json.load(f)
    
    config = BusConfig()
    config.bus_type = data.get('bus_type', 'AXI4')
    config.data_width = data.get('data_width', 64)
    config.addr_width = data.get('addr_width', 32)
    config.arbitration = data.get('arbitration', 'QOS')
    
    # Load masters
    for m_data in data.get('masters', []):
        master = Master(
            name=m_data['name'],
            id_width=m_data.get('id_width', 4),
            qos_support=m_data.get('qos_support', True),
            exclusive_support=m_data.get('exclusive_support', True),
            user_width=m_data.get('user_width', 0),
            priority=m_data.get('priority', 0),
            default_prot=m_data.get('default_prot', 2),
            default_cache=m_data.get('default_cache', 3),
            default_region=m_data.get('default_region', 0)
        )
        config.add_master(master)
    
    # Load slaves
    for s_data in data.get('slaves', []):
        slave = Slave(
            name=s_data['name'],
            base_address=s_data['base_address'],
            size=s_data['size'],
            memory_type=s_data.get('memory_type', 'Memory'),
            read_latency=s_data.get('read_latency', 1),
            write_latency=s_data.get('write_latency', 1),
            num_regions=s_data.get('num_regions', 1),
            secure_only=s_data.get('secure_only', False),
            privileged_only=s_data.get('privileged_only', False)
        )
        config.add_slave(slave)
    
    return config

def main():
    # Output directory as requested
    output_dir = "/home/timtim01/eda_test/project/gen_amba_2025/output/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl"
    
    # Load configuration from JSON template
    json_file = "templates/simple_axi4_2m3s.json"
    
    print(f"Loading configuration from: {json_file}")
    config = load_config_from_json(json_file)
    
    print(f"Configuration loaded:")
    print(f"  Bus Type: {config.bus_type}")
    print(f"  Data Width: {config.data_width}")
    print(f"  Address Width: {config.addr_width}")
    print(f"  Arbitration: {config.arbitration}")
    print(f"  Masters: {len(config.masters)}")
    for i, m in enumerate(config.masters):
        print(f"    {i}: {m.name}")
    print(f"  Slaves: {len(config.slaves)}")
    for i, s in enumerate(config.slaves):
        print(f"    {i}: {s.name} @ 0x{s.base_address:08X} ({s.size}KB)")
    
    # Create output directory
    os.makedirs(output_dir, exist_ok=True)
    print(f"\nCreating output directory: {output_dir}")
    
    # Create generator with custom output directory
    generator = AXIVerilogGenerator(config)
    generator.output_dir = output_dir
    
    # Generate RTL
    print("\nGenerating RTL files...")
    try:
        result_dir = generator.generate()
        print(f"RTL generation completed successfully!")
        print(f"Files generated in: {result_dir}")
        
        # List generated files
        files = os.listdir(result_dir)
        verilog_files = [f for f in files if f.endswith('.v')]
        print(f"\nGenerated Verilog files:")
        for f in sorted(verilog_files):
            print(f"  - {f}")
            
    except Exception as e:
        print(f"Error generating RTL: {e}")
        return 1
    
    return 0

if __name__ == "__main__":
    sys.exit(main())