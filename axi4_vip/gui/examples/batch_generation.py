#!/usr/bin/env python3
"""
Example: Batch generation of multiple bus configurations
Demonstrates automated generation for different system variants
"""

import sys
import os
import json
sys.path.append(os.path.join(os.path.dirname(__file__), '..', 'src'))

from bus_config import BusConfig, Master, Slave
from axi_verilog_generator import AXIVerilogGenerator

def create_system_variant(num_masters, num_slaves, data_width, name_suffix):
    """Create a system variant with specified parameters"""
    
    config = BusConfig()
    config.bus_type = "AXI4"
    config.data_width = data_width
    config.addr_width = 32 if data_width <= 64 else 40  # Wider address for larger systems
    config.arbitration = "QOS" if num_masters > 4 else "ROUND_ROBIN"
    
    # Add masters
    master_types = [
        ("CPU", 15, True, True),
        ("GPU", 12, True, False),
        ("DMA", 8, True, False),
        ("DSP", 10, True, False),
        ("Video", 9, True, False),
        ("Audio", 7, False, False),
        ("USB", 6, False, False),
        ("Ethernet", 5, False, False)
    ]
    
    for i in range(num_masters):
        master_type = master_types[i % len(master_types)]
        master = Master(f"{master_type[0]}_{i}")
        master.id_width = 4 if i < 4 else 2  # First 4 masters get more IDs
        master.priority = master_type[1] - (i // len(master_types))
        master.qos_support = master_type[2]
        master.exclusive_support = master_type[3]
        config.masters.append(master)
    
    # Add slaves
    slave_types = [
        ("DDR", "Memory", 20, 10, 4194304),    # 4GB
        ("SRAM", "Memory", 3, 2, 32768),       # 32MB
        ("Flash", "Memory", 10, 50, 262144),   # 256MB
        ("Config", "Peripheral", 2, 2, 64),    # 64KB
        ("IO", "Peripheral", 3, 3, 256),       # 256KB
    ]
    
    base_addr = 0x00000000
    for i in range(num_slaves):
        slave_type = slave_types[i % len(slave_types)]
        slave = Slave(
            f"{slave_type[0]}_{i}",
            base_addr,
            slave_type[4]  # size
        )
        slave.memory_type = slave_type[1]
        slave.read_latency = slave_type[2]
        slave.write_latency = slave_type[3]
        config.slaves.append(slave)
        
        # Calculate next base address (aligned)
        base_addr += slave_type[4] * 1024  # Convert KB to bytes
        # Align to next power of 2
        if base_addr & (base_addr - 1):
            base_addr = 1 << (base_addr.bit_length())
    
    return config, f"system_{name_suffix}"

def generate_batch_systems():
    """Generate multiple system variants"""
    
    print("AMBA Bus Matrix Batch Generation")
    print("="*60)
    
    # Define variants to generate
    variants = [
        # (masters, slaves, data_width, name)
        (2, 3, 32, "small_32b"),      # Small embedded system
        (2, 3, 64, "small_64b"),      # Small with wider bus
        (4, 4, 64, "medium_64b"),     # Medium system
        (4, 4, 128, "medium_128b"),   # Medium with high bandwidth
        (8, 5, 128, "large_128b"),    # Large system
        (8, 8, 256, "large_256b"),    # High-performance system
        (16, 8, 512, "xlarge_512b"),  # Very large system
    ]
    
    results = []
    
    for variant in variants:
        num_masters, num_slaves, data_width, name = variant
        print(f"\nGenerating {name}...")
        print(f"  Masters: {num_masters}, Slaves: {num_slaves}, Data Width: {data_width}")
        
        try:
            # Create configuration
            config, system_name = create_system_variant(
                num_masters, num_slaves, data_width, name
            )
            
            # Save configuration
            config_file = f"batch_output/{system_name}_config.json"
            os.makedirs("batch_output", exist_ok=True)
            
            config_dict = {
                "system_name": system_name,
                "bus_type": config.bus_type,
                "data_width": config.data_width,
                "addr_width": config.addr_width,
                "arbitration": config.arbitration,
                "num_masters": len(config.masters),
                "num_slaves": len(config.slaves),
                "masters": [{"name": m.name, "id_width": m.id_width, 
                           "priority": m.priority} for m in config.masters],
                "slaves": [{"name": s.name, "base_address": hex(s.base_address),
                          "size_kb": s.size} for s in config.slaves]
            }
            
            with open(config_file, 'w') as f:
                json.dump(config_dict, f, indent=2)
            
            # Generate RTL
            rtl_gen = AXIVerilogGenerator(config)
            rtl_gen.output_dir = f"batch_output/{system_name}_rtl"
            rtl_output = rtl_gen.generate()
            
            # Calculate metrics
            total_bandwidth = config.data_width * num_masters / 8  # GB/s at 1GHz
            total_memory = sum(s.size for s in config.slaves 
                             if s.memory_type == "Memory") / 1048576  # GB
            
            result = {
                "name": system_name,
                "masters": num_masters,
                "slaves": num_slaves,
                "data_width": data_width,
                "bandwidth_gbps": total_bandwidth,
                "memory_gb": total_memory,
                "config_file": config_file,
                "rtl_dir": rtl_output,
                "status": "SUCCESS"
            }
            results.append(result)
            
            print(f"  ✓ Generated successfully")
            print(f"    - Peak bandwidth: {total_bandwidth} GB/s")
            print(f"    - Total memory: {total_memory:.1f} GB")
            
        except Exception as e:
            print(f"  ✗ Generation failed: {str(e)}")
            results.append({
                "name": name,
                "status": "FAILED",
                "error": str(e)
            })
    
    # Generate summary report
    print("\n" + "="*60)
    print("BATCH GENERATION SUMMARY")
    print("="*60)
    
    summary_file = "batch_output/generation_summary.json"
    with open(summary_file, 'w') as f:
        json.dump({
            "total_variants": len(variants),
            "successful": len([r for r in results if r["status"] == "SUCCESS"]),
            "failed": len([r for r in results if r["status"] == "FAILED"]),
            "results": results
        }, f, indent=2)
    
    # Print summary table
    print(f"\n{'System':<20} {'Masters':<8} {'Slaves':<8} {'Width':<8} {'Status':<10}")
    print("-" * 60)
    for result in results:
        if result["status"] == "SUCCESS":
            print(f"{result['name']:<20} {result['masters']:<8} "
                  f"{result['slaves']:<8} {result['data_width']:<8} "
                  f"{result['status']:<10}")
        else:
            print(f"{result['name']:<20} {'N/A':<8} {'N/A':<8} "
                  f"{'N/A':<8} {result['status']:<10}")
    
    print(f"\nSummary saved to: {summary_file}")
    print("\nGenerated files in: batch_output/")
    print("\nNext steps:")
    print("  1. Review configurations in batch_output/*_config.json")
    print("  2. Examine RTL in batch_output/*_rtl/")
    print("  3. Run synthesis on different variants")
    print("  4. Compare area/timing results")
    
    # Create comparison script
    comparison_script = """#!/bin/bash
# Compare generated RTL files

echo "RTL Comparison Report"
echo "===================="

for dir in batch_output/*_rtl; do
    if [ -d "$dir" ]; then
        system=$(basename "$dir" _rtl)
        echo -e "\\n$system:"
        
        # Count lines of RTL
        total_lines=$(find "$dir" -name "*.v" -exec wc -l {} + | tail -1 | awk '{print $1}')
        echo "  Total RTL lines: $total_lines"
        
        # Count modules
        num_modules=$(grep -h "^module" "$dir"/*.v 2>/dev/null | wc -l)
        echo "  Number of modules: $num_modules"
        
        # Check main interconnect
        main_file=$(find "$dir" -name "axi4_interconnect_*.v" | head -1)
        if [ -f "$main_file" ]; then
            params=$(grep "parameter" "$main_file" | head -5)
            echo "  Parameters:"
            echo "$params" | sed 's/^/    /'
        fi
    fi
done
"""
    
    with open("batch_output/compare_rtl.sh", 'w') as f:
        f.write(comparison_script)
    os.chmod("batch_output/compare_rtl.sh", 0o755)
    
    return results

if __name__ == "__main__":
    generate_batch_systems()