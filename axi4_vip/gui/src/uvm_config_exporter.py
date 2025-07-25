#!/usr/bin/env python3
"""
UVM Configuration Exporter - Bridge between GUI and SystemVerilog UVM simulation
Exports GUI bus configuration to formats usable by UVM testbench
"""

import json
import os
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional

class UVMConfigExporter:
    """Exports GUI configuration to UVM-compatible formats"""
    
    def __init__(self, bus_config, vip_mode="BEHAVIORAL", rtl_path=None):
        """Initialize with GUI bus configuration object"""
        self.bus_config = bus_config
        self.vip_mode = vip_mode
        self.rtl_path = rtl_path
        self.export_timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        
    def export_json_config(self, output_path: str) -> bool:
        """Export configuration as JSON for UVM config reader"""
        try:
            config_data = {
                "export_info": {
                    "timestamp": self.export_timestamp,
                    "source": "AXI4_Bus_Matrix_GUI",
                    "version": "1.0"
                },
                "bus_config": {
                    "bus_type": self.bus_config.bus_type,
                    "addr_width": self.bus_config.addr_width,
                    "data_width": self.bus_config.data_width,
                    "arbitration": self.bus_config.arbitration
                },
                "vip_config": {
                    "vip_mode": self.vip_mode,
                    "rtl_path": self.rtl_path if self.rtl_path else ""
                },
                "masters": [],
                "slaves": []
            }
            
            # Export master configurations
            for i, master in enumerate(self.bus_config.masters):
                master_data = {
                    "index": i,
                    "name": master.name,
                    "id_width": getattr(master, 'id_width', 4),
                    "priority": getattr(master, 'priority', 0),
                    "qos_support": getattr(master, 'qos_support', True),
                    "exclusive_support": getattr(master, 'exclusive_support', True),
                    "user_width": getattr(master, 'user_width', 0),
                    "default_prot": getattr(master, 'default_prot', 0b010),
                    "default_cache": getattr(master, 'default_cache', 0b0011),
                    "default_region": getattr(master, 'default_region', 0)
                }
                config_data["masters"].append(master_data)
            
            # Export slave configurations
            for i, slave in enumerate(self.bus_config.slaves):
                slave_data = {
                    "index": i,
                    "name": slave.name,
                    "base_addr": f"0x{slave.base_address:X}",
                    "base_addr_int": slave.base_address,
                    "size_kb": slave.size,
                    "size_bytes": slave.size * 1024,
                    "end_addr": f"0x{slave.get_end_address():X}",
                    "memory_type": getattr(slave, 'memory_type', 'Memory'),
                    "priority": getattr(slave, 'priority', 0),
                    "num_regions": getattr(slave, 'num_regions', 1),
                    "secure_only": getattr(slave, 'secure_only', False),
                    "privileged_only": getattr(slave, 'privileged_only', False),
                    "read_latency": getattr(slave, 'read_latency', 1),
                    "write_latency": getattr(slave, 'write_latency', 1),
                    "read_latency_min": getattr(slave, 'read_latency', 1),
                    "read_latency_max": max(getattr(slave, 'read_latency', 1) * 2, 10),
                    "write_latency_min": getattr(slave, 'write_latency', 1),
                    "write_latency_max": max(getattr(slave, 'write_latency', 1) * 2, 10),
                    "allowed_masters": getattr(slave, 'allowed_masters', [])
                }
                config_data["slaves"].append(slave_data)
            
            # Write JSON file
            os.makedirs(os.path.dirname(output_path), exist_ok=True)
            with open(output_path, 'w') as f:
                json.dump(config_data, f, indent=2)
            
            print(f"[OK] UVM JSON configuration exported to: {output_path}")
            return True
            
        except Exception as e:
            print(f"[ERROR] Failed to export JSON configuration: {e}")
            return False
    
    def export_makefile_args(self, output_path: str) -> bool:
        """Export configuration as Makefile arguments"""
        try:
            makefile_args = [
                f"# AXI4 VIP Makefile Arguments - Generated {self.export_timestamp}",
                f"# Source: AXI4 Bus Matrix GUI",
                "",
                f"# Bus Configuration",
                f"BUS_TYPE = {self.bus_config.bus_type}",
                f"ADDR_WIDTH = {self.bus_config.addr_width}",
                f"DATA_WIDTH = {self.bus_config.data_width}",
                f"ARBITRATION = {self.bus_config.arbitration}",
                "",
                f"# Component Counts",
                f"NUM_MASTERS = {len(self.bus_config.masters)}",
                f"NUM_SLAVES = {len(self.bus_config.slaves)}",
                "",
                f"# UVM Test Arguments",
                f"UVM_ARGS = +CONFIG_FILE=$(CONFIG_JSON)",
                f"UVM_ARGS += +BUS_TYPE={self.bus_config.bus_type}",
                f"UVM_ARGS += +ADDR_WIDTH={self.bus_config.addr_width}",
                f"UVM_ARGS += +DATA_WIDTH={self.bus_config.data_width}",
                f"UVM_ARGS += +NUM_MASTERS={len(self.bus_config.masters)}",
                f"UVM_ARGS += +NUM_SLAVES={len(self.bus_config.slaves)}",
                f"UVM_ARGS += +VIP_MODE={self.vip_mode}",
                f"UVM_ARGS += +RTL_PATH={self.rtl_path if self.rtl_path else 'none'}",
                ""
            ]
            
            # Add slave-specific arguments
            makefile_args.append("# Slave Configuration Arguments")
            for i, slave in enumerate(self.bus_config.slaves):
                makefile_args.extend([
                    f"UVM_ARGS += +SLAVE_{i}_NAME={slave.name}",
                    f"UVM_ARGS += +SLAVE_{i}_BASE=0x{slave.base_address:X}",
                    f"UVM_ARGS += +SLAVE_{i}_SIZE=0x{slave.size * 1024:X}",
                ])
            
            makefile_args.append("")
            
            # Add master-specific arguments  
            makefile_args.append("# Master Configuration Arguments")
            for i, master in enumerate(self.bus_config.masters):
                makefile_args.extend([
                    f"UVM_ARGS += +MASTER_{i}_NAME={master.name}",
                    f"UVM_ARGS += +MASTER_{i}_PRIORITY={getattr(master, 'priority', 0)}",
                ])
            
            # Write makefile include
            os.makedirs(os.path.dirname(output_path), exist_ok=True)
            with open(output_path, 'w') as f:
                f.write('\n'.join(makefile_args))
            
            print(f"[OK] Makefile arguments exported to: {output_path}")
            return True
            
        except Exception as e:
            print(f"[ERROR] Failed to export Makefile arguments: {e}")
            return False
    
    def export_test_script(self, output_path: str, uvm_sim_path: str = "../axi4_vip_sim") -> bool:
        """Export a test execution script"""
        try:
            script_content = [
                "#!/bin/bash",
                "#==============================================================================",
                f"# AXI4 VIP Test Script - Generated {self.export_timestamp}",
                "# Auto-generated by AXI4 Bus Matrix Configuration GUI",
                "#==============================================================================",
                "",
                "set -e  # Exit on error",
                "",
                f"# Configuration",
                f'UVM_SIM_PATH="{uvm_sim_path}"',
                f'CONFIG_NAME="{self.bus_config.bus_type.lower()}_config_{self.export_timestamp}"',
                f'CONFIG_JSON="$UVM_SIM_PATH/output/configs/$CONFIG_NAME.json"',
                "",
                "# Colors for output",
                'RED="\\033[0;31m"',
                'GREEN="\\033[0;32m"',
                'YELLOW="\\033[1;33m"',
                'BLUE="\\033[0;34m"',
                'NC="\\033[0m" # No Color',
                "",
                "print_msg() {",
                '    echo -e "${1}[GUI_TEST] ${2}${NC}"',
                "}",
                "",
                'print_msg $BLUE "Starting AXI4 VIP test with GUI configuration"',
                f'print_msg $BLUE "Bus Type: {self.bus_config.bus_type}"',
                f'print_msg $BLUE "Masters: {len(self.bus_config.masters)}, Slaves: {len(self.bus_config.slaves)}"',
                f'print_msg $BLUE "Data Width: {self.bus_config.data_width} bits"',
                "",
                "# Change to UVM simulation directory",
                'cd "$UVM_SIM_PATH" || {',
                '    print_msg $RED "Failed to change to UVM simulation directory"',
                '    exit 1',
                '}',
                "",
                '# Create output directories',
                'mkdir -p output/configs',
                'mkdir -p output/logs',
                'mkdir -p output/reports',
                "",
                'print_msg $YELLOW "Running AXI4 VIP simulation..."',
                "",
                "# Run basic test",
                'print_msg $BLUE "Phase 1: Basic Test"',
                f'make run TEST=axi4_basic_test CONFIG_FILE="$CONFIG_JSON" || {{',
                '    print_msg $RED "Basic test failed"',
                '    exit 1',
                '}',
                "",
                "# Run comprehensive test if basic passes",
                'print_msg $BLUE "Phase 2: Comprehensive Test"',
                f'make run TEST=axi4_comprehensive_test CONFIG_FILE="$CONFIG_JSON" || {{',
                '    print_msg $RED "Comprehensive test failed"',
                '    exit 1',
                '}',
                "",
                "# Generate reports",
                'print_msg $BLUE "Generating reports..."',
                'make coverage 2>/dev/null || true',
                "",
                f'print_msg $GREEN "[OK] AXI4 VIP tests completed successfully!"',
                f'print_msg $BLUE "Check results in: $UVM_SIM_PATH/output/"',
                ""
            ]
            
            # Write script file
            os.makedirs(os.path.dirname(output_path), exist_ok=True)
            with open(output_path, 'w') as f:
                f.write('\n'.join(script_content))
            
            # Make script executable
            os.chmod(output_path, 0o755)
            
            print(f"[OK] Test script exported to: {output_path}")
            return True
            
        except Exception as e:
            print(f"[ERROR] Failed to export test script: {e}")
            return False
    
    def export_summary_report(self, output_path: str) -> bool:
        """Export a human-readable configuration summary"""
        try:
            summary_lines = [
                "================================================================================",
                f"AXI4 Bus Matrix Configuration Summary",
                f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
                f"Source: AXI4 Bus Matrix Configuration GUI",
                "================================================================================",
                "",
                "[BUS] Bus Configuration:",
                f"  • Bus Type: {self.bus_config.bus_type}",
                f"  • Address Width: {self.bus_config.addr_width} bits",
                f"  • Data Width: {self.bus_config.data_width} bits", 
                f"  • Arbitration: {self.bus_config.arbitration}",
                "",
                "[TEST] VIP Configuration:",
                f"  • VIP Mode: {self.vip_mode}",
                f"  • RTL Path: {self.rtl_path if self.rtl_path else 'N/A (Behavioral Mode)'}",
                "",
                f"[MASTERS] Masters ({len(self.bus_config.masters)}):",
            ]
            
            for i, master in enumerate(self.bus_config.masters):
                priority = getattr(master, 'priority', 0)
                summary_lines.extend([
                    f"  [{i}] {master.name}",
                    f"      Priority: {priority}",
                    f"      QoS Support: {getattr(master, 'qos_support', True)}",
                    f"      Exclusive Access: {getattr(master, 'exclusive_support', True)}",
                    ""
                ])
            
            summary_lines.extend([
                f"[SLAVES] Slaves ({len(self.bus_config.slaves)}):",
            ])
            
            total_memory = 0
            for i, slave in enumerate(self.bus_config.slaves):
                memory_mb = slave.size // 1024
                total_memory += slave.size
                summary_lines.extend([
                    f"  [{i}] {slave.name}",
                    f"      Address: 0x{slave.base_address:08X} - 0x{slave.get_end_address():08X}",
                    f"      Size: {slave.size} KB ({memory_mb} MB)" if memory_mb > 0 else f"      Size: {slave.size} KB",
                    f"      Type: {getattr(slave, 'memory_type', 'Memory')}",
                    ""
                ])
            
            summary_lines.extend([
                f"[STATS] Statistics:",
                f"  • Total Memory: {total_memory} KB ({total_memory // 1024} MB)",
                f"  • Address Space Utilization: {len(self.bus_config.slaves)} regions",
                f"  • Masters per Slave Ratio: {len(self.bus_config.masters)}/{len(self.bus_config.slaves)}",
                "",
                "[CONFIG] UVM Simulation Commands:",
                "  Basic Test:",
                f"    make run TEST=axi4_basic_test CONFIG_FILE=<config.json>",
                "  Comprehensive Test:", 
                f"    make run TEST=axi4_comprehensive_test CONFIG_FILE=<config.json>",
                "  With Coverage:",
                f"    make run TEST=axi4_comprehensive_test CONFIG_FILE=<config.json> COVERAGE=1",
                "",
                "[DIR] Output Files:",
                "  • Logs: output/logs/",
                "  • Waveforms: output/waves/", 
                "  • Coverage: output/coverage/",
                "  • Reports: output/reports/",
                "",
                "================================================================================",
                f"Configuration ready for UVM simulation!",
                "Use the exported JSON file with: +CONFIG_FILE=<path_to_json>",
                "================================================================================"
            ])
            
            # Write summary file
            os.makedirs(os.path.dirname(output_path), exist_ok=True)
            with open(output_path, 'w') as f:
                f.write('\n'.join(summary_lines))
            
            print(f"[OK] Configuration summary exported to: {output_path}")
            return True
            
        except Exception as e:
            print(f"[ERROR] Failed to export summary report: {e}")
            return False
    
    def export_all(self, base_output_dir: str) -> Dict[str, str]:
        """Export all configuration formats"""
        
        config_name = f"{self.bus_config.bus_type.lower()}_config_{self.export_timestamp}"
        
        # Create output directory structure
        output_paths = {
            'json': os.path.join(base_output_dir, 'configs', f'{config_name}.json'),
            'makefile': os.path.join(base_output_dir, 'configs', f'{config_name}.mk'),
            'script': os.path.join(base_output_dir, 'scripts', f'run_{config_name}.sh'),
            'summary': os.path.join(base_output_dir, 'reports', f'{config_name}_summary.txt')
        }
        
        results = {}
        
        print(f"[START] Exporting AXI4 VIP configuration: {config_name}")
        print(f"[DIR] Base output directory: {base_output_dir}")
        
        # Export each format
        results['json'] = self.export_json_config(output_paths['json'])
        results['makefile'] = self.export_makefile_args(output_paths['makefile'])
        results['script'] = self.export_test_script(output_paths['script'])
        results['summary'] = self.export_summary_report(output_paths['summary'])
        
        # Print summary
        successful_exports = sum(results.values())
        total_exports = len(results)
        
        print(f"\n[STATS] Export Summary: {successful_exports}/{total_exports} successful")
        
        if successful_exports == total_exports:
            print(f"[OK] All configuration files exported successfully!")
            print(f"\n[CONFIG] Next steps:")
            print(f"1. cd ../axi4_vip_sim")
            print(f"2. ./scripts/run_sim.sh -t axi4_basic_test")
            print(f"3. Or use: make run TEST=axi4_basic_test CONFIG_FILE={output_paths['json']}")
        else:
            print(f"[WARNING] Some exports failed. Check error messages above.")
        
        return output_paths


def export_gui_config_to_uvm(bus_config, vip_mode="BEHAVIORAL", rtl_path=None, output_dir: str = None) -> Dict[str, str]:
    """
    Convenience function to export GUI configuration for UVM simulation
    
    Args:
        bus_config: GUI BusConfig object
        output_dir: Output directory (defaults to ../axi4_vip_sim/output)
    
    Returns:
        Dict with paths to exported files
    """
    
    if output_dir is None:
        # Default to UVM simulation output directory
        current_dir = os.path.dirname(os.path.abspath(__file__))
        output_dir = os.path.join(current_dir, "..", "..", "..", "axi4_vip_sim", "output")
    
    exporter = UVMConfigExporter(bus_config, vip_mode, rtl_path)
    return exporter.export_all(output_dir)


if __name__ == "__main__":
    print("UVM Configuration Exporter")
    print("This module should be imported and used with GUI bus configuration")
    print("Example usage:")
    print("  from uvm_config_exporter import export_gui_config_to_uvm")
    print("  paths = export_gui_config_to_uvm(gui_bus_config)")