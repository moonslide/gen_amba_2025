#!/usr/bin/env python3
"""
VIP GUI Reference Model Integration
Ensures 100% consistency between GUI settings and reference model
Integrates reference model generation with GUI bus matrix configuration
"""

import os
import json
import tkinter as tk
from tkinter import ttk, messagebox
from datetime import datetime
from typing import Dict, List, Optional, Any
import logging

from vip_bus_matrix_reference_model import VIPBusMatrixReferenceModel

class VIPGUIReferenceModelIntegration:
    """Integrate reference model generation with GUI configuration"""
    
    def __init__(self, gui_instance):
        self.gui = gui_instance
        self.logger = self._setup_logging()
        
        # Configuration synchronization
        self.current_config = None
        self.config_hash = None
        
    def _setup_logging(self) -> logging.Logger:
        """Setup logging"""
        logger = logging.getLogger('VIPRefModelIntegration')
        logger.setLevel(logging.INFO)
        
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            
        return logger
        
    def extract_gui_configuration(self) -> Dict[str, Any]:
        """Extract complete configuration from GUI - this is the single source of truth"""
        
        config = {}
        
        # Basic bus configuration
        config['num_masters'] = self.gui.num_masters
        config['num_slaves'] = self.gui.num_slaves
        config['data_width'] = self.gui.data_width
        config['addr_width'] = self.gui.addr_width
        config['id_width'] = self.gui.id_width
        config['user_width'] = self.gui.user_width
        
        # Memory map - critical for consistency
        config['memory_map'] = self._extract_memory_map()
        
        # Features and options
        config['support_qos'] = self.gui.qos_enable
        config['support_region'] = self.gui.region_enable
        config['support_exclusive'] = self.gui.exclusive_enable
        config['support_user'] = self.gui.user_enable
        config['support_axi3'] = self.gui.axi3_mode
        
        # Arbitration configuration
        config['arbitration_scheme'] = self.gui.arbitration_scheme
        config['qos_enable'] = self.gui.qos_enable
        config['qos_scheme'] = self.gui.qos_scheme if hasattr(self.gui, 'qos_scheme') else 'weighted'
        
        # ID mapping configuration
        config['id_map_bits'] = self.gui.id_map_bits if hasattr(self.gui, 'id_map_bits') else None
        
        # Outstanding transaction limits
        config['max_outstanding_per_master'] = self.gui.max_outstanding_per_master if hasattr(self.gui, 'max_outstanding_per_master') else 16
        config['max_outstanding_per_route'] = 16
        
        # Cache configuration
        config['cache_line_size'] = 64
        config['support_ace_lite'] = self.gui.ace_lite_enable if hasattr(self.gui, 'ace_lite_enable') else False
        
        # Exclusive monitor configuration
        config['exclusive_monitor_per_slave'] = True
        config['exclusive_timeout_cycles'] = 1000
        
        # Timestamp for tracking
        config['generation_timestamp'] = datetime.now().isoformat()
        
        # Calculate configuration hash for verification
        self.config_hash = self._calculate_config_hash(config)
        config['config_hash'] = self.config_hash
        
        self.current_config = config
        return config
        
    def _extract_memory_map(self) -> List[Dict[str, Any]]:
        """Extract memory map from GUI slave configuration"""
        
        memory_map = []
        
        # Get slave configurations from GUI
        for i in range(self.gui.num_slaves):
            slave_config = self.gui.get_slave_config(i)
            
            # Ensure consistent format
            slave_entry = {
                'slave_id': i,
                'name': slave_config.get('name', f'slave_{i}'),
                'base_addr': int(slave_config.get('base_addr', 0)),
                'size': int(slave_config.get('size', 0x10000000)),  # Default 256MB
                'end_addr': 0,  # Will be calculated
                'type': slave_config.get('type', 'memory'),
                'access': slave_config.get('access', 'read_write'),
                'secure': slave_config.get('secure', False),
                'cacheable': slave_config.get('cacheable', True),
                'executable': slave_config.get('executable', False)
            }
            
            # Calculate end address
            slave_entry['end_addr'] = slave_entry['base_addr'] + slave_entry['size'] - 1
            
            memory_map.append(slave_entry)
            
        # Validate memory map
        self._validate_memory_map(memory_map)
        
        return memory_map
        
    def _validate_memory_map(self, memory_map: List[Dict[str, Any]]):
        """Validate memory map for overlaps and gaps"""
        
        # Sort by base address
        sorted_map = sorted(memory_map, key=lambda x: x['base_addr'])
        
        # Check for overlaps
        for i in range(len(sorted_map) - 1):
            if sorted_map[i]['end_addr'] >= sorted_map[i+1]['base_addr']:
                self.logger.warning(f"Memory overlap detected between slave {sorted_map[i]['slave_id']} and {sorted_map[i+1]['slave_id']}")
                
        # Check for gaps (optional warning)
        total_coverage = sum(entry['size'] for entry in memory_map)
        address_space = 2 ** self.gui.addr_width
        
        if total_coverage < address_space * 0.5:
            self.logger.info(f"Memory map covers {total_coverage/address_space*100:.1f}% of address space")
            
    def _calculate_config_hash(self, config: Dict[str, Any]) -> str:
        """Calculate hash of configuration for verification"""
        
        import hashlib
        
        # Create deterministic string representation
        config_str = json.dumps(config, sort_keys=True, default=str)
        
        # Calculate SHA256 hash
        return hashlib.sha256(config_str.encode()).hexdigest()[:16]
        
    def generate_reference_model(self, output_dir: str) -> bool:
        """Generate reference model with current GUI configuration"""
        
        try:
            # Extract configuration
            config = self.extract_gui_configuration()
            
            # Log configuration
            self.logger.info(f"Generating reference model with configuration hash: {config['config_hash']}")
            
            # Create reference model generator
            ref_model_gen = VIPBusMatrixReferenceModel(config)
            
            # Generate reference model
            success = ref_model_gen.generate_reference_model(output_dir)
            
            if success:
                # Save configuration for verification
                self._save_configuration_file(output_dir, config)
                
                # Generate configuration report
                self._generate_configuration_report(output_dir, config)
                
                self.logger.info(f"Reference model generated successfully in {output_dir}")
                
            return success
            
        except Exception as e:
            self.logger.error(f"Error generating reference model: {str(e)}")
            return False
            
    def _save_configuration_file(self, output_dir: str, config: Dict[str, Any]):
        """Save configuration file for verification"""
        
        config_file = os.path.join(output_dir, "gui_configuration.json")
        
        with open(config_file, 'w') as f:
            json.dump(config, f, indent=2, default=str)
            
        self.logger.info(f"Configuration saved to {config_file}")
        
    def _generate_configuration_report(self, output_dir: str, config: Dict[str, Any]):
        """Generate human-readable configuration report"""
        
        report_file = os.path.join(output_dir, "configuration_report.txt")
        
        with open(report_file, 'w') as f:
            f.write("Bus Matrix Configuration Report\n")
            f.write("=" * 60 + "\n\n")
            f.write(f"Generated: {config['generation_timestamp']}\n")
            f.write(f"Configuration Hash: {config['config_hash']}\n\n")
            
            f.write("Bus Configuration:\n")
            f.write(f"  Masters: {config['num_masters']}\n")
            f.write(f"  Slaves: {config['num_slaves']}\n")
            f.write(f"  Data Width: {config['data_width']} bits\n")
            f.write(f"  Address Width: {config['addr_width']} bits\n")
            f.write(f"  ID Width: {config['id_width']} bits\n")
            f.write(f"  User Width: {config['user_width']} bits\n\n")
            
            f.write("Memory Map:\n")
            for slave in config['memory_map']:
                f.write(f"  Slave[{slave['slave_id']}] - {slave['name']}:\n")
                f.write(f"    Base Address: 0x{slave['base_addr']:016X}\n")
                f.write(f"    End Address:  0x{slave['end_addr']:016X}\n")
                f.write(f"    Size: {slave['size'] / (1024*1024):.1f} MB\n")
                f.write(f"    Type: {slave['type']}\n")
                f.write(f"    Access: {slave['access']}\n")
                f.write(f"    Cacheable: {slave['cacheable']}\n\n")
                
            f.write("Features:\n")
            f.write(f"  QoS Support: {config['support_qos']}\n")
            f.write(f"  REGION Support: {config['support_region']}\n")
            f.write(f"  Exclusive Access: {config['support_exclusive']}\n")
            f.write(f"  USER Signals: {config['support_user']}\n")
            f.write(f"  AXI3 Mode: {config['support_axi3']}\n")
            f.write(f"  ACE-Lite: {config.get('support_ace_lite', False)}\n\n")
            
            f.write("Arbitration:\n")
            f.write(f"  Scheme: {config['arbitration_scheme']}\n")
            f.write(f"  QoS Enabled: {config['qos_enable']}\n")
            f.write(f"  QoS Scheme: {config.get('qos_scheme', 'N/A')}\n\n")
            
            f.write("Performance:\n")
            f.write(f"  Max Outstanding per Master: {config['max_outstanding_per_master']}\n")
            f.write(f"  Max Outstanding per Route: {config['max_outstanding_per_route']}\n\n")
            
            f.write("This configuration is used for both RTL generation and reference model.\n")
            f.write("The reference model will predict behavior based on these exact parameters.\n")
            
    def verify_rtl_configuration_match(self, rtl_config_file: str) -> bool:
        """Verify that RTL configuration matches reference model"""
        
        try:
            # Load RTL configuration
            with open(rtl_config_file, 'r') as f:
                rtl_config = json.load(f)
                
            # Compare with current configuration
            if rtl_config.get('config_hash') != self.config_hash:
                self.logger.error("Configuration mismatch detected!")
                self.logger.error(f"GUI hash: {self.config_hash}")
                self.logger.error(f"RTL hash: {rtl_config.get('config_hash')}")
                
                # Find differences
                self._report_config_differences(self.current_config, rtl_config)
                
                return False
                
            self.logger.info("Configuration verification passed - RTL and reference model match")
            return True
            
        except Exception as e:
            self.logger.error(f"Error verifying configuration: {str(e)}")
            return False
            
    def _report_config_differences(self, config1: Dict, config2: Dict):
        """Report differences between configurations"""
        
        def compare_dicts(d1, d2, path=""):
            for key in set(d1.keys()) | set(d2.keys()):
                if key not in d1:
                    self.logger.warning(f"{path}.{key}: Missing in GUI config")
                elif key not in d2:
                    self.logger.warning(f"{path}.{key}: Missing in RTL config")
                elif isinstance(d1[key], dict) and isinstance(d2[key], dict):
                    compare_dicts(d1[key], d2[key], f"{path}.{key}")
                elif d1[key] != d2[key]:
                    self.logger.warning(f"{path}.{key}: GUI={d1[key]}, RTL={d2[key]}")
                    
        compare_dicts(config1, config2)
        
    def create_reference_model_testbench(self, output_dir: str) -> bool:
        """Create testbench that instantiates reference model with GUI configuration"""
        
        config = self.current_config
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Reference Model Testbench
// Generated: {datetime.now()}
// Configuration Hash: {config['config_hash']}
// Description: Testbench with reference model using GUI configuration
//------------------------------------------------------------------------------

module axi4_reference_model_tb;
    
    // Import UVM package
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Import test packages
    import axi4_test_pkg::*;
    import axi4_vip_pkg::*;
    
    // Clock and reset
    logic aclk;
    logic aresetn;
    
    // Clock generation
    initial begin
        aclk = 0;
        forever #5 aclk = ~aclk;
    end
    
    // Reset generation
    initial begin
        aresetn = 0;
        repeat(10) @(posedge aclk);
        aresetn = 1;
    end
    
    // Instantiate DUT interfaces
    axi4_if master_if[{config['num_masters']}](aclk, aresetn);
    axi4_if slave_if[{config['num_slaves']}](aclk, aresetn);
    
    // DUT instance
    {self.gui.module_name} dut (
        .aclk(aclk),
        .aresetn(aresetn)
'''
        
        # Add master interfaces
        for i in range(config['num_masters']):
            content += f'''        // Master {i} connections
        ,.m{i}_axi_if(master_if[{i}])
'''
        
        # Add slave interfaces
        for i in range(config['num_slaves']):
            content += f'''        // Slave {i} connections
        ,.s{i}_axi_if(slave_if[{i}])
'''
            
        content += '''    );
    
    // Test harness
    initial begin
        // Set configuration in config DB - MUST match GUI
        axi4_vip_config cfg;
        axi4_bus_config bus_cfg;
        
        cfg = axi4_vip_config::type_id::create("cfg");
        bus_cfg = axi4_bus_config::type_id::create("bus_cfg");
        
        // Set bus configuration from GUI
'''
        
        # Add configuration settings
        content += f'''        bus_cfg.num_masters = {config['num_masters']};
        bus_cfg.num_slaves = {config['num_slaves']};
        bus_cfg.data_width = {config['data_width']};
        bus_cfg.addr_width = {config['addr_width']};
        bus_cfg.id_width = {config['id_width']};
        bus_cfg.user_width = {config['user_width']};
        
        // Set memory map from GUI
'''
        
        # Add memory map
        for slave in config['memory_map']:
            content += f'''        bus_cfg.add_slave_region({slave['slave_id']}, 
                                {slave['base_addr']:#x}, 
                                {slave['end_addr']:#x}, 
                                "{slave['name']}");
'''
            
        content += '''        
        // Store configuration
        uvm_config_db#(axi4_vip_config)::set(null, "*", "axi4_vip_config", cfg);
        uvm_config_db#(axi4_bus_config)::set(null, "*", "axi4_bus_config", bus_cfg);
        
        // Set interface handles
'''
        
        # Set interface handles
        for i in range(config['num_masters']):
            content += f'''        uvm_config_db#(virtual axi4_if)::set(null, "*.master_agent[{i}]*", "vif", master_if[{i}]);
'''
            
        for i in range(config['num_slaves']):
            content += f'''        uvm_config_db#(virtual axi4_if)::set(null, "*.slave_agent[{i}]*", "vif", slave_if[{i}]);
'''
            
        content += '''        
        // Create and configure reference model
        axi4_bus_matrix_model ref_model;
        ref_model = axi4_bus_matrix_model::type_id::create("ref_model", null);
        
        // Verify configuration matches
        if (!ref_model.verify_configuration(bus_cfg)) begin
            $fatal("Reference model configuration mismatch!");
        end
        
        // Store reference model in config DB
        uvm_config_db#(axi4_bus_matrix_model)::set(null, "*", "matrix_model", ref_model);
        
        // Run test
        run_test();
    end
    
    // Dump waves
    initial begin
        $dumpfile("reference_model_tb.vcd");
        $dumpvars(0, axi4_reference_model_tb);
    end
    
endmodule
'''
        
        filepath = os.path.join(output_dir, "axi4_reference_model_tb.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
        return True

class ReferenceModelGUIPanel:
    """GUI panel for reference model configuration and generation"""
    
    def __init__(self, parent_frame, gui_integration):
        self.parent = parent_frame
        self.integration = gui_integration
        
        self._create_panel()
        
    def _create_panel(self):
        """Create reference model panel"""
        
        # Main frame
        main_frame = ttk.LabelFrame(self.parent, text="Reference Model Configuration")
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # Configuration display
        config_frame = ttk.Frame(main_frame)
        config_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(config_frame, text="Current Configuration:").grid(row=0, column=0, sticky="w", padx=5)
        self.config_label = ttk.Label(config_frame, text="Not extracted", foreground="gray")
        self.config_label.grid(row=0, column=1, sticky="w", padx=5)
        
        ttk.Label(config_frame, text="Configuration Hash:").grid(row=1, column=0, sticky="w", padx=5)
        self.hash_label = ttk.Label(config_frame, text="N/A", font=("Courier", 10))
        self.hash_label.grid(row=1, column=1, sticky="w", padx=5)
        
        # Control buttons
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(fill=tk.X, padx=5, pady=10)
        
        ttk.Button(button_frame, text="Extract Configuration", 
                  command=self._extract_config).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(button_frame, text="Generate Reference Model", 
                  command=self._generate_model).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(button_frame, text="Verify RTL Match", 
                  command=self._verify_match).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(button_frame, text="View Configuration", 
                  command=self._view_config).pack(side=tk.LEFT, padx=5)
        
        # Status frame
        status_frame = ttk.LabelFrame(main_frame, text="Generation Status")
        status_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        self.status_text = tk.Text(status_frame, height=10, width=60)
        self.status_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Add scrollbar
        scrollbar = ttk.Scrollbar(status_frame, command=self.status_text.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.status_text.config(yscrollcommand=scrollbar.set)
        
    def _extract_config(self):
        """Extract configuration from GUI"""
        
        try:
            config = self.integration.extract_gui_configuration()
            
            self.config_label.config(text=f"{config['num_masters']}x{config['num_slaves']} matrix", 
                                   foreground="black")
            self.hash_label.config(text=config['config_hash'])
            
            self._log_status("Configuration extracted successfully")
            self._log_status(f"Hash: {config['config_hash']}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to extract configuration: {str(e)}")
            
    def _generate_model(self):
        """Generate reference model"""
        
        try:
            output_dir = self.integration.gui.output_directory
            ref_model_dir = os.path.join(output_dir, "reference_model")
            
            self._log_status(f"Generating reference model in {ref_model_dir}...")
            
            success = self.integration.generate_reference_model(ref_model_dir)
            
            if success:
                self._log_status("✓ Reference model generated successfully")
                self._log_status(f"✓ Configuration saved to {ref_model_dir}/gui_configuration.json")
                self._log_status(f"✓ Report saved to {ref_model_dir}/configuration_report.txt")
                
                # Also generate testbench
                self.integration.create_reference_model_testbench(ref_model_dir)
                self._log_status(f"✓ Testbench saved to {ref_model_dir}/axi4_reference_model_tb.sv")
                
                messagebox.showinfo("Success", "Reference model generated successfully!")
            else:
                messagebox.showerror("Error", "Failed to generate reference model")
                
        except Exception as e:
            messagebox.showerror("Error", f"Generation failed: {str(e)}")
            
    def _verify_match(self):
        """Verify RTL configuration matches"""
        
        try:
            from tkinter import filedialog
            
            rtl_config = filedialog.askopenfilename(
                title="Select RTL configuration file",
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
            )
            
            if rtl_config:
                match = self.integration.verify_rtl_configuration_match(rtl_config)
                
                if match:
                    self._log_status("✓ Configuration verification PASSED")
                    messagebox.showinfo("Success", "RTL and reference model configurations match!")
                else:
                    self._log_status("✗ Configuration verification FAILED")
                    messagebox.showerror("Error", "Configuration mismatch detected! Check log for details.")
                    
        except Exception as e:
            messagebox.showerror("Error", f"Verification failed: {str(e)}")
            
    def _view_config(self):
        """View current configuration"""
        
        if self.integration.current_config:
            # Create popup window
            popup = tk.Toplevel(self.parent)
            popup.title("Current Configuration")
            popup.geometry("600x500")
            
            # Text widget
            text = tk.Text(popup, wrap=tk.WORD)
            text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
            
            # Add scrollbar
            scrollbar = ttk.Scrollbar(popup, command=text.yview)
            scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
            text.config(yscrollcommand=scrollbar.set)
            
            # Insert configuration
            text.insert(tk.END, json.dumps(self.integration.current_config, indent=2, default=str))
            text.config(state=tk.DISABLED)
            
            # Close button
            ttk.Button(popup, text="Close", command=popup.destroy).pack(pady=5)
            
        else:
            messagebox.showinfo("No Configuration", "Please extract configuration first")
            
    def _log_status(self, message: str):
        """Log status message"""
        
        timestamp = datetime.now().strftime("%H:%M:%S")
        self.status_text.insert(tk.END, f"[{timestamp}] {message}\n")
        self.status_text.see(tk.END)

def integrate_reference_model_with_gui(gui_instance):
    """Integrate reference model generation with existing GUI"""
    
    # Create integration instance
    integration = VIPGUIReferenceModelIntegration(gui_instance)
    
    # Add reference model tab to GUI
    if hasattr(gui_instance, 'notebook'):
        ref_model_frame = ttk.Frame(gui_instance.notebook)
        gui_instance.notebook.add(ref_model_frame, text="Reference Model")
        
        # Create panel
        panel = ReferenceModelGUIPanel(ref_model_frame, integration)
        
    return integration

# Example usage
if __name__ == "__main__":
    # This would be called from the main GUI
    print("Reference model integration module loaded")
    print("Use integrate_reference_model_with_gui() to add to existing GUI")