#!/usr/bin/env python3
"""
Demo: Bus Matrix Reference Model Generation
Shows how the GUI generates reference model 100% consistent with settings
"""

import os
import sys
import json
import tkinter as tk
from tkinter import ttk, messagebox

# Add src directory to path
sys.path.append(os.path.join(os.path.dirname(__file__), 'src'))

from vip_gui_reference_model_integration import VIPGUIReferenceModelIntegration, ReferenceModelGUIPanel

class DemoGUI:
    """Simple demo GUI showing reference model generation"""
    
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("AXI4 Bus Matrix Reference Model Demo")
        self.root.geometry("800x600")
        
        # GUI configuration - this is the single source of truth
        self.num_masters = 4
        self.num_slaves = 4
        self.data_width = 128
        self.addr_width = 64
        self.id_width = 8
        self.user_width = 32
        
        # Features
        self.qos_enable = True
        self.region_enable = True
        self.exclusive_enable = True
        self.user_enable = True
        self.axi3_mode = False
        
        # Arbitration
        self.arbitration_scheme = "round_robin"
        self.qos_scheme = "weighted"
        self.id_map_bits = 2
        
        # Module name
        self.module_name = "axi4_interconnect"
        
        # Output directory
        self.output_directory = "demo_output"
        
        # Create GUI
        self._create_gui()
        
    def _create_gui(self):
        """Create demo GUI"""
        
        # Title
        title_label = ttk.Label(self.root, text="Bus Matrix Reference Model Demo", 
                              font=("Arial", 16, "bold"))
        title_label.pack(pady=10)
        
        # Configuration display
        config_frame = ttk.LabelFrame(self.root, text="Current Bus Configuration")
        config_frame.pack(fill=tk.X, padx=20, pady=10)
        
        config_text = f"""Masters: {self.num_masters}
Slaves: {self.num_slaves}
Data Width: {self.data_width} bits
Address Width: {self.addr_width} bits
ID Width: {self.id_width} bits
USER Width: {self.user_width} bits

Features:
- QoS: {'Enabled' if self.qos_enable else 'Disabled'}
- REGION: {'Enabled' if self.region_enable else 'Disabled'}
- Exclusive Access: {'Enabled' if self.exclusive_enable else 'Disabled'}
- USER Signals: {'Enabled' if self.user_enable else 'Disabled'}
- AXI3 Mode: {'Yes' if self.axi3_mode else 'No'}

Arbitration: {self.arbitration_scheme}
"""
        
        config_label = ttk.Label(config_frame, text=config_text, justify=tk.LEFT)
        config_label.pack(padx=10, pady=10)
        
        # Create reference model integration
        self.ref_model_integration = VIPGUIReferenceModelIntegration(self)
        
        # Add reference model panel
        ref_frame = ttk.Frame(self.root)
        ref_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        self.ref_panel = ReferenceModelGUIPanel(ref_frame, self.ref_model_integration)
        
        # Demo button
        demo_button = ttk.Button(self.root, text="Run Full Demo", 
                               command=self._run_demo, style="Accent.TButton")
        demo_button.pack(pady=20)
        
    def get_slave_config(self, slave_id):
        """Get slave configuration for memory map"""
        
        # Demo memory map - aligned with 64-bit address space
        slave_configs = [
            {
                'name': 'ddr0',
                'base_addr': 0x0000000000000000,
                'size': 0x0000000100000000,  # 4GB
                'type': 'memory',
                'access': 'read_write',
                'secure': False,
                'cacheable': True,
                'executable': True
            },
            {
                'name': 'ddr1', 
                'base_addr': 0x0000000100000000,
                'size': 0x0000000100000000,  # 4GB
                'type': 'memory',
                'access': 'read_write',
                'secure': False,
                'cacheable': True,
                'executable': True
            },
            {
                'name': 'sram',
                'base_addr': 0x0000000200000000,
                'size': 0x0000000080000000,  # 2GB
                'type': 'memory',
                'access': 'read_write',
                'secure': True,
                'cacheable': True,
                'executable': False
            },
            {
                'name': 'periph',
                'base_addr': 0x0000000280000000,
                'size': 0x0000000080000000,  # 2GB
                'type': 'peripheral',
                'access': 'read_write',
                'secure': False,
                'cacheable': False,
                'executable': False
            }
        ]
        
        if slave_id < len(slave_configs):
            return slave_configs[slave_id]
        else:
            # Default for any additional slaves
            return {
                'name': f'slave_{slave_id}',
                'base_addr': 0x0000000300000000 + (slave_id * 0x10000000),
                'size': 0x10000000,
                'type': 'memory',
                'access': 'read_write',
                'secure': False,
                'cacheable': True,
                'executable': False
            }
            
    def _run_demo(self):
        """Run full demonstration"""
        
        messagebox.showinfo("Demo", 
            "This demo will:\n"
            "1. Extract configuration from GUI\n"
            "2. Generate reference model\n"
            "3. Create verification testbench\n"
            "4. Show configuration report")
        
        # Create output directory
        os.makedirs(self.output_directory, exist_ok=True)
        
        # Extract configuration
        self.ref_panel._extract_config()
        
        # Generate reference model
        self.ref_panel._generate_model()
        
        # Show results
        report_file = os.path.join(self.output_directory, "reference_model", "configuration_report.txt")
        if os.path.exists(report_file):
            with open(report_file, 'r') as f:
                report_content = f.read()
                
            # Create popup to show report
            popup = tk.Toplevel(self.root)
            popup.title("Configuration Report")
            popup.geometry("600x500")
            
            text = tk.Text(popup, wrap=tk.WORD)
            text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
            text.insert(tk.END, report_content)
            text.config(state=tk.DISABLED)
            
            ttk.Button(popup, text="Close", command=popup.destroy).pack(pady=5)

def main():
    """Run demo"""
    
    print("Starting Bus Matrix Reference Model Demo...")
    print("This demonstrates how the GUI generates a reference model")
    print("that is 100% consistent with the GUI settings.")
    print()
    
    demo = DemoGUI()
    demo.root.mainloop()
    
    print("\nDemo complete!")
    print("Check the 'demo_output' directory for generated files:")
    print("- reference_model/gui_configuration.json - Configuration from GUI")
    print("- reference_model/reference_model_config.json - Reference model config")
    print("- reference_model/*.sv - SystemVerilog reference model components")
    print("- reference_model/configuration_report.txt - Human-readable report")

if __name__ == "__main__":
    main()