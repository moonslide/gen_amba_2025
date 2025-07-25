#!/usr/bin/env python3
"""
VIP GUI Integration Module
Integrates AXI4 Verification IP components with the Bus Matrix GUI
Based on CLAUDE.md requirements for GUI development
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import json
import threading
import queue
import time
import os
from typing import Dict, List, Optional, Any
from dataclasses import asdict

# Import with fallback for missing modules
try:
    from axi_vip_components import (
        AXIMasterAgent, AXISlaveAgent, AXIMonitor, AXIChecker,
        VIPConfig, AXITransaction, create_axi_vip_environment
    )
    from axi_test_sequences import (
        AXITestSequenceGenerator, TestScenarioConfig, 
        create_comprehensive_test_suite
    )
    # Force to False since these are just stub implementations
    # Set to True only when real VIP components are available
    VIP_COMPONENTS_AVAILABLE = False
except (ImportError, AttributeError):
    # VIP components not available - GUI will work without simulation features
    VIP_COMPONENTS_AVAILABLE = False
    # Define placeholder classes to avoid NameError
    VIPConfig = None
    create_axi_vip_environment = None
    AXIMasterAgent = None
    AXISlaveAgent = None
    AXIMonitor = None
    AXIChecker = None
    AXITransaction = None
    AXITestSequenceGenerator = None
    TestScenarioConfig = None
    create_comprehensive_test_suite = None
    
try:
    from uvm_config_exporter import export_gui_config_to_uvm
except ImportError:
    from .uvm_config_exporter import export_gui_config_to_uvm

class VIPControlPanel:
    """VIP Control Panel for the Bus Matrix GUI"""
    
    def __init__(self, parent_frame, gui_instance):
        self.parent = parent_frame
        self.gui = gui_instance
        self.vip_environment = None
        self.test_thread = None
        self.test_running = False
        self.test_results = {}
        
        # Initialize all UI variables
        self.env_status_label = None
        self.vip_mode_var = None
        self.rtl_path_var = None
        self.rtl_path_entry = None
        self.rtl_browse_btn = None
        
        try:
            self.setup_vip_panel()
        except Exception as e:
            print(f"[WARNING] VIP panel setup error: {e}")
            # Create minimal placeholder
            ttk.Label(parent_frame, text="VIP features unavailable").pack()
        
    def setup_vip_panel(self):
        """Setup VIP control panel UI"""
        # Create VIP notebook
        self.vip_notebook = ttk.Notebook(self.parent)
        self.vip_notebook.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # VIP Environment tab
        self.setup_environment_tab()
        
        # Test Generation tab
        self.setup_test_generation_tab()
        
        # Verification Results tab
        self.setup_results_tab()
        
        # Coverage Analysis tab
        self.setup_coverage_tab()
    
    def setup_environment_tab(self):
        """Setup UVM Configuration Export tab"""
        env_frame = ttk.Frame(self.vip_notebook)
        self.vip_notebook.add(env_frame, text="UVM Export")
        
        # Important notice
        notice_frame = ttk.LabelFrame(env_frame, text="Important Notice", padding=10)
        notice_frame.pack(fill=tk.X, padx=5, pady=5)
        
        notice_text = """[WARNING] UVM Simulation should be run via Makefile, not GUI!
        
The GUI exports configuration files that the SystemVerilog/UVM 
simulation environment can read. Use the exported files with:

  • cd ../axi4_vip_sim
  • make run TEST=axi4_basic_test CONFIG_FILE=<exported_json>
  • Or use the generated test script"""
        
        ttk.Label(notice_frame, text=notice_text, justify=tk.LEFT).pack(anchor=tk.W)
        
        # VIP Mode Selection
        mode_frame = ttk.LabelFrame(env_frame, text="VIP Mode Selection", padding=10)
        mode_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(mode_frame, text="VIP Verification Mode:").grid(row=0, column=0, sticky=tk.W, padx=5)
        
        self.vip_mode_var = tk.StringVar(value="BEHAVIORAL")
        ttk.Radiobutton(mode_frame, text="Behavioral Model (No RTL)", 
                       variable=self.vip_mode_var, value="BEHAVIORAL",
                       command=self.on_vip_mode_change).grid(row=0, column=1, padx=5)
        ttk.Radiobutton(mode_frame, text="RTL Integration (Generated RTL)", 
                       variable=self.vip_mode_var, value="RTL",
                       command=self.on_vip_mode_change).grid(row=0, column=2, padx=5)
        
        # RTL Path (enabled only in RTL mode)
        ttk.Label(mode_frame, text="RTL Path:").grid(row=1, column=0, sticky=tk.W, padx=5)
        self.rtl_path_var = tk.StringVar(value="")
        self.rtl_path_entry = ttk.Entry(mode_frame, textvariable=self.rtl_path_var, width=40, state=tk.DISABLED)
        self.rtl_path_entry.grid(row=1, column=1, columnspan=2, padx=5, pady=5)
        
        self.rtl_browse_btn = ttk.Button(mode_frame, text="Browse...", 
                                        command=self.browse_rtl_path, state=tk.DISABLED)
        self.rtl_browse_btn.grid(row=1, column=3, padx=5)
        
        # Output Directory Selection
        output_frame = ttk.LabelFrame(env_frame, text="Output Directories", padding=10)
        output_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # VIP Output Directory
        ttk.Label(output_frame, text="VIP Output Directory:").grid(row=0, column=0, sticky=tk.W, padx=5)
        self.vip_output_dir_var = tk.StringVar(value=os.path.abspath("../axi4_vip_sim/output"))
        self.vip_output_entry = ttk.Entry(output_frame, textvariable=self.vip_output_dir_var, width=50)
        self.vip_output_entry.grid(row=0, column=1, padx=5, pady=5)
        ttk.Button(output_frame, text="Browse...", 
                  command=self.browse_vip_output_dir).grid(row=0, column=2, padx=5)
        
        # Verilog/RTL Output Directory
        ttk.Label(output_frame, text="Verilog Output Directory:").grid(row=1, column=0, sticky=tk.W, padx=5)
        self.verilog_output_dir_var = tk.StringVar(value=os.path.abspath("output/rtl"))
        self.verilog_output_entry = ttk.Entry(output_frame, textvariable=self.verilog_output_dir_var, width=50)
        self.verilog_output_entry.grid(row=1, column=1, padx=5, pady=5)
        ttk.Button(output_frame, text="Browse...", 
                  command=self.browse_verilog_output_dir).grid(row=1, column=2, padx=5)
        
        # Create directories button
        ttk.Button(output_frame, text="Create Output Directories", 
                  command=self.create_output_directories).grid(row=2, column=0, columnspan=3, pady=10)
        
        # Export controls
        control_frame = ttk.LabelFrame(env_frame, text="Export Configuration for UVM", padding=10)
        control_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(control_frame, text="[FILE] Export UVM Config", 
                  command=self.export_uvm_configuration).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="[DIR] Open UVM Directory", 
                  command=self.open_uvm_directory).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="[LIST] Show Commands", 
                  command=self.show_uvm_commands).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="[CONFIG] Generate RTL First", 
                  command=self.generate_rtl_for_vip).pack(side=tk.LEFT, padx=5)
        
        # VIP Environment controls
        env_control_frame = ttk.Frame(env_frame)
        env_control_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(env_control_frame, text="Create VIP Environment", 
                  command=self.create_vip_environment).pack(side=tk.LEFT, padx=5)
        
        self.env_status_label = ttk.Label(env_control_frame, text="Environment: Not Created")
        self.env_status_label.pack(side=tk.LEFT, padx=10)
        
        # VIP Configuration
        config_frame = ttk.LabelFrame(env_frame, text="VIP Configuration", padding=10)
        config_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Configuration tree
        self.config_tree = ttk.Treeview(config_frame, columns=('Type', 'Config', 'Status'), show='tree headings')
        self.config_tree.heading('#0', text='Component')
        self.config_tree.heading('Type', text='Type')
        self.config_tree.heading('Config', text='Configuration')
        self.config_tree.heading('Status', text='Status')
        
        config_scroll = ttk.Scrollbar(config_frame, orient=tk.VERTICAL, command=self.config_tree.yview)
        self.config_tree.configure(yscrollcommand=config_scroll.set)
        
        self.config_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        config_scroll.pack(side=tk.RIGHT, fill=tk.Y)
    
    def setup_test_generation_tab(self):
        """Setup Test Generation tab"""
        test_frame = ttk.Frame(self.vip_notebook)
        self.vip_notebook.add(test_frame, text="Test Generation")
        
        # Test scenario selection
        scenario_frame = ttk.LabelFrame(test_frame, text="Test Scenarios", padding=10)
        scenario_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # Scenario checkboxes
        self.scenario_vars = {}
        scenarios = [
            ('basic', 'Basic Transactions (Single R/W, All Burst Types)'),
            ('advanced', 'Advanced Features (Out-of-order, Exclusive Access)'),
            ('error_injection', 'Error Injection (SLVERR, DECERR, Violations)'),
            ('stress', 'Stress Tests (High Throughput, Randomized)')
        ]
        
        for scenario_id, description in scenarios:
            var = tk.BooleanVar(value=True)
            self.scenario_vars[scenario_id] = var
            ttk.Checkbutton(scenario_frame, text=description, variable=var).pack(anchor=tk.W)
        
        # Test parameters
        params_frame = ttk.LabelFrame(test_frame, text="Test Parameters", padding=10)
        params_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # Number of transactions
        ttk.Label(params_frame, text="Transactions per Scenario:").grid(row=0, column=0, sticky=tk.W)
        self.num_transactions_var = tk.StringVar(value="100")
        ttk.Entry(params_frame, textvariable=self.num_transactions_var, width=10).grid(row=0, column=1, padx=5)
        
        # Address range
        ttk.Label(params_frame, text="Address Range:").grid(row=1, column=0, sticky=tk.W)
        self.addr_start_var = tk.StringVar(value="0x80000000")
        self.addr_end_var = tk.StringVar(value="0x8FFFFFFF")
        ttk.Entry(params_frame, textvariable=self.addr_start_var, width=12).grid(row=1, column=1, padx=5)
        ttk.Label(params_frame, text="to").grid(row=1, column=2)
        ttk.Entry(params_frame, textvariable=self.addr_end_var, width=12).grid(row=1, column=3, padx=5)
        
        # Test controls
        control_frame = ttk.LabelFrame(test_frame, text="Test Controls", padding=10)
        control_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(control_frame, text="Generate Test Suite", 
                  command=self.generate_test_suite).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Run Tests", 
                  command=self.run_tests).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Stop Tests", 
                  command=self.stop_tests).pack(side=tk.LEFT, padx=5)
        
        # Test progress
        progress_frame = ttk.LabelFrame(test_frame, text="Test Progress", padding=10)
        progress_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.test_progress = ttk.Progressbar(progress_frame, mode='determinate')
        self.test_progress.pack(fill=tk.X, pady=5)
        
        self.test_status_label = ttk.Label(progress_frame, text="Ready")
        self.test_status_label.pack(anchor=tk.W)
        
        # Generated tests summary
        summary_frame = ttk.LabelFrame(test_frame, text="Generated Tests Summary", padding=10)
        summary_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        self.test_summary_text = tk.Text(summary_frame, height=10, wrap=tk.WORD)
        summary_scroll = ttk.Scrollbar(summary_frame, orient=tk.VERTICAL, command=self.test_summary_text.yview)
        self.test_summary_text.configure(yscrollcommand=summary_scroll.set)
        
        self.test_summary_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        summary_scroll.pack(side=tk.RIGHT, fill=tk.Y)
    
    def setup_results_tab(self):
        """Setup Verification Results tab"""
        results_frame = ttk.Frame(self.vip_notebook)
        self.vip_notebook.add(results_frame, text="Results")
        
        # Results statistics
        stats_frame = ttk.LabelFrame(results_frame, text="Test Statistics", padding=10)
        stats_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # Statistics grid
        self.stats_labels = {}
        stats = [
            ('total_tests', 'Total Tests:'),
            ('passed_tests', 'Passed:'),
            ('failed_tests', 'Failed:'),
            ('protocol_violations', 'Protocol Violations:'),
            ('transactions_generated', 'Transactions Generated:'),
            ('responses_received', 'Responses Received:')
        ]
        
        for i, (key, label) in enumerate(stats):
            ttk.Label(stats_frame, text=label).grid(row=i//3, column=(i%3)*2, sticky=tk.W, padx=5)
            self.stats_labels[key] = ttk.Label(stats_frame, text="0", foreground="blue")
            self.stats_labels[key].grid(row=i//3, column=(i%3)*2+1, sticky=tk.W, padx=5)
        
        # Results details
        details_frame = ttk.LabelFrame(results_frame, text="Test Results Details", padding=10)
        details_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Results tree
        self.results_tree = ttk.Treeview(details_frame, columns=('Status', 'Transactions', 'Errors', 'Time'), show='tree headings')
        self.results_tree.heading('#0', text='Test Scenario')
        self.results_tree.heading('Status', text='Status')
        self.results_tree.heading('Transactions', text='Transactions')
        self.results_tree.heading('Errors', text='Errors')
        self.results_tree.heading('Time', text='Time (s)')
        
        results_scroll = ttk.Scrollbar(details_frame, orient=tk.VERTICAL, command=self.results_tree.yview)
        self.results_tree.configure(yscrollcommand=results_scroll.set)
        
        self.results_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        results_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Export results
        export_frame = ttk.Frame(results_frame)
        export_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(export_frame, text="Export Results", 
                  command=self.export_results).pack(side=tk.LEFT, padx=5)
        ttk.Button(export_frame, text="Generate Report", 
                  command=self.generate_report).pack(side=tk.LEFT, padx=5)
    
    def setup_coverage_tab(self):
        """Setup Coverage Analysis tab"""
        coverage_frame = ttk.Frame(self.vip_notebook)
        self.vip_notebook.add(coverage_frame, text="Coverage")
        
        # Coverage metrics
        metrics_frame = ttk.LabelFrame(coverage_frame, text="Coverage Metrics", padding=10)
        metrics_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # Coverage progress bars
        self.coverage_bars = {}
        coverage_types = [
            ('burst_types', 'Burst Types'),
            ('transfer_sizes', 'Transfer Sizes'),
            ('response_types', 'Response Types'),
            ('qos_levels', 'QoS Levels'),
            ('prot_variations', 'Protection Types'),
            ('cache_types', 'Cache Types')
        ]
        
        for i, (key, label) in enumerate(coverage_types):
            ttk.Label(metrics_frame, text=f"{label}:").grid(row=i, column=0, sticky=tk.W, padx=5)
            progress = ttk.Progressbar(metrics_frame, mode='determinate', length=200)
            progress.grid(row=i, column=1, padx=5, pady=2)
            self.coverage_bars[key] = progress
            
            # Coverage percentage label
            percent_label = ttk.Label(metrics_frame, text="0%")
            percent_label.grid(row=i, column=2, padx=5)
            self.coverage_bars[f"{key}_label"] = percent_label
        
        # Coverage details
        details_frame = ttk.LabelFrame(coverage_frame, text="Coverage Details", padding=10)
        details_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        self.coverage_text = tk.Text(details_frame, wrap=tk.WORD)
        coverage_scroll = ttk.Scrollbar(details_frame, orient=tk.VERTICAL, command=self.coverage_text.yview)
        self.coverage_text.configure(yscrollcommand=coverage_scroll.set)
        
        self.coverage_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        coverage_scroll.pack(side=tk.RIGHT, fill=tk.Y)
    
    def create_vip_environment(self):
        """Create VIP environment based on current bus configuration"""
        try:
            # Validate GUI instance
            if not hasattr(self.gui, 'current_config'):
                messagebox.showerror("Error", "GUI configuration not available")
                return
                
            if not hasattr(self.gui.current_config, 'masters') or not hasattr(self.gui.current_config, 'slaves'):
                messagebox.showerror("Error", "Bus configuration is incomplete")
                return
                
            if not self.gui.current_config.masters or not self.gui.current_config.slaves:
                messagebox.showerror("Error", "No masters or slaves configured. Please add components first.")
                return
            
            if not VIP_COMPONENTS_AVAILABLE:
                # Create placeholder environment when components not available
                self.vip_environment = {
                    'masters': [{'name': f'Master_{i}_{m.name}'} for i, m in enumerate(self.gui.current_config.masters)],
                    'slaves': [{'name': f'Slave_{i}_{s.name}', 'base_addr': s.base_address, 'end_addr': s.get_end_address()} 
                              for i, s in enumerate(self.gui.current_config.slaves)],
                    'monitors': [{'name': 'Monitor_0'}],
                    'checkers': [{'name': 'Checker_0'}]
                }
                self.env_status_label.config(text="Environment: Created (Placeholder Mode)")
                self.update_config_tree()
                messagebox.showinfo("Info", "VIP environment created in placeholder mode.\nExport configuration for UVM simulation.")
                return
            
            # Create VIP configs for masters
            master_configs = []
            for master in self.gui.current_config.masters:
                vip_config = VIPConfig(
                    name=master.name,
                    data_width=self.gui.current_config.data_width,
                    addr_width=self.gui.current_config.addr_width,
                    id_width=getattr(master, 'id_width', 4),
                    user_width=getattr(master, 'user_width', 0)
                )
                master_configs.append(vip_config)
            
            # Create slave configs
            slave_configs = []
            for slave in self.gui.current_config.slaves:
                slave_vip_config = VIPConfig(
                    name=slave.name,
                    data_width=self.gui.current_config.data_width,
                    addr_width=self.gui.current_config.addr_width
                )
                slave_configs.append((slave_vip_config, slave.base_address, slave.size * 1024))
            
            # Create VIP environment
            self.vip_environment = create_axi_vip_environment(
                masters=master_configs,
                slaves=slave_configs
            )
            
            self.env_status_label.config(text="Environment: Created Successfully")
            self.update_config_tree()
            
            messagebox.showinfo("Success", 
                              f"VIP Environment created with {len(master_configs)} masters and {len(slave_configs)} slaves")
            
        except AttributeError as e:
            # Handle missing attributes
            messagebox.showerror("Configuration Error", 
                               f"Missing configuration attribute: {str(e)}\n\n"
                               "Please ensure all masters and slaves are properly configured.")
        except Exception as e:
            # General error handling
            import traceback
            error_details = traceback.format_exc()
            messagebox.showerror("VIP Environment Error", 
                               f"Failed to create VIP environment:\n{str(e)}\n\n"
                               "Check the console for more details.")
            print(f"[ERROR] VIP Environment creation failed:\n{error_details}")
    
    def update_config_tree(self):
        """Update VIP configuration tree display"""
        # Clear existing items
        for item in self.config_tree.get_children():
            self.config_tree.delete(item)
        
        if not self.vip_environment:
            return
        
        # Add masters
        masters_node = self.config_tree.insert('', 'end', text='Masters', values=('Container', '', 'Active'))
        for i, master in enumerate(self.vip_environment['masters']):
            # Handle both VIP objects and placeholder dicts
            if isinstance(master, dict):
                name = master.get('name', f'Master_{i}')
                config_str = "Placeholder Mode"
            else:
                name = master.config.name
                config_str = f"ID_W:{master.config.id_width}, DATA_W:{master.config.data_width}"
            
            self.config_tree.insert(masters_node, 'end', 
                                   text=name,
                                   values=('AXI Master Agent', config_str, 'Ready'))
        
        # Add slaves
        slaves_node = self.config_tree.insert('', 'end', text='Slaves', values=('Container', '', 'Active'))
        for i, slave in enumerate(self.vip_environment['slaves']):
            # Handle both VIP objects and placeholder dicts
            if isinstance(slave, dict):
                name = slave.get('name', f'Slave_{i}')
                base = slave.get('base_addr', 0)
                size = slave.get('size', 0) // 1024 if 'size' in slave else 0
                config_str = f"Base:0x{base:X}, Size:{size}KB"
            else:
                name = slave.config.name
                config_str = f"Base:0x{slave.base_addr:X}, Size:{slave.size_bytes//1024}KB"
            
            self.config_tree.insert(slaves_node, 'end',
                                   text=name,
                                   values=('AXI Slave Agent', config_str, 'Ready'))
        
        # Add monitors
        monitors_node = self.config_tree.insert('', 'end', text='Monitors', values=('Container', '', 'Active'))
        for i, monitor in enumerate(self.vip_environment.get('monitors', [])):
            # Handle both VIP objects and placeholder dicts
            if isinstance(monitor, dict):
                name = monitor.get('name', f'Monitor_{i}')
            else:
                name = f"Monitor_{i}"
            
            self.config_tree.insert(monitors_node, 'end',
                                   text=name,
                                   values=('AXI Monitor', 'Protocol Checking', 'Active'))
        
        # Add checkers
        checkers_node = self.config_tree.insert('', 'end', text='Checkers', values=('Container', '', 'Active'))
        for i, checker in enumerate(self.vip_environment.get('checkers', [])):
            # Handle both VIP objects and placeholder dicts
            if isinstance(checker, dict):
                name = checker.get('name', f'Checker_{i}')
            else:
                name = f"Checker_{i}"
            
            self.config_tree.insert(checkers_node, 'end',
                                   text=name,
                                   values=('AXI Checker', 'Assertion Checking', 'Active'))
        
        # Expand all nodes
        self.config_tree.item(masters_node, open=True)
        self.config_tree.item(slaves_node, open=True)
        self.config_tree.item(monitors_node, open=True)
        self.config_tree.item(checkers_node, open=True)
    
    def generate_test_suite(self):
        """Generate comprehensive test suite"""
        if not VIP_COMPONENTS_AVAILABLE:
            messagebox.showinfo("Info", "Test generation requires VIP components.\nPlease export configuration for UVM simulation instead.")
            return
            
        if not self.vip_environment:
            messagebox.showerror("Error", "Please create VIP environment first")
            return
        
        try:
            # Get test parameters
            num_transactions = int(self.num_transactions_var.get())
            addr_start = int(self.addr_start_var.get(), 16)
            addr_end = int(self.addr_end_var.get(), 16)
            
            # Use first master for test generation
            master = self.vip_environment['masters'][0]
            
            # Generate test suite
            self.test_suite = {}
            summary_text = "Generated Test Suite Summary:\n" + "="*50 + "\n"
            
            for scenario_id, var in self.scenario_vars.items():
                if var.get():  # Scenario is enabled
                    # Create scenario config
                    if VIP_COMPONENTS_AVAILABLE:
                        scenario_config = TestScenarioConfig(
                            name=scenario_id.replace('_', ' ').title(),
                            description=f"Auto-generated {scenario_id} test scenario",
                            num_transactions=num_transactions,
                            address_range=(addr_start, addr_end)
                        )
                        
                        # Generate sequences
                        generator = AXITestSequenceGenerator(master, scenario_config)
                    else:
                        # Placeholder when components not available
                        transactions = []
                    
                    if scenario_id == 'basic':
                        transactions = generator.generate_basic_sequences()
                    elif scenario_id == 'advanced':
                        transactions = generator.generate_advanced_sequences()
                    elif scenario_id == 'error_injection':
                        transactions = generator.generate_error_injection_sequences()
                    elif scenario_id == 'stress':
                        transactions = generator.generate_stress_test_sequences()
                    
                    self.test_suite[scenario_id] = transactions
                    
                    # Update summary
                    summary_text += f"\n{scenario_config.name}:\n"
                    summary_text += f"  - Transactions: {len(transactions)}\n"
                    summary_text += f"  - Address Range: 0x{addr_start:X} - 0x{addr_end:X}\n"
                    
                    # Analyze transaction types
                    writes = sum(1 for tx in transactions if tx.is_write)
                    reads = len(transactions) - writes
                    summary_text += f"  - Writes: {writes}, Reads: {reads}\n"
                    
                    # Analyze burst types
                    burst_types = {}
                    for tx in transactions:
                        burst_name = tx.burst.name
                        burst_types[burst_name] = burst_types.get(burst_name, 0) + 1
                    
                    summary_text += f"  - Burst Types: {burst_types}\n"
            
            total_transactions = sum(len(txs) for txs in self.test_suite.values())
            summary_text += f"\nTotal Transactions: {total_transactions}\n"
            summary_text += f"Estimated Test Time: {total_transactions * 0.01:.1f} seconds\n"
            
            # Update summary display
            self.test_summary_text.delete(1.0, tk.END)
            self.test_summary_text.insert(1.0, summary_text)
            
            messagebox.showinfo("Success", f"Generated test suite with {total_transactions} transactions")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to generate test suite: {str(e)}")
    
    def run_tests(self):
        """Run generated test suite"""
        if not VIP_COMPONENTS_AVAILABLE:
            messagebox.showinfo("Info", "Test execution requires VIP components.\nPlease export configuration and run UVM simulation instead.")
            return
            
        if not hasattr(self, 'test_suite') or not self.test_suite:
            messagebox.showerror("Error", "Please generate test suite first")
            return
        
        if self.test_running:
            messagebox.showwarning("Warning", "Tests are already running")
            return
        
        # Start test execution in separate thread
        self.test_running = True
        self.test_thread = threading.Thread(target=self._execute_tests)
        self.test_thread.daemon = True
        self.test_thread.start()
        
        self.test_status_label.config(text="Running tests...")
    
    def _execute_tests(self):
        """Execute test suite (runs in separate thread)"""
        try:
            total_tests = sum(len(txs) for txs in self.test_suite.values())
            completed_tests = 0
            
            self.test_results = {}
            
            # Clear previous results
            self.gui.root.after(0, self._clear_results_display)
            
            for scenario_name, transactions in self.test_suite.items():
                if not self.test_running:
                    break
                
                scenario_start_time = time.time()
                scenario_results = {
                    'transactions_run': 0,
                    'responses_received': 0,
                    'errors': 0,
                    'protocol_violations': [],
                    'start_time': scenario_start_time
                }
                
                # Update status
                self.gui.root.after(0, lambda s=scenario_name: 
                                   self.test_status_label.config(text=f"Running: {s}"))
                
                # Execute transactions
                for tx in transactions:
                    if not self.test_running:
                        break
                    
                    # Simulate transaction execution
                    response = self._simulate_transaction(tx)
                    
                    scenario_results['transactions_run'] += 1
                    if response:
                        scenario_results['responses_received'] += 1
                        if response.response != 'OKAY':
                            scenario_results['errors'] += 1
                    
                    completed_tests += 1
                    
                    # Update progress
                    progress = int((completed_tests / total_tests) * 100)
                    self.gui.root.after(0, lambda p=progress: 
                                       self.test_progress.config(value=p))
                    
                    # Small delay to simulate real execution
                    time.sleep(0.001)
                
                scenario_results['duration'] = time.time() - scenario_start_time
                self.test_results[scenario_name] = scenario_results
                
                # Update results display
                self.gui.root.after(0, lambda: self._update_results_display())
            
            # Test completion
            self.test_running = False
            self.gui.root.after(0, lambda: self.test_status_label.config(text="Tests completed"))
            self.gui.root.after(0, lambda: messagebox.showinfo("Success", "Test execution completed"))
            
        except Exception as e:
            self.test_running = False
            self.gui.root.after(0, lambda: messagebox.showerror("Error", f"Test execution failed: {str(e)}"))
    
    def _simulate_transaction(self, transaction):
        """Simulate transaction execution with VIP components"""
        if not self.vip_environment:
            return None
        
        try:
            # Find appropriate slave based on address
            target_slave = None
            for slave in self.vip_environment['slaves']:
                if slave.base_addr <= transaction.addr <= slave.end_addr:
                    target_slave = slave
                    break
            
            if target_slave:
                # Process transaction through slave agent
                if VIP_COMPONENTS_AVAILABLE and hasattr(target_slave, 'process_transaction'):
                    response = target_slave.process_transaction(transaction)
                else:
                    # Placeholder response
                    response = transaction  # Just return the transaction as response
                
                # Monitor the transaction
                if self.vip_environment['monitors']:
                    monitor = self.vip_environment['monitors'][0]
                    monitor.observe_transaction(response)
                
                return response
            else:
                # No slave found - DECERR
                transaction.response = 'DECERR'
                return transaction
                
        except Exception:
            return None
    
    def _clear_results_display(self):
        """Clear results display"""
        for item in self.results_tree.get_children():
            self.results_tree.delete(item)
        
        for key in self.stats_labels:
            self.stats_labels[key].config(text="0")
    
    def _update_results_display(self):
        """Update results display with current test results"""
        # Clear existing items
        for item in self.results_tree.get_children():
            self.results_tree.delete(item)
        
        # Calculate totals
        total_tests = sum(r['transactions_run'] for r in self.test_results.values())
        total_responses = sum(r['responses_received'] for r in self.test_results.values())
        total_errors = sum(r['errors'] for r in self.test_results.values())
        total_violations = sum(len(r['protocol_violations']) for r in self.test_results.values())
        
        # Update statistics
        self.stats_labels['total_tests'].config(text=str(total_tests))
        self.stats_labels['passed_tests'].config(text=str(total_responses - total_errors))
        self.stats_labels['failed_tests'].config(text=str(total_errors))
        self.stats_labels['protocol_violations'].config(text=str(total_violations))
        self.stats_labels['transactions_generated'].config(text=str(total_tests))
        self.stats_labels['responses_received'].config(text=str(total_responses))
        
        # Update results tree
        for scenario_name, results in self.test_results.items():
            status = "PASS" if results['errors'] == 0 else "FAIL"
            status_color = "green" if status == "PASS" else "red"
            
            item = self.results_tree.insert('', 'end', 
                                           text=scenario_name,
                                           values=(status, 
                                                  results['transactions_run'],
                                                  results['errors'],
                                                  f"{results.get('duration', 0):.2f}"))
            
            # Set color based on status
            if status == "FAIL":
                self.results_tree.set(item, 'Status', '[ERROR] FAIL')
            else:
                self.results_tree.set(item, 'Status', '[OK] PASS')
    
    def stop_tests(self):
        """Stop running tests"""
        if self.test_running:
            self.test_running = False
            self.test_status_label.config(text="Stopping tests...")
            messagebox.showinfo("Info", "Tests will stop after current transaction")
    
    def reset_vip_environment(self):
        """Reset VIP environment"""
        if self.test_running:
            messagebox.showwarning("Warning", "Cannot reset while tests are running")
            return
        
        self.vip_environment = None
        self.env_status_label.config(text="Environment: Not Created")
        
        # Clear displays
        for item in self.config_tree.get_children():
            self.config_tree.delete(item)
        
        self.test_summary_text.delete(1.0, tk.END)
        
        messagebox.showinfo("Info", "VIP environment reset")
    
    def export_vip_config(self):
        """Export VIP configuration"""
        if not self.vip_environment:
            messagebox.showerror("Error", "No VIP environment to export")
            return
        
        filename = filedialog.asksaveasfilename(
            title="Export VIP Configuration",
            defaultextension=".json",
            filetypes=[("JSON files", "*.json")]
        )
        
        if filename:
            try:
                config_data = {
                    'masters': [{'name': m.config.name, 'config': asdict(m.config)} 
                               for m in self.vip_environment['masters']],
                    'slaves': [{'name': s.config.name, 'base_addr': s.base_addr, 'size': s.size_bytes}
                              for s in self.vip_environment['slaves']],
                    'environment_status': 'created',
                    'export_timestamp': time.time()
                }
                
                with open(filename, 'w') as f:
                    json.dump(config_data, f, indent=2)
                
                messagebox.showinfo("Success", f"VIP configuration exported to {filename}")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to export configuration: {str(e)}")
    
    def export_results(self):
        """Export test results"""
        if not self.test_results:
            messagebox.showwarning("Warning", "No test results to export")
            return
        
        filename = filedialog.asksaveasfilename(
            title="Export Test Results",
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("CSV files", "*.csv")]
        )
        
        if filename:
            try:
                if filename.endswith('.csv'):
                    self._export_results_csv(filename)
                else:
                    self._export_results_json(filename)
                
                messagebox.showinfo("Success", f"Test results exported to {filename}")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to export results: {str(e)}")
    
    def _export_results_json(self, filename):
        """Export results as JSON"""
        export_data = {
            'test_results': self.test_results,
            'summary': {
                'total_tests': sum(r['transactions_run'] for r in self.test_results.values()),
                'total_errors': sum(r['errors'] for r in self.test_results.values()),
                'export_timestamp': time.time()
            }
        }
        
        with open(filename, 'w') as f:
            json.dump(export_data, f, indent=2)
    
    def _export_results_csv(self, filename):
        """Export results as CSV"""
        import csv
        
        with open(filename, 'w', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(['Scenario', 'Transactions', 'Responses', 'Errors', 'Duration'])
            
            for scenario_name, results in self.test_results.items():
                writer.writerow([
                    scenario_name,
                    results['transactions_run'],
                    results['responses_received'],
                    results['errors'],
                    f"{results.get('duration', 0):.2f}"
                ])
    
    def generate_report(self):
        """Generate comprehensive test report"""
        if not self.test_results:
            messagebox.showwarning("Warning", "No test results to report")
            return
        
        filename = filedialog.asksaveasfilename(
            title="Save Test Report",
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt"), ("HTML files", "*.html")]
        )
        
        if filename:
            try:
                if filename.endswith('.html'):
                    self._generate_html_report(filename)
                else:
                    self._generate_text_report(filename)
                
                messagebox.showinfo("Success", f"Test report generated: {filename}")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to generate report: {str(e)}")
    
    def _generate_text_report(self, filename):
        """Generate text format test report"""
        with open(filename, 'w') as f:
            f.write("AXI4 VIP Test Report\n")
            f.write("=" * 50 + "\n\n")
            
            # Summary
            total_tests = sum(r['transactions_run'] for r in self.test_results.values())
            total_errors = sum(r['errors'] for r in self.test_results.values())
            
            f.write(f"Test Summary:\n")
            f.write(f"  Total Tests: {total_tests}\n")
            f.write(f"  Passed: {total_tests - total_errors}\n")
            f.write(f"  Failed: {total_errors}\n")
            f.write(f"  Success Rate: {((total_tests - total_errors) / total_tests * 100):.1f}%\n\n")
            
            # Scenario details
            f.write("Scenario Results:\n")
            f.write("-" * 30 + "\n")
            
            for scenario_name, results in self.test_results.items():
                f.write(f"\n{scenario_name.upper()}:\n")
                f.write(f"  Transactions: {results['transactions_run']}\n")
                f.write(f"  Responses: {results['responses_received']}\n")
                f.write(f"  Errors: {results['errors']}\n")
                f.write(f"  Duration: {results.get('duration', 0):.2f}s\n")
                
                if results['protocol_violations']:
                    f.write(f"  Protocol Violations: {len(results['protocol_violations'])}\n")
    
    def _generate_html_report(self, filename):
        """Generate HTML format test report"""
        total_tests = sum(r['transactions_run'] for r in self.test_results.values())
        total_errors = sum(r['errors'] for r in self.test_results.values())
        success_rate = ((total_tests - total_errors) / total_tests * 100) if total_tests > 0 else 0
        
        html_content = f"""
        <!DOCTYPE html>
        <html>
        <head>
            <title>AXI4 VIP Test Report</title>
            <style>
                body {{ font-family: Arial, sans-serif; margin: 20px; }}
                .header {{ background-color: #f0f0f0; padding: 20px; border-radius: 5px; }}
                .summary {{ margin: 20px 0; }}
                .pass {{ color: green; }}
                .fail {{ color: red; }}
                table {{ border-collapse: collapse; width: 100%; }}
                th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
                th {{ background-color: #f2f2f2; }}
            </style>
        </head>
        <body>
            <div class="header">
                <h1>AXI4 VIP Test Report</h1>
                <p>Generated: {time.strftime('%Y-%m-%d %H:%M:%S')}</p>
            </div>
            
            <div class="summary">
                <h2>Test Summary</h2>
                <p>Total Tests: <strong>{total_tests}</strong></p>
                <p>Passed: <strong class="pass">{total_tests - total_errors}</strong></p>
                <p>Failed: <strong class="fail">{total_errors}</strong></p>
                <p>Success Rate: <strong>{success_rate:.1f}%</strong></p>
            </div>
            
            <h2>Scenario Results</h2>
            <table>
                <tr>
                    <th>Scenario</th>
                    <th>Status</th>
                    <th>Transactions</th>
                    <th>Errors</th>
                    <th>Duration (s)</th>
                </tr>
        """
        
        for scenario_name, results in self.test_results.items():
            status = "PASS" if results['errors'] == 0 else "FAIL"
            status_class = "pass" if status == "PASS" else "fail"
            
            html_content += f"""
                <tr>
                    <td>{scenario_name}</td>
                    <td class="{status_class}">{status}</td>
                    <td>{results['transactions_run']}</td>
                    <td>{results['errors']}</td>
                    <td>{results.get('duration', 0):.2f}</td>
                </tr>
            """
        
        html_content += """
            </table>
        </body>
        </html>
        """
        
        with open(filename, 'w') as f:
            f.write(html_content)
    
    def export_uvm_configuration(self):
        """Export GUI configuration for UVM simulation"""
        try:
            if not self.gui.current_config.masters or not self.gui.current_config.slaves:
                messagebox.showerror("Error", "No masters or slaves configured. Please add components first.")
                return
            
            # Get VIP mode and RTL path
            vip_mode = self.vip_mode_var.get()
            rtl_path = self.rtl_path_var.get() if vip_mode == "RTL" else None
            
            # Use the selected VIP output directory
            vip_output_dir = self.vip_output_dir_var.get()
            
            # Export configuration using the UVM config exporter
            export_paths = export_gui_config_to_uvm(
                self.gui.current_config, 
                vip_mode, 
                rtl_path,
                output_dir=vip_output_dir
            )
            
            if export_paths:
                # Show success message with paths
                paths_text = "\n".join([f"• {name}: {path}" for name, path in export_paths.items()])
                message = f"[OK] UVM configuration exported successfully!\n\nGenerated files:\n{paths_text}\n\n"
                message += "[CONFIG] Next steps:\n"
                message += "1. cd ../axi4_vip_sim\n"
                message += "2. make run TEST=axi4_basic_test\n"
                message += "3. Or use the generated test script"
                
                messagebox.showinfo("Export Success", message)
                
                # Add export info to config tree
                self.update_export_tree(export_paths)
            
        except Exception as e:
            messagebox.showerror("Export Error", f"Failed to export UVM configuration:\n{str(e)}")
    
    def open_uvm_directory(self):
        """Open UVM simulation directory in file manager"""
        import subprocess
        import platform
        import os
        
        # Get path to UVM simulation directory
        current_dir = os.path.dirname(os.path.abspath(__file__))
        uvm_dir = os.path.join(current_dir, "..", "..", "..", "axi4_vip_sim")
        uvm_dir = os.path.abspath(uvm_dir)
        
        if not os.path.exists(uvm_dir):
            messagebox.showerror("Error", f"UVM simulation directory not found:\n{uvm_dir}")
            return
        
        try:
            # Open directory in OS-specific file manager
            if platform.system() == "Windows":
                os.startfile(uvm_dir)
            elif platform.system() == "Darwin":  # macOS
                subprocess.run(["open", uvm_dir])
            else:  # Linux and others
                subprocess.run(["xdg-open", uvm_dir])
                
            messagebox.showinfo("Info", f"Opened UVM simulation directory:\n{uvm_dir}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to open directory:\n{str(e)}")
    
    def show_uvm_commands(self):
        """Show UVM simulation commands"""
        commands_text = """[CONFIG] UVM Simulation Commands

Basic Commands:
  make run TEST=axi4_basic_test
  make run TEST=axi4_comprehensive_test
  make gui TEST=axi4_basic_test
  make coverage
  make clean

With Configuration File:
  make run TEST=axi4_basic_test CONFIG_FILE=output/configs/<config>.json

Using Automated Script:
  ./scripts/run_sim.sh -t axi4_basic_test
  ./scripts/run_sim.sh -t axi4_comprehensive_test -g -c
  ./scripts/run_sim.sh --regression

Output Locations:
  [DIR] Logs: output/logs/
  [DIR] Waveforms: output/waves/
  [DIR] Coverage: output/coverage/
  [DIR] Reports: output/reports/

Simulators Supported:
  • VCS (default): make run SIM=vcs
  • Questa: make run SIM=questa  
  • Xcelium: make run SIM=xcelium

For help: make help"""
        
        # Create a new window to display commands
        cmd_window = tk.Toplevel(self.parent)
        cmd_window.title("UVM Simulation Commands")
        cmd_window.geometry("600x500")
        
        # Text widget with scrollbar
        text_frame = ttk.Frame(cmd_window)
        text_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        text_widget = tk.Text(text_frame, wrap=tk.WORD, font=("Consolas", 10))
        scrollbar = ttk.Scrollbar(text_frame, orient=tk.VERTICAL, command=text_widget.yview)
        text_widget.configure(yscrollcommand=scrollbar.set)
        
        text_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        text_widget.insert(1.0, commands_text)
        text_widget.config(state=tk.DISABLED)
        
        # Close button
        ttk.Button(cmd_window, text="Close", command=cmd_window.destroy).pack(pady=10)
    
    def update_export_tree(self, export_paths):
        """Update configuration tree with export information"""
        # Clear existing items
        for item in self.config_tree.get_children():
            self.config_tree.delete(item)
        
        # Add export information
        export_node = self.config_tree.insert('', 'end', text='Exported Files', values=('Export', 'UVM Config', 'Ready'))
        
        for file_type, file_path in export_paths.items():
            if file_type == 'json':
                desc = 'UVM Configuration JSON'
            elif file_type == 'makefile':
                desc = 'Makefile Arguments'
            elif file_type == 'script':
                desc = 'Test Execution Script'
            elif file_type == 'summary':
                desc = 'Configuration Summary'
            else:
                desc = file_type.title()
            
            self.config_tree.insert(export_node, 'end',
                                   text=f"{file_type.upper()}",
                                   values=(desc, os.path.basename(file_path), 'Generated'))
        
        # Add bus configuration summary
        bus_node = self.config_tree.insert('', 'end', text='Bus Configuration', values=('Config', 'Current', 'Active'))
        
        # Add masters info
        masters_node = self.config_tree.insert(bus_node, 'end', text='Masters', values=('Container', f'{len(self.gui.current_config.masters)} components', 'Active'))
        for i, master in enumerate(self.gui.current_config.masters):
            self.config_tree.insert(masters_node, 'end',
                                   text=f"Master_{i}_{master.name}",
                                   values=('AXI Master', f'Priority: {getattr(master, "priority", 0)}', 'Ready'))
        
        # Add slaves info
        slaves_node = self.config_tree.insert(bus_node, 'end', text='Slaves', values=('Container', f'{len(self.gui.current_config.slaves)} components', 'Active'))
        for i, slave in enumerate(self.gui.current_config.slaves):
            self.config_tree.insert(slaves_node, 'end',
                                   text=f"Slave_{i}_{slave.name}",
                                   values=('AXI Slave', f'0x{slave.base_address:X} ({slave.size}KB)', 'Ready'))
        
        # Expand all nodes
        self.config_tree.item(export_node, open=True)
        self.config_tree.item(bus_node, open=True)
        self.config_tree.item(masters_node, open=True)
        self.config_tree.item(slaves_node, open=True)
    
    def on_vip_mode_change(self):
        """Handle VIP mode selection change"""
        mode = self.vip_mode_var.get()
        
        if mode == "RTL":
            # Enable RTL path controls
            self.rtl_path_entry.config(state=tk.NORMAL)
            self.rtl_browse_btn.config(state=tk.NORMAL)
            
            # Check if RTL has been generated
            if hasattr(self.gui, 'last_generated_rtl_path'):
                self.rtl_path_var.set(self.gui.last_generated_rtl_path)
            else:
                messagebox.showinfo("Info", "Please generate RTL first using 'Generate RTL' button in the main GUI")
        else:
            # Disable RTL path controls
            self.rtl_path_entry.config(state=tk.DISABLED)
            self.rtl_browse_btn.config(state=tk.DISABLED)
    
    def browse_rtl_path(self):
        """Browse for RTL file"""
        filename = filedialog.askopenfilename(
            title="Select Generated RTL File",
            filetypes=[("Verilog files", "*.v *.sv"), ("All files", "*.*")],
            initialdir=os.path.join(os.path.dirname(__file__), "..", "..", "output")
        )
        
        if filename:
            self.rtl_path_var.set(filename)
    
    def generate_rtl_for_vip(self):
        """Generate RTL from current configuration"""
        try:
            # Check if we have a valid configuration
            if not self.gui.current_config.masters or not self.gui.current_config.slaves:
                messagebox.showerror("Error", "No masters or slaves configured. Please add components first.")
                return
            
            # Generate RTL using the existing generator
            from axi_verilog_generator import AXIVerilogGenerator
            
            generator = AXIVerilogGenerator(self.gui.current_config)
            
            # Use the selected Verilog output directory
            output_dir = self.verilog_output_dir_var.get()
            os.makedirs(output_dir, exist_ok=True)
            
            output_file = os.path.join(output_dir, f"axi4_interconnect_{self.gui.current_config.bus_type.lower()}.v")
            
            if generator.generate_verilog(output_file):
                self.gui.last_generated_rtl_path = output_file
                self.rtl_path_var.set(output_file)
                
                messagebox.showinfo("Success", f"RTL generated successfully!\n\nFile: {output_file}\n\nYou can now select 'RTL Integration' mode and export configuration.")
                
                # Auto-switch to RTL mode
                self.vip_mode_var.set("RTL")
                self.on_vip_mode_change()
            else:
                messagebox.showerror("Error", "Failed to generate RTL")
                
        except Exception as e:
            messagebox.showerror("Error", f"RTL generation failed: {str(e)}")
    
    def browse_vip_output_dir(self):
        """Browse for VIP output directory"""
        directory = filedialog.askdirectory(
            title="Select VIP Output Directory",
            initialdir=self.vip_output_dir_var.get()
        )
        
        if directory:
            self.vip_output_dir_var.set(directory)
            print(f"[INFO] VIP output directory set to: {directory}")
    
    def browse_verilog_output_dir(self):
        """Browse for Verilog output directory"""
        directory = filedialog.askdirectory(
            title="Select Verilog Output Directory",
            initialdir=self.verilog_output_dir_var.get()
        )
        
        if directory:
            self.verilog_output_dir_var.set(directory)
            print(f"[INFO] Verilog output directory set to: {directory}")
    
    def create_output_directories(self):
        """Create the output directories if they don't exist"""
        try:
            vip_dir = self.vip_output_dir_var.get()
            verilog_dir = self.verilog_output_dir_var.get()
            
            created = []
            
            # Create VIP output directory structure
            vip_subdirs = ['configs', 'scripts', 'reports', 'logs', 'waves', 'coverage']
            for subdir in vip_subdirs:
                dir_path = os.path.join(vip_dir, subdir)
                if not os.path.exists(dir_path):
                    os.makedirs(dir_path, exist_ok=True)
                    created.append(f"VIP/{subdir}")
            
            # Create Verilog output directory
            if not os.path.exists(verilog_dir):
                os.makedirs(verilog_dir, exist_ok=True)
                created.append("Verilog/RTL")
            
            if created:
                messagebox.showinfo("Success", 
                                  f"Created output directories:\n\n" + "\n".join(created) +
                                  f"\n\nVIP Output: {vip_dir}\n" +
                                  f"Verilog Output: {verilog_dir}")
            else:
                messagebox.showinfo("Info", "All output directories already exist.")
                
        except Exception as e:
            messagebox.showerror("Error", f"Failed to create directories: {str(e)}")

def integrate_vip_with_gui(bus_matrix_gui):
    """Integrate VIP components with existing Bus Matrix GUI"""
    
    # Add VIP tab to main notebook if it exists
    if hasattr(bus_matrix_gui, 'canvas') and hasattr(bus_matrix_gui.canvas, 'master'):
        # Find the main frame to add VIP controls
        main_frame = bus_matrix_gui.canvas.master
        
        # Create VIP control panel
        vip_frame = ttk.LabelFrame(main_frame, text="AXI4 Verification IP", padding=10)
        vip_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Create VIP control panel
        vip_panel = VIPControlPanel(vip_frame, bus_matrix_gui)
        
        return vip_panel
    
    return None