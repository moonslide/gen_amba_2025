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
        """Show VIP Environment Setup dialog for mode selection"""
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
            
            # Show VIP Environment Setup dialog
            self.show_vip_setup_dialog()
            
        except Exception as e:
            # General error handling
            import traceback
            error_details = traceback.format_exc()
            messagebox.showerror("VIP Environment Error", 
                               f"Failed to create VIP environment:\n{str(e)}\n\n"
                               "Check the console for more details.")
            print(f"[ERROR] VIP Environment creation failed:\n{error_details}")
    
    def show_vip_setup_dialog(self):
        """Show VIP Environment Setup dialog with mode selection"""
        dialog = tk.Toplevel(self.parent.winfo_toplevel())
        dialog.title("VIP Environment Setup")
        # Requirement 1.1: Set larger default size to show all content including Next button
        dialog.geometry("600x500")
        dialog.minsize(600, 500)  # Set minimum size to prevent resizing too small
        dialog.transient(self.parent.winfo_toplevel())
        dialog.grab_set()
        
        # Center the dialog
        dialog.update_idletasks()
        x = (dialog.winfo_screenwidth() // 2) - (dialog.winfo_width() // 2)
        y = (dialog.winfo_screenheight() // 2) - (dialog.winfo_height() // 2)
        dialog.geometry(f"+{x}+{y}")
        
        # Main frame
        main_frame = ttk.Frame(dialog, padding=20)
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # Title label
        title_label = ttk.Label(main_frame, text="Select VIP Generation Mode", 
                               font=('TkDefaultFont', 12, 'bold'))
        title_label.pack(pady=(0, 20))
        
        # Mode selection variable
        mode_var = tk.StringVar(value="rtl_integration")
        
        # RTL Integration Mode
        rtl_frame = ttk.LabelFrame(main_frame, text="", padding=10)
        rtl_frame.pack(fill=tk.X, pady=5)
        
        rtl_radio = ttk.Radiobutton(rtl_frame, text="RTL Integration Mode", 
                                   variable=mode_var, value="rtl_integration")
        rtl_radio.pack(anchor=tk.W)
        
        rtl_desc = ttk.Label(rtl_frame, 
                            text="Generate a verification environment designed to connect with an existing RTL DUT.",
                            wraplength=450, foreground="gray")
        rtl_desc.pack(anchor=tk.W, padx=(20, 0), pady=(5, 0))
        
        # VIP Standalone Mode
        vip_frame = ttk.LabelFrame(main_frame, text="", padding=10)
        vip_frame.pack(fill=tk.X, pady=5)
        
        vip_radio = ttk.Radiobutton(vip_frame, text="VIP Standalone Mode", 
                                   variable=mode_var, value="vip_standalone")
        vip_radio.pack(anchor=tk.W)
        
        vip_desc = ttk.Label(vip_frame, 
                            text="Generate a self-contained environment to run tests on the VIP independently.",
                            wraplength=450, foreground="gray")
        vip_desc.pack(anchor=tk.W, padx=(20, 0), pady=(5, 0))
        
        # Additional options frame
        options_frame = ttk.LabelFrame(main_frame, text="Additional Options", padding=10)
        options_frame.pack(fill=tk.X, pady=(20, 10))
        
        # Include example tests checkbox
        include_tests_var = tk.BooleanVar(value=True)
        tests_check = ttk.Checkbutton(options_frame, text="Include example test cases",
                                     variable=include_tests_var)
        tests_check.pack(anchor=tk.W)
        
        # Include documentation checkbox
        include_docs_var = tk.BooleanVar(value=True)
        docs_check = ttk.Checkbutton(options_frame, text="Generate documentation",
                                    variable=include_docs_var)
        docs_check.pack(anchor=tk.W)
        
        # Simulator selection
        sim_frame = ttk.Frame(options_frame)
        sim_frame.pack(fill=tk.X, pady=(10, 0))
        
        ttk.Label(sim_frame, text="Target Simulator:").pack(side=tk.LEFT)
        sim_var = tk.StringVar(value="vcs")
        sim_combo = ttk.Combobox(sim_frame, textvariable=sim_var, 
                                values=["vcs", "questa", "xcelium", "vivado"],
                                state="readonly", width=15)
        sim_combo.pack(side=tk.LEFT, padx=(10, 0))
        
        # Button frame
        button_frame = ttk.Frame(main_frame)
        button_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(20, 0))
        
        # Output directory selection frame (initially hidden)
        output_frame = ttk.LabelFrame(main_frame, text="Output Directory", padding=10)
        
        # Path display and browse button frame
        path_frame = ttk.Frame(output_frame)
        path_frame.pack(fill=tk.X, pady=(5, 10))
        
        output_path_var = tk.StringVar(value="")
        path_label = ttk.Label(path_frame, text="Selected Path:")
        path_label.pack(side=tk.LEFT)
        
        path_display = ttk.Label(path_frame, textvariable=output_path_var, 
                                relief="sunken", padding=5)
        path_display.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(10, 10))
        
        def browse_directory():
            # Requirement 2.1: Modal dialog for directory selection
            selected_dir = filedialog.askdirectory(
                title="Select Output Directory for VIP Environment",
                parent=dialog,  # Make it modal to this dialog
                initialdir=os.path.dirname(os.path.abspath("."))
            )
            
            if selected_dir:
                output_path_var.set(selected_dir)
                # Requirement 2.2: Show status after selection
                status_var.set("Path selected. Ready for execution.")
                generate_btn.config(state="normal")
        
        browse_btn = ttk.Button(path_frame, text="Browse...", command=browse_directory)
        browse_btn.pack(side=tk.LEFT)
        
        # Status label
        status_var = tk.StringVar(value="Please select an output directory.")
        status_label = ttk.Label(output_frame, textvariable=status_var, 
                                foreground="blue")
        status_label.pack(fill=tk.X, pady=(0, 10))
        
        # Generate button (initially disabled)
        def on_generate():
            if not output_path_var.get():
                messagebox.showerror("Error", "Please select an output directory first.", parent=dialog)
                return
            
            # Store selections
            self.vip_mode = mode_var.get()
            self.include_tests = include_tests_var.get()
            self.include_docs = include_docs_var.get()
            self.target_simulator = sim_var.get()
            
            # Update status
            status_var.set("Generating VIP environment...")
            dialog.update()
            
            try:
                # Generate VIP environment based on selected mode
                output_dir = output_path_var.get()
                if self.vip_mode == "rtl_integration":
                    # Check if we need to generate RTL first
                    if hasattr(self, 'rtl_source') and self.rtl_source == "generated":
                        status_var.set("Generating RTL design...")
                        dialog.update()
                        
                        # Generate RTL using the main GUI's Verilog generator
                        rtl_output_dir = os.path.join(output_dir, "rtl_integration_env", "rtl_wrapper", "generated_rtl")
                        os.makedirs(rtl_output_dir, exist_ok=True)
                        
                        # Use the AXI Verilog generator from main GUI
                        from axi_verilog_generator import AXIVerilogGenerator
                        generator = AXIVerilogGenerator(self.gui.current_config)
                        generator.output_dir = rtl_output_dir  # Set output directory
                        generated_dir = generator.generate()  # Generate RTL
                        
                        # Store the generated RTL path
                        self.generated_rtl_path = rtl_output_dir
                        
                        status_var.set("RTL generated. Creating VIP environment...")
                        dialog.update()
                    
                    env_path = self.generate_rtl_integration_environment(output_dir)
                else:
                    env_path = self.generate_vip_standalone_environment(output_dir)
                
                # Requirement 2.2: Show success with full path
                status_var.set(f"Success: VIP generated and saved to {env_path}")
                status_label.config(foreground="green")
                generate_btn.config(text="Close", command=dialog.destroy)
                
            except Exception as e:
                status_var.set(f"Error: {str(e)}")
                status_label.config(foreground="red")
        
        generate_btn = ttk.Button(output_frame, text="Generate VIP Environment", 
                                 command=on_generate, state="disabled")
        generate_btn.pack(fill=tk.X)
        
        # RTL source selection frame (initially hidden)
        rtl_source_frame = ttk.LabelFrame(main_frame, text="RTL Source Selection", padding=20)
        
        rtl_source_var = tk.StringVar(value="external")
        rtl_source_path_var = tk.StringVar(value="")
        
        # External RTL option
        ext_rtl_frame = ttk.Frame(rtl_source_frame)
        ext_rtl_frame.pack(fill=tk.X, pady=5)
        
        ext_rtl_radio = ttk.Radiobutton(ext_rtl_frame, text="Use External RTL IP", 
                                       variable=rtl_source_var, value="external")
        ext_rtl_radio.pack(anchor=tk.W)
        
        ext_rtl_desc = ttk.Label(ext_rtl_frame, 
                                text="Select this if you have an existing RTL design to verify.",
                                wraplength=550, foreground="gray")
        ext_rtl_desc.pack(anchor=tk.W, padx=(20, 0), pady=(5, 0))
        
        # Tool-generated RTL option
        gen_rtl_frame = ttk.Frame(rtl_source_frame)
        gen_rtl_frame.pack(fill=tk.X, pady=5)
        
        gen_rtl_radio = ttk.Radiobutton(gen_rtl_frame, text="Generate RTL with this Tool", 
                                       variable=rtl_source_var, value="generated")
        gen_rtl_radio.pack(anchor=tk.W)
        
        gen_rtl_desc = ttk.Label(gen_rtl_frame, 
                                text="The tool will generate Verilog RTL based on your bus configuration and automatically wrap it with VIP.",
                                wraplength=550, foreground="gray")
        gen_rtl_desc.pack(anchor=tk.W, padx=(20, 0), pady=(5, 0))
        
        # RTL path selection (for external RTL)
        rtl_path_frame = ttk.LabelFrame(rtl_source_frame, text="External RTL Location (Optional)", padding=10)
        rtl_path_frame.pack(fill=tk.X, pady=(20, 10))
        
        rtl_path_entry_frame = ttk.Frame(rtl_path_frame)
        rtl_path_entry_frame.pack(fill=tk.X)
        
        ttk.Label(rtl_path_entry_frame, text="RTL Directory:").pack(side=tk.LEFT)
        rtl_path_entry = ttk.Entry(rtl_path_entry_frame, textvariable=rtl_source_path_var)
        rtl_path_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(10, 10))
        
        def browse_rtl():
            rtl_dir = filedialog.askdirectory(
                title="Select Directory Containing Your RTL Files",
                parent=dialog
            )
            if rtl_dir:
                rtl_source_path_var.set(rtl_dir)
        
        ttk.Button(rtl_path_entry_frame, text="Browse...", command=browse_rtl).pack(side=tk.LEFT)
        
        ttk.Label(rtl_path_frame, 
                 text="Leave empty to manually add RTL files later.",
                 foreground="gray").pack(anchor=tk.W, pady=(5, 0))
        
        # RTL source navigation buttons
        rtl_source_btn_frame = ttk.Frame(rtl_source_frame)
        rtl_source_btn_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(20, 0))
        
        def on_rtl_source_next():
            # Store RTL source selection
            self.rtl_source = rtl_source_var.get()
            self.rtl_source_path = rtl_source_path_var.get()
            
            # Hide RTL source selection
            rtl_source_frame.pack_forget()
            rtl_source_btn_frame.pack_forget()
            
            # Show output directory selection
            output_frame.pack(fill=tk.BOTH, expand=True, pady=(20, 0))
            title_label.config(text="Select Output Directory")
        
        def on_rtl_source_back():
            # Go back to mode selection
            rtl_source_frame.pack_forget()
            rtl_source_btn_frame.pack_forget()
            
            # Show mode selection elements
            rtl_frame.pack(fill=tk.X, pady=5)
            vip_frame.pack(fill=tk.X, pady=5)
            options_frame.pack(fill=tk.X, pady=(20, 10))
            button_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(20, 0))
            
            title_label.config(text="Select VIP Generation Mode")
        
        ttk.Button(rtl_source_btn_frame, text="Next", command=on_rtl_source_next).pack(side=tk.RIGHT)
        ttk.Button(rtl_source_btn_frame, text="Back", command=on_rtl_source_back).pack(side=tk.RIGHT, padx=(0, 5))
        
        def on_next():
            # Store selections
            self.vip_mode = mode_var.get()
            self.include_tests = include_tests_var.get()
            self.include_docs = include_docs_var.get()
            self.target_simulator = sim_var.get()
            
            # Hide mode selection elements
            rtl_frame.pack_forget()
            vip_frame.pack_forget()
            options_frame.pack_forget()
            button_frame.pack_forget()
            
            if self.vip_mode == "rtl_integration":
                # Show RTL source selection for RTL integration mode
                rtl_source_frame.pack(fill=tk.BOTH, expand=True, pady=(20, 0))
                title_label.config(text="Select RTL Source")
            else:
                # Go directly to output directory selection for standalone mode
                output_frame.pack(fill=tk.BOTH, expand=True, pady=(20, 0))
                title_label.config(text="Select Output Directory")
        
        def on_cancel():
            dialog.destroy()
        
        # Buttons
        next_btn = ttk.Button(button_frame, text="Next", command=on_next)
        next_btn.pack(side=tk.RIGHT)
        ttk.Button(button_frame, text="Cancel", command=on_cancel).pack(side=tk.RIGHT, padx=(5, 5))
        
        # Focus on dialog
        dialog.focus_set()
    
    def select_output_directory_and_generate(self):
        """DEPRECATED: This method is replaced by the integrated dialog flow"""
        # This method is no longer used as directory selection is now 
        # integrated into the show_vip_setup_dialog workflow
        pass
    
    def generate_rtl_integration_environment(self, output_dir):
        """Generate RTL Integration Mode environment following tim_axi4_vip structure"""
        try:
            # Import the new VIP environment generator
            from vip_environment_generator import VIPEnvironmentGenerator
            
            # Create generator instance
            generator = VIPEnvironmentGenerator(
                gui_config=self.gui.current_config,
                mode="rtl_integration",
                simulator=self.target_simulator
            )
            
            # Generate the complete environment
            env_path = generator.generate_environment(output_dir)
            
            # If we have generated RTL, copy it to the environment
            if hasattr(self, 'generated_rtl_path') and os.path.exists(self.generated_rtl_path):
                import shutil
                dest_rtl_dir = os.path.join(env_path, "rtl_wrapper", "generated_rtl")
                if os.path.exists(dest_rtl_dir):
                    shutil.rmtree(dest_rtl_dir)
                shutil.copytree(self.generated_rtl_path, dest_rtl_dir)
                
                # Update the RTL filelist
                self._update_rtl_filelist(env_path)
            
            # Update status
            self.env_status_label.config(text="Environment: RTL Integration Mode")
            self.update_config_tree()
            
            # Return the full path for status display
            return env_path
            
        except Exception as e:
            raise Exception(f"Failed to generate RTL integration environment: {str(e)}")
    
    def generate_vip_standalone_environment(self, output_dir):
        """Generate VIP Standalone Mode environment following tim_axi4_vip structure"""
        try:
            # Import the new VIP environment generator
            from vip_environment_generator import VIPEnvironmentGenerator
            
            # Create generator instance
            generator = VIPEnvironmentGenerator(
                gui_config=self.gui.current_config,
                mode="vip_standalone",
                simulator=self.target_simulator
            )
            
            # Generate the complete environment
            env_path = generator.generate_environment(output_dir)
            
            # Update status
            self.env_status_label.config(text="Environment: VIP Standalone Mode")
            self.update_config_tree()
            
            # Return the full path for status display
            return env_path
            
        except Exception as e:
            raise Exception(f"Failed to generate VIP standalone environment: {str(e)}")
    
    def _update_rtl_filelist(self, env_path):
        """Update RTL filelist with generated RTL files"""
        rtl_dir = os.path.join(env_path, "rtl_wrapper", "generated_rtl")
        filelist_path = os.path.join(env_path, "rtl_wrapper", "rtl_files.f")
        
        if os.path.exists(rtl_dir):
            rtl_files = []
            # Find all Verilog files
            for root, dirs, files in os.walk(rtl_dir):
                for file in files:
                    if file.endswith('.v') or file.endswith('.sv'):
                        rel_path = os.path.relpath(os.path.join(root, file), env_path)
                        rtl_files.append(f"${{VIP_ROOT}}/{rel_path}")
            
            # Write filelist
            with open(filelist_path, 'w') as f:
                f.write("# Auto-generated RTL file list\n")
                f.write("# Generated by AMBA Bus Matrix Configuration Tool\n\n")
                for rtl_file in sorted(rtl_files):
                    f.write(f"{rtl_file}\n")
    
    def update_config_tree(self):
        """Update VIP configuration tree display"""
        # Clear existing items
        for item in self.config_tree.get_children():
            self.config_tree.delete(item)
        
        # Check if we have a VIP mode set (new dialog-based flow)
        if hasattr(self, 'vip_mode') and self.vip_mode:
            # Display mode-based configuration
            mode_text = "RTL Integration" if self.vip_mode == "rtl_integration" else "VIP Standalone"
            mode_node = self.config_tree.insert('', 'end', text=f'Mode: {mode_text}', 
                                              values=('Configuration', self.vip_mode, 'Selected'))
            
            # Add configuration details
            config_node = self.config_tree.insert('', 'end', text='Bus Configuration', 
                                                values=('Settings', '', 'Active'))
            
            self.config_tree.insert(config_node, 'end', text='Bus Type',
                                  values=('Parameter', self.gui.current_config.bus_type, 'Set'))
            self.config_tree.insert(config_node, 'end', text='Data Width',
                                  values=('Parameter', f'{self.gui.current_config.data_width} bits', 'Set'))
            self.config_tree.insert(config_node, 'end', text='Address Width',
                                  values=('Parameter', f'{self.gui.current_config.addr_width} bits', 'Set'))
            
            # Add masters info
            masters_node = self.config_tree.insert('', 'end', text='Masters', 
                                                 values=('Components', f'{len(self.gui.current_config.masters)} configured', 'Ready'))
            for master in self.gui.current_config.masters:
                self.config_tree.insert(masters_node, 'end', text=master.name,
                                      values=('Master', f'ID Width: {master.id_width}', 'Configured'))
            
            # Add slaves info
            slaves_node = self.config_tree.insert('', 'end', text='Slaves', 
                                                values=('Components', f'{len(self.gui.current_config.slaves)} configured', 'Ready'))
            for slave in self.gui.current_config.slaves:
                self.config_tree.insert(slaves_node, 'end', text=slave.name,
                                      values=('Slave', f'0x{slave.base_address:X} ({slave.size}KB)', 'Configured'))
            
            # Expand nodes
            self.config_tree.item(config_node, open=True)
            self.config_tree.item(masters_node, open=True)
            self.config_tree.item(slaves_node, open=True)
            
        elif self.vip_environment:
            # Legacy display for old placeholder mode
            self._update_legacy_config_tree()
    
    def _update_legacy_config_tree(self):
        """Legacy config tree update for backward compatibility"""
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

    def _generate_rtl_integration_files(self, env_path):
        """Generate files for RTL Integration Mode"""
        # Create symbolic link to tim_axi4_vip
        tim_vip_path = os.path.abspath(os.path.join(os.path.dirname(__file__), 
                                                    "../../../../external/tim_axi4_vip"))
        vip_link = os.path.join(env_path, "tim_axi4_vip")
        if not os.path.exists(vip_link):
            os.symlink(tim_vip_path, vip_link)
        
        # Generate testbench top file
        tb_top_content = self._get_rtl_tb_top_template()
        with open(os.path.join(env_path, "tb", "top_tb.sv"), "w") as f:
            f.write(tb_top_content)
        
        # Check if we're using generated RTL or external RTL
        if hasattr(self, 'rtl_source') and self.rtl_source == "generated":
            # Generate wrapper for tool-generated RTL
            wrapper_content = self._get_generated_rtl_wrapper_template()
            with open(os.path.join(env_path, "rtl_wrapper", "dut_wrapper.sv"), "w") as f:
                f.write(wrapper_content)
            
            # Copy external RTL if path was provided
            if hasattr(self, 'rtl_source_path') and self.rtl_source_path:
                import shutil
                ext_rtl_dir = os.path.join(env_path, "rtl_wrapper", "external_rtl")
                shutil.copytree(self.rtl_source_path, ext_rtl_dir)
        else:
            # Generate standard wrapper for external RTL
            wrapper_content = self._get_rtl_wrapper_template()
            with open(os.path.join(env_path, "rtl_wrapper", "dut_wrapper.sv"), "w") as f:
                f.write(wrapper_content)
        
        # Generate compilation script
        compile_script = self._get_compile_script(self.target_simulator, "rtl_integration")
        with open(os.path.join(env_path, "scripts", "compile.sh"), "w") as f:
            f.write(compile_script)
        os.chmod(os.path.join(env_path, "scripts", "compile.sh"), 0o755)
        
        # Generate filelist
        filelist_content = self._get_filelist_template("rtl_integration")
        # Add generated RTL to filelist if applicable
        if hasattr(self, 'rtl_source') and self.rtl_source == "generated":
            filelist_content = filelist_content.replace(
                "# Add your RTL files here\n# ./rtl_wrapper/your_dut.sv",
                "# Generated RTL\n./rtl_wrapper/generated_rtl/*.v\n./rtl_wrapper/generated_rtl/*.sv"
            )
        with open(os.path.join(env_path, "scripts", "filelist.f"), "w") as f:
            f.write(filelist_content)
        
        # Generate run script
        run_script = self._get_run_script(self.target_simulator, "rtl_integration")
        with open(os.path.join(env_path, "scripts", "run_test.sh"), "w") as f:
            f.write(run_script)
        os.chmod(os.path.join(env_path, "scripts", "run_test.sh"), 0o755)
        
        # Generate example test
        if self.include_tests:
            test_content = self._get_example_test_template("rtl_integration")
            with open(os.path.join(env_path, "tb", "tests", "axi4_rtl_basic_test.sv"), "w") as f:
                f.write(test_content)
        
        # Generate documentation
        if self.include_docs:
            doc_content = self._get_documentation_template("rtl_integration")
            with open(os.path.join(env_path, "docs", "README.md"), "w") as f:
                f.write(doc_content)
        
        # Export current configuration
        config_data = {
            "mode": "rtl_integration",
            "bus_type": self.gui.current_config.bus_type,
            "data_width": self.gui.current_config.data_width,
            "addr_width": self.gui.current_config.addr_width,
            "masters": [asdict(m) for m in self.gui.current_config.masters],
            "slaves": [asdict(s) for s in self.gui.current_config.slaves]
        }
        
        with open(os.path.join(env_path, "configs", "bus_config.json"), "w") as f:
            json.dump(config_data, f, indent=2)
    
    def _generate_vip_standalone_files(self, env_path):
        """Generate files for VIP Standalone Mode"""
        # Create symbolic link to tim_axi4_vip
        tim_vip_path = os.path.abspath(os.path.join(os.path.dirname(__file__), 
                                                    "../../../../external/tim_axi4_vip"))
        vip_link = os.path.join(env_path, "tim_axi4_vip")
        if not os.path.exists(vip_link):
            os.symlink(tim_vip_path, vip_link)
        
        # Generate testbench top file
        tb_top_content = self._get_standalone_tb_top_template()
        with open(os.path.join(env_path, "tb", "top_tb.sv"), "w") as f:
            f.write(tb_top_content)
        
        # Generate compilation script
        compile_script = self._get_compile_script(self.target_simulator, "vip_standalone")
        with open(os.path.join(env_path, "scripts", "compile.sh"), "w") as f:
            f.write(compile_script)
        os.chmod(os.path.join(env_path, "scripts", "compile.sh"), 0o755)
        
        # Generate filelist
        filelist_content = self._get_filelist_template("vip_standalone")
        with open(os.path.join(env_path, "scripts", "filelist.f"), "w") as f:
            f.write(filelist_content)
        
        # Generate run script
        run_script = self._get_run_script(self.target_simulator, "vip_standalone")
        with open(os.path.join(env_path, "scripts", "run_test.sh"), "w") as f:
            f.write(run_script)
        os.chmod(os.path.join(env_path, "scripts", "run_test.sh"), 0o755)
        
        # Generate example test
        if self.include_tests:
            test_content = self._get_example_test_template("vip_standalone")
            with open(os.path.join(env_path, "tb", "tests", "axi4_standalone_test.sv"), "w") as f:
                f.write(test_content)
        
        # Generate documentation
        if self.include_docs:
            doc_content = self._get_documentation_template("vip_standalone")
            with open(os.path.join(env_path, "docs", "README.md"), "w") as f:
                f.write(doc_content)
        
        # Export current configuration
        config_data = {
            "mode": "vip_standalone",
            "bus_type": self.gui.current_config.bus_type,
            "data_width": self.gui.current_config.data_width,
            "addr_width": self.gui.current_config.addr_width,
            "masters": [asdict(m) for m in self.gui.current_config.masters],
            "slaves": [asdict(s) for s in self.gui.current_config.slaves]
        }
        
        with open(os.path.join(env_path, "configs", "bus_config.json"), "w") as f:
            json.dump(config_data, f, indent=2)
    
    def _get_rtl_tb_top_template(self):
        """Get RTL integration testbench template using tim_axi4_vip"""
        masters = self.gui.current_config.masters
        slaves = self.gui.current_config.slaves
        id_width = masters[0].id_width if masters else 4
        data_width = self.gui.current_config.data_width
        addr_width = self.gui.current_config.addr_width
        num_masters = len(masters)
        num_slaves = len(slaves)
        
        return f'''`timescale 1ns/1ps

import axi4_globals_pkg::*;
import axi4_master_pkg::*;
import axi4_slave_pkg::*;
import axi4_master_seq_pkg::*;
import axi4_slave_seq_pkg::*;
import axi4_env_pkg::*;
import axi4_test_pkg::*;
import uvm_pkg::*;

module top_tb;

    // Clock and reset
    logic clk;
    logic rst_n;
    
    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;
    
    // Reset generation
    initial begin
        rst_n = 0;
        repeat(10) @(posedge clk);
        rst_n = 1;
    end
    
    // AXI4 interface instance from tim_axi4_vip
    axi4_if #(
        .AXI4_ADDRESS_WIDTH({addr_width}),
        .AXI4_RDATA_WIDTH({data_width}),
        .AXI4_WDATA_WIDTH({data_width}),
        .AXI4_ID_WIDTH({id_width}),
        .AXI4_USER_WIDTH(1)
    ) dut_if (
        .clk(clk),
        .resetn(rst_n)
    );
    
    // Master and Slave BFM instantiation
    axi4_master_agent_bfm #(.MASTER_ID(0)) master_bfm(dut_if);
    axi4_slave_agent_bfm #(.SLAVE_ID(0)) slave_bfm(dut_if);
    
    // DUT wrapper instantiation
    dut_wrapper #(
        .ADDR_WIDTH({addr_width}),
        .DATA_WIDTH({data_width}),
        .ID_WIDTH({id_width})
    ) dut_inst (
        .clk(clk),
        .rst_n(rst_n),
        .axi_if(dut_if)
    );
    
    // UVM test harness
    initial begin
        // Configure number of masters and slaves
        uvm_config_db#(int)::set(null, "*", "no_of_masters", {num_masters});
        uvm_config_db#(int)::set(null, "*", "no_of_slaves", {num_slaves});
        
        // Register interface with UVM config DB
        uvm_config_db#(virtual axi4_if)::set(null, "*", "vif", dut_if);
        
        // Register BFMs
        uvm_config_db#(axi4_master_agent_bfm)::set(null, "*master_agent*", "master_agent_bfm", master_bfm);
        uvm_config_db#(axi4_slave_agent_bfm)::set(null, "*slave_agent*", "slave_agent_bfm", slave_bfm);
        
        // Run UVM test
        run_test();
    end
    
endmodule
'''
    
    def _get_standalone_tb_top_template(self):
        """Get VIP standalone testbench template using tim_axi4_vip"""
        masters = self.gui.current_config.masters
        slaves = self.gui.current_config.slaves
        id_width = masters[0].id_width if masters else 4
        data_width = self.gui.current_config.data_width
        addr_width = self.gui.current_config.addr_width
        num_masters = len(masters)
        num_slaves = len(slaves)
        
        return f'''`timescale 1ns/1ps

import axi4_globals_pkg::*;
import axi4_master_pkg::*;
import axi4_slave_pkg::*;
import axi4_master_seq_pkg::*;
import axi4_slave_seq_pkg::*;
import axi4_env_pkg::*;
import axi4_test_pkg::*;
import uvm_pkg::*;

module top_tb;

    // Clock and reset
    logic clk;
    logic rst_n;
    
    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;
    
    // Reset generation
    initial begin
        rst_n = 0;
        repeat(10) @(posedge clk);
        rst_n = 1;
    end
    
    // AXI4 interface instance from tim_axi4_vip
    axi4_if #(
        .AXI4_ADDRESS_WIDTH({addr_width}),
        .AXI4_RDATA_WIDTH({data_width}),
        .AXI4_WDATA_WIDTH({data_width}),
        .AXI4_ID_WIDTH({id_width}),
        .AXI4_USER_WIDTH(1)
    ) test_if (
        .clk(clk),
        .resetn(rst_n)
    );
    
    // Master and Slave BFM instantiation for standalone mode
    axi4_master_agent_bfm #(.MASTER_ID(0)) master_bfm(test_if);
    axi4_slave_agent_bfm #(.SLAVE_ID(0)) slave_bfm(test_if);
    
    // Bind assertions to interface
    bind test_if master_assertions u_master_assertions(.*);
    bind test_if slave_assertions u_slave_assertions(.*);
    
    // UVM test harness
    initial begin
        // Configure number of masters and slaves
        uvm_config_db#(int)::set(null, "*", "no_of_masters", {num_masters});
        uvm_config_db#(int)::set(null, "*", "no_of_slaves", {num_slaves});
        
        // Register interface with UVM config DB
        uvm_config_db#(virtual axi4_if)::set(null, "*", "vif", test_if);
        
        // Register BFMs
        uvm_config_db#(axi4_master_agent_bfm)::set(null, "*master_agent*", "master_agent_bfm", master_bfm);
        uvm_config_db#(axi4_slave_agent_bfm)::set(null, "*slave_agent*", "slave_agent_bfm", slave_bfm);
        
        // Configure for standalone mode with memory model
        uvm_config_db#(bit)::set(null, "*slave*", "slave_memory_mode_enable", 1'b1);
        
        // Run UVM test
        run_test();
    end
    
endmodule
'''
    
    def _get_filelist_template(self, mode):
        """Generate filelist for compilation"""
        if mode == "rtl_integration":
            return '''// Filelist for RTL Integration Mode with tim_axi4_vip

// Include directories
+incdir+./tim_axi4_vip/include
+incdir+./tim_axi4_vip/intf
+incdir+./tim_axi4_vip/master
+incdir+./tim_axi4_vip/slave
+incdir+./tim_axi4_vip/seq/master_sequences
+incdir+./tim_axi4_vip/seq/slave_sequences

// Package files (order matters)
./tim_axi4_vip/pkg/axi4_globals_pkg.sv
./tim_axi4_vip/master/axi4_master_pkg.sv
./tim_axi4_vip/slave/axi4_slave_pkg.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_seq_pkg.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_seq_pkg.sv
./tim_axi4_vip/test/axi4_test_pkg.sv

// Interface
./tim_axi4_vip/intf/axi4_interface/axi4_if.sv

// BFM modules (Bus Functional Models)
./tim_axi4_vip/agent/master_agent_bfm/axi4_master_driver_bfm.sv
./tim_axi4_vip/agent/master_agent_bfm/axi4_master_monitor_bfm.sv
./tim_axi4_vip/agent/master_agent_bfm/axi4_master_agent_bfm.sv
./tim_axi4_vip/agent/slave_agent_bfm/axi4_slave_driver_bfm.sv
./tim_axi4_vip/agent/slave_agent_bfm/axi4_slave_monitor_bfm.sv
./tim_axi4_vip/agent/slave_agent_bfm/axi4_slave_agent_bfm.sv

// Assertions
./tim_axi4_vip/assertions/master_assertions.sv
./tim_axi4_vip/assertions/slave_assertions.sv

// Master components
./tim_axi4_vip/master/axi4_master_agent_config.sv
./tim_axi4_vip/master/axi4_master_tx.sv
./tim_axi4_vip/master/axi4_master_seq_item_converter.sv
./tim_axi4_vip/master/axi4_master_cfg_converter.sv
./tim_axi4_vip/master/axi4_master_write_sequencer.sv
./tim_axi4_vip/master/axi4_master_read_sequencer.sv
./tim_axi4_vip/master/axi4_master_monitor_proxy.sv
./tim_axi4_vip/master/axi4_master_driver_proxy.sv
./tim_axi4_vip/master/axi4_master_coverage.sv
./tim_axi4_vip/master/axi4_master_agent.sv

// Slave components
./tim_axi4_vip/slave/axi4_slave_agent_config.sv
./tim_axi4_vip/slave/axi4_slave_tx.sv
./tim_axi4_vip/slave/axi4_slave_seq_item_converter.sv
./tim_axi4_vip/slave/axi4_slave_cfg_converter.sv
./tim_axi4_vip/slave/axi4_slave_write_sequencer.sv
./tim_axi4_vip/slave/axi4_slave_read_sequencer.sv
./tim_axi4_vip/slave/axi4_slave_monitor_proxy.sv
./tim_axi4_vip/slave/axi4_slave_driver_proxy.sv
./tim_axi4_vip/slave/axi4_slave_memory.sv
./tim_axi4_vip/slave/axi4_slave_coverage.sv
./tim_axi4_vip/slave/axi4_slave_agent.sv

// Base sequences
./tim_axi4_vip/seq/master_sequences/axi4_master_base_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_bk_base_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_nbk_base_seq.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_base_seq.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_bk_base_seq.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_nbk_base_seq.sv

// Basic sequences for testing
./tim_axi4_vip/seq/master_sequences/axi4_master_write_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_read_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_bk_write_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_bk_read_seq.sv

// Virtual sequences and sequencer
./tim_axi4_vip/virtual_seqr/axi4_virtual_sequencer.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_seq_pkg.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_base_seq.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_write_seq.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_read_seq.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_write_read_seq.sv

// Environment package and components
./tim_axi4_vip/env/axi4_env_pkg.sv
./tim_axi4_vip/env/axi4_env_config.sv
./tim_axi4_vip/env/axi4_scoreboard.sv
./tim_axi4_vip/env/axi4_protocol_coverage.sv
./tim_axi4_vip/env/axi4_env.sv

// Test base class
./tim_axi4_vip/test/axi4_base_test.sv

// RTL wrapper
./rtl_wrapper/dut_wrapper.sv

// Add your RTL files here
// ./rtl_wrapper/your_dut.sv

// HDL top and HVL top
./tim_axi4_vip/top/hdl_top.sv
./tim_axi4_vip/top/hvl_top.sv

// Testbench top
./tb/top_tb.sv

// Test files
./tb/tests/axi4_rtl_basic_test.sv
'''
        else:  # vip_standalone
            return '''// Filelist for VIP Standalone Mode with tim_axi4_vip

// Include directories
+incdir+./tim_axi4_vip/include
+incdir+./tim_axi4_vip/intf
+incdir+./tim_axi4_vip/master
+incdir+./tim_axi4_vip/slave
+incdir+./tim_axi4_vip/seq/master_sequences
+incdir+./tim_axi4_vip/seq/slave_sequences

// Package files (order matters)
./tim_axi4_vip/pkg/axi4_globals_pkg.sv
./tim_axi4_vip/master/axi4_master_pkg.sv
./tim_axi4_vip/slave/axi4_slave_pkg.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_seq_pkg.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_seq_pkg.sv
./tim_axi4_vip/test/axi4_test_pkg.sv

// Interface
./tim_axi4_vip/intf/axi4_interface/axi4_if.sv

// BFM modules (Bus Functional Models)
./tim_axi4_vip/agent/master_agent_bfm/axi4_master_driver_bfm.sv
./tim_axi4_vip/agent/master_agent_bfm/axi4_master_monitor_bfm.sv
./tim_axi4_vip/agent/master_agent_bfm/axi4_master_agent_bfm.sv
./tim_axi4_vip/agent/slave_agent_bfm/axi4_slave_driver_bfm.sv
./tim_axi4_vip/agent/slave_agent_bfm/axi4_slave_monitor_bfm.sv
./tim_axi4_vip/agent/slave_agent_bfm/axi4_slave_agent_bfm.sv

// Assertions
./tim_axi4_vip/assertions/master_assertions.sv
./tim_axi4_vip/assertions/slave_assertions.sv

// Master components
./tim_axi4_vip/master/axi4_master_agent_config.sv
./tim_axi4_vip/master/axi4_master_tx.sv
./tim_axi4_vip/master/axi4_master_seq_item_converter.sv
./tim_axi4_vip/master/axi4_master_cfg_converter.sv
./tim_axi4_vip/master/axi4_master_write_sequencer.sv
./tim_axi4_vip/master/axi4_master_read_sequencer.sv
./tim_axi4_vip/master/axi4_master_monitor_proxy.sv
./tim_axi4_vip/master/axi4_master_driver_proxy.sv
./tim_axi4_vip/master/axi4_master_coverage.sv
./tim_axi4_vip/master/axi4_master_agent.sv

// Slave components
./tim_axi4_vip/slave/axi4_slave_agent_config.sv
./tim_axi4_vip/slave/axi4_slave_tx.sv
./tim_axi4_vip/slave/axi4_slave_seq_item_converter.sv
./tim_axi4_vip/slave/axi4_slave_cfg_converter.sv
./tim_axi4_vip/slave/axi4_slave_write_sequencer.sv
./tim_axi4_vip/slave/axi4_slave_read_sequencer.sv
./tim_axi4_vip/slave/axi4_slave_monitor_proxy.sv
./tim_axi4_vip/slave/axi4_slave_driver_proxy.sv
./tim_axi4_vip/slave/axi4_slave_memory.sv
./tim_axi4_vip/slave/axi4_slave_coverage.sv
./tim_axi4_vip/slave/axi4_slave_agent.sv

// Base sequences
./tim_axi4_vip/seq/master_sequences/axi4_master_base_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_bk_base_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_nbk_base_seq.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_base_seq.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_bk_base_seq.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_nbk_base_seq.sv

// Basic sequences for testing
./tim_axi4_vip/seq/master_sequences/axi4_master_write_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_read_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_bk_write_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_bk_read_seq.sv

// Virtual sequences and sequencer
./tim_axi4_vip/virtual_seqr/axi4_virtual_sequencer.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_seq_pkg.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_base_seq.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_write_seq.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_read_seq.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_write_read_seq.sv

// Environment package and components
./tim_axi4_vip/env/axi4_env_pkg.sv
./tim_axi4_vip/env/axi4_env_config.sv
./tim_axi4_vip/env/axi4_scoreboard.sv
./tim_axi4_vip/env/axi4_protocol_coverage.sv
./tim_axi4_vip/env/axi4_env.sv

// Test base class
./tim_axi4_vip/test/axi4_base_test.sv

// Include some basic tests from tim_axi4_vip
./tim_axi4_vip/test/axi4_write_test.sv
./tim_axi4_vip/test/axi4_read_test.sv
./tim_axi4_vip/test/axi4_write_read_test.sv
./tim_axi4_vip/test/axi4_blocking_write_read_test.sv

// HDL top and HVL top
./tim_axi4_vip/top/hdl_top.sv
./tim_axi4_vip/top/hvl_top.sv

// Testbench top
./tb/top_tb.sv

// Test files
./tb/tests/axi4_standalone_test.sv
'''
    
    def _get_generated_rtl_wrapper_template(self):
        """Get RTL wrapper template for tool-generated RTL with full automation"""
        masters = self.gui.current_config.masters
        slaves = self.gui.current_config.slaves
        id_width = masters[0].id_width if masters else 4
        data_width = self.gui.current_config.data_width
        addr_width = self.gui.current_config.addr_width
        bus_type = self.gui.current_config.bus_type
        
        # For tool-generated RTL, we know the exact module name and ports
        num_masters = len(masters)
        num_slaves = len(slaves)
        module_name = f"axi4_interconnect_m{num_masters}s{num_slaves}"
        
        wrapper = f'''// Auto-generated RTL Wrapper for Tool-Generated {bus_type} Interconnect
// This wrapper connects tim_axi4_vip to the generated RTL interconnect
// Configuration: {num_masters} Masters, {num_slaves} Slaves

module dut_wrapper #(
    parameter ADDR_WIDTH = {addr_width},
    parameter DATA_WIDTH = {data_width},
    parameter ID_WIDTH   = {id_width}
) (
    input  logic clk,
    input  logic rst_n,
    axi4_if.slave axi_if  // tim_axi4_vip interface
);

'''
        
        # Add internal signals for additional masters (if more than 1)
        if num_masters > 1:
            wrapper += "    // Internal signals for additional masters\n"
            for i in range(1, num_masters):
                wrapper += f"    // Master {i} signals (terminated)\n"
                wrapper += self._generate_master_signals(i, data_width, addr_width, id_width)
                wrapper += "\n"
        
        # Add internal signals for all slaves
        wrapper += "    // Internal signals for slave interfaces\n"
        for i in range(num_slaves):
            wrapper += f"    // Slave {i} signals\n"
            wrapper += self._generate_slave_signals(i, data_width, addr_width, id_width)
            wrapper += "\n"
        
        wrapper += f'''    // =========================================
    // INTERCONNECT INSTANTIATION
    // =========================================
    
    {module_name} #(
        .DATA_WIDTH({data_width}),
        .ADDR_WIDTH({addr_width}),
        .ID_WIDTH({id_width}),
        .USER_WIDTH(1)
    ) generated_interconnect (
        // Clock and Reset
        .aclk(clk),
        .aresetn(rst_n),
        
        // Master 0 Interface (connected to VIP)
'''
        
        # Connect master 0 to VIP
        wrapper += self._generate_master_connections(0, "axi_if")
        
        # Connect/terminate other masters
        for i in range(1, num_masters):
            wrapper += f"\n        // Master {i} Interface (terminated)\n"
            wrapper += self._generate_master_connections(i, f"m{i}")
        
        # Connect all slaves
        for i in range(num_slaves):
            wrapper += f"\n        // Slave {i} Interface\n"
            wrapper += self._generate_slave_connections(i, f"s{i}")
        
        # Remove trailing comma and close
        wrapper = wrapper.rstrip(",\n") + "\n    );\n"
        
        # Add slave termination logic
        wrapper += self._generate_slave_termination_logic(slaves)
        
        wrapper += '''\n    // =========================================
    // AUTO-GENERATED WRAPPER
    // =========================================
    // This wrapper was automatically generated for the
    // tool-generated interconnect with proper connections
    // for all masters and slaves.
    
endmodule
'''
        
        return wrapper
    
    def _generate_master_signals(self, idx, data_width, addr_width, id_width):
        """Generate internal signal declarations for a master"""
        return f'''    logic [{id_width-1}:0]    m{idx}_awid;
    logic [{addr_width-1}:0]  m{idx}_awaddr;
    logic [7:0]              m{idx}_awlen;
    logic [2:0]              m{idx}_awsize;
    logic [1:0]              m{idx}_awburst;
    logic                    m{idx}_awlock;
    logic [3:0]              m{idx}_awcache;
    logic [2:0]              m{idx}_awprot;
    logic [3:0]              m{idx}_awqos;
    logic                    m{idx}_awvalid;
    logic                    m{idx}_awready;
    
    logic [{data_width-1}:0]  m{idx}_wdata;
    logic [{data_width/8-1}:0] m{idx}_wstrb;
    logic                    m{idx}_wlast;
    logic                    m{idx}_wvalid;
    logic                    m{idx}_wready;
    
    logic [{id_width-1}:0]    m{idx}_bid;
    logic [1:0]              m{idx}_bresp;
    logic                    m{idx}_bvalid;
    logic                    m{idx}_bready;
    
    logic [{id_width-1}:0]    m{idx}_arid;
    logic [{addr_width-1}:0]  m{idx}_araddr;
    logic [7:0]              m{idx}_arlen;
    logic [2:0]              m{idx}_arsize;
    logic [1:0]              m{idx}_arburst;
    logic                    m{idx}_arlock;
    logic [3:0]              m{idx}_arcache;
    logic [2:0]              m{idx}_arprot;
    logic [3:0]              m{idx}_arqos;
    logic                    m{idx}_arvalid;
    logic                    m{idx}_arready;
    
    logic [{id_width-1}:0]    m{idx}_rid;
    logic [{data_width-1}:0]  m{idx}_rdata;
    logic [1:0]              m{idx}_rresp;
    logic                    m{idx}_rlast;
    logic                    m{idx}_rvalid;
    logic                    m{idx}_rready;'''
    
    def _generate_slave_signals(self, idx, data_width, addr_width, id_width):
        """Generate internal signal declarations for a slave"""
        return f'''    logic [{id_width-1}:0]    s{idx}_awid;
    logic [{addr_width-1}:0]  s{idx}_awaddr;
    logic [7:0]              s{idx}_awlen;
    logic [2:0]              s{idx}_awsize;
    logic [1:0]              s{idx}_awburst;
    logic                    s{idx}_awlock;
    logic [3:0]              s{idx}_awcache;
    logic [2:0]              s{idx}_awprot;
    logic [3:0]              s{idx}_awqos;
    logic                    s{idx}_awvalid;
    logic                    s{idx}_awready;
    
    logic [{data_width-1}:0]  s{idx}_wdata;
    logic [{data_width/8-1}:0] s{idx}_wstrb;
    logic                    s{idx}_wlast;
    logic                    s{idx}_wvalid;
    logic                    s{idx}_wready;
    
    logic [{id_width-1}:0]    s{idx}_bid;
    logic [1:0]              s{idx}_bresp;
    logic                    s{idx}_bvalid;
    logic                    s{idx}_bready;
    
    logic [{id_width-1}:0]    s{idx}_arid;
    logic [{addr_width-1}:0]  s{idx}_araddr;
    logic [7:0]              s{idx}_arlen;
    logic [2:0]              s{idx}_arsize;
    logic [1:0]              s{idx}_arburst;
    logic                    s{idx}_arlock;
    logic [3:0]              s{idx}_arcache;
    logic [2:0]              s{idx}_arprot;
    logic [3:0]              s{idx}_arqos;
    logic                    s{idx}_arvalid;
    logic                    s{idx}_arready;
    
    logic [{id_width-1}:0]    s{idx}_rid;
    logic [{data_width-1}:0]  s{idx}_rdata;
    logic [1:0]              s{idx}_rresp;
    logic                    s{idx}_rlast;
    logic                    s{idx}_rvalid;
    logic                    s{idx}_rready;'''
    
    def _generate_master_connections(self, idx, signal_prefix):
        """Generate master port connections"""
        if signal_prefix == "axi_if":
            # Direct connection to VIP interface
            return f'''        .m{idx}_awid({signal_prefix}.awid),
        .m{idx}_awaddr({signal_prefix}.awaddr),
        .m{idx}_awlen({signal_prefix}.awlen),
        .m{idx}_awsize({signal_prefix}.awsize),
        .m{idx}_awburst({signal_prefix}.awburst),
        .m{idx}_awlock({signal_prefix}.awlock),
        .m{idx}_awcache({signal_prefix}.awcache),
        .m{idx}_awprot({signal_prefix}.awprot),
        .m{idx}_awqos({signal_prefix}.awqos),
        .m{idx}_awvalid({signal_prefix}.awvalid),
        .m{idx}_awready({signal_prefix}.awready),
        
        .m{idx}_wdata({signal_prefix}.wdata),
        .m{idx}_wstrb({signal_prefix}.wstrb),
        .m{idx}_wlast({signal_prefix}.wlast),
        .m{idx}_wvalid({signal_prefix}.wvalid),
        .m{idx}_wready({signal_prefix}.wready),
        
        .m{idx}_bid({signal_prefix}.bid),
        .m{idx}_bresp({signal_prefix}.bresp),
        .m{idx}_bvalid({signal_prefix}.bvalid),
        .m{idx}_bready({signal_prefix}.bready),
        
        .m{idx}_arid({signal_prefix}.arid),
        .m{idx}_araddr({signal_prefix}.araddr),
        .m{idx}_arlen({signal_prefix}.arlen),
        .m{idx}_arsize({signal_prefix}.arsize),
        .m{idx}_arburst({signal_prefix}.arburst),
        .m{idx}_arlock({signal_prefix}.arlock),
        .m{idx}_arcache({signal_prefix}.arcache),
        .m{idx}_arprot({signal_prefix}.arprot),
        .m{idx}_arqos({signal_prefix}.arqos),
        .m{idx}_arvalid({signal_prefix}.arvalid),
        .m{idx}_arready({signal_prefix}.arready),
        
        .m{idx}_rid({signal_prefix}.rid),
        .m{idx}_rdata({signal_prefix}.rdata),
        .m{idx}_rresp({signal_prefix}.rresp),
        .m{idx}_rlast({signal_prefix}.rlast),
        .m{idx}_rvalid({signal_prefix}.rvalid),
        .m{idx}_rready({signal_prefix}.rready),'''
        else:
            # Connection to internal signals
            return f'''        .m{idx}_awid({signal_prefix}_awid),
        .m{idx}_awaddr({signal_prefix}_awaddr),
        .m{idx}_awlen({signal_prefix}_awlen),
        .m{idx}_awsize({signal_prefix}_awsize),
        .m{idx}_awburst({signal_prefix}_awburst),
        .m{idx}_awlock({signal_prefix}_awlock),
        .m{idx}_awcache({signal_prefix}_awcache),
        .m{idx}_awprot({signal_prefix}_awprot),
        .m{idx}_awqos({signal_prefix}_awqos),
        .m{idx}_awvalid({signal_prefix}_awvalid),
        .m{idx}_awready({signal_prefix}_awready),
        
        .m{idx}_wdata({signal_prefix}_wdata),
        .m{idx}_wstrb({signal_prefix}_wstrb),
        .m{idx}_wlast({signal_prefix}_wlast),
        .m{idx}_wvalid({signal_prefix}_wvalid),
        .m{idx}_wready({signal_prefix}_wready),
        
        .m{idx}_bid({signal_prefix}_bid),
        .m{idx}_bresp({signal_prefix}_bresp),
        .m{idx}_bvalid({signal_prefix}_bvalid),
        .m{idx}_bready({signal_prefix}_bready),
        
        .m{idx}_arid({signal_prefix}_arid),
        .m{idx}_araddr({signal_prefix}_araddr),
        .m{idx}_arlen({signal_prefix}_arlen),
        .m{idx}_arsize({signal_prefix}_arsize),
        .m{idx}_arburst({signal_prefix}_arburst),
        .m{idx}_arlock({signal_prefix}_arlock),
        .m{idx}_arcache({signal_prefix}_arcache),
        .m{idx}_arprot({signal_prefix}_arprot),
        .m{idx}_arqos({signal_prefix}_arqos),
        .m{idx}_arvalid({signal_prefix}_arvalid),
        .m{idx}_arready({signal_prefix}_arready),
        
        .m{idx}_rid({signal_prefix}_rid),
        .m{idx}_rdata({signal_prefix}_rdata),
        .m{idx}_rresp({signal_prefix}_rresp),
        .m{idx}_rlast({signal_prefix}_rlast),
        .m{idx}_rvalid({signal_prefix}_rvalid),
        .m{idx}_rready({signal_prefix}_rready),'''
    
    def _generate_slave_connections(self, idx, signal_prefix):
        """Generate slave port connections"""
        return f'''        .s{idx}_awid({signal_prefix}_awid),
        .s{idx}_awaddr({signal_prefix}_awaddr),
        .s{idx}_awlen({signal_prefix}_awlen),
        .s{idx}_awsize({signal_prefix}_awsize),
        .s{idx}_awburst({signal_prefix}_awburst),
        .s{idx}_awlock({signal_prefix}_awlock),
        .s{idx}_awcache({signal_prefix}_awcache),
        .s{idx}_awprot({signal_prefix}_awprot),
        .s{idx}_awqos({signal_prefix}_awqos),
        .s{idx}_awvalid({signal_prefix}_awvalid),
        .s{idx}_awready({signal_prefix}_awready),
        
        .s{idx}_wdata({signal_prefix}_wdata),
        .s{idx}_wstrb({signal_prefix}_wstrb),
        .s{idx}_wlast({signal_prefix}_wlast),
        .s{idx}_wvalid({signal_prefix}_wvalid),
        .s{idx}_wready({signal_prefix}_wready),
        
        .s{idx}_bid({signal_prefix}_bid),
        .s{idx}_bresp({signal_prefix}_bresp),
        .s{idx}_bvalid({signal_prefix}_bvalid),
        .s{idx}_bready({signal_prefix}_bready),
        
        .s{idx}_arid({signal_prefix}_arid),
        .s{idx}_araddr({signal_prefix}_araddr),
        .s{idx}_arlen({signal_prefix}_arlen),
        .s{idx}_arsize({signal_prefix}_arsize),
        .s{idx}_arburst({signal_prefix}_arburst),
        .s{idx}_arlock({signal_prefix}_arlock),
        .s{idx}_arcache({signal_prefix}_arcache),
        .s{idx}_arprot({signal_prefix}_arprot),
        .s{idx}_arqos({signal_prefix}_arqos),
        .s{idx}_arvalid({signal_prefix}_arvalid),
        .s{idx}_arready({signal_prefix}_arready),
        
        .s{idx}_rid({signal_prefix}_rid),
        .s{idx}_rdata({signal_prefix}_rdata),
        .s{idx}_rresp({signal_prefix}_rresp),
        .s{idx}_rlast({signal_prefix}_rlast),
        .s{idx}_rvalid({signal_prefix}_rvalid),
        .s{idx}_rready({signal_prefix}_rready),'''
    
    def _generate_slave_termination_logic(self, slaves):
        """Generate slave response logic for testing"""
        if not slaves:
            return ""
            
        logic = "\n    // Slave termination logic for testing\n"
        
        for i, slave in enumerate(slaves):
            logic += f'''\n    // Slave {i} ({slave.name}) - Simple memory model
    always @(posedge clk) begin
        if (!rst_n) begin
            s{i}_awready <= 1'b0;
            s{i}_wready  <= 1'b0;
            s{i}_bvalid  <= 1'b0;
            s{i}_arready <= 1'b0;
            s{i}_rvalid  <= 1'b0;
        end else begin
            // Simple handshaking
            s{i}_awready <= 1'b1;
            s{i}_wready  <= 1'b1;
            s{i}_arready <= 1'b1;
            
            // Write response
            if (s{i}_awvalid && s{i}_awready && s{i}_wvalid && s{i}_wready && s{i}_wlast) begin
                s{i}_bvalid <= 1'b1;
                s{i}_bid    <= s{i}_awid;
                s{i}_bresp  <= 2'b00; // OKAY
            end else if (s{i}_bready && s{i}_bvalid) begin
                s{i}_bvalid <= 1'b0;
            end
            
            // Read response (single beat for now)
            if (s{i}_arvalid && s{i}_arready) begin
                s{i}_rvalid <= 1'b1;
                s{i}_rid    <= s{i}_arid;
                s{i}_rdata  <= {{{{DATA_WIDTH{{1'b0}}}}}}; // Return zeros
                s{i}_rresp  <= 2'b00; // OKAY
                s{i}_rlast  <= 1'b1;  // Single beat
            end else if (s{i}_rready && s{i}_rvalid) begin
                s{i}_rvalid <= 1'b0;
            end
        end
    end
'''
        
        # Terminate unused master signals
        num_masters = len(self.gui.current_config.masters)
        if num_masters > 1:
            logic += "\n    // Terminate unused master interfaces\n"
            for i in range(1, num_masters):
                logic += f'''    assign m{i}_awvalid = 1'b0;
    assign m{i}_wvalid  = 1'b0;
    assign m{i}_bready  = 1'b1;
    assign m{i}_arvalid = 1'b0;
    assign m{i}_rready  = 1'b1;
'''
        
        return logic
    
    def _get_rtl_wrapper_template(self):
        """Get enhanced RTL wrapper template with automated port connections"""
        masters = self.gui.current_config.masters
        id_width = masters[0].id_width if masters else 4
        data_width = self.gui.current_config.data_width
        addr_width = self.gui.current_config.addr_width
        
        return f'''// RTL Wrapper for DUT Integration
// This wrapper connects the tim_axi4_vip interface to your RTL DUT
// Requirement 3.2: Automated RTL wrapper with port connections

module dut_wrapper #(
    parameter ADDR_WIDTH = {addr_width},
    parameter DATA_WIDTH = {data_width},
    parameter ID_WIDTH   = {id_width}
) (
    input  logic clk,
    input  logic rst_n,
    axi4_if.slave axi_if  // tim_axi4_vip interface
);

    // =========================================
    // AUTOMATED DUT INSTANTIATION AND CONNECTION
    // =========================================
    // Replace 'your_axi_dut' with your actual module name
    // The tool has pre-connected all standard AXI4 signals
    
    your_axi_dut #(
        .C_S_AXI_ID_WIDTH(ID_WIDTH),
        .C_S_AXI_DATA_WIDTH(DATA_WIDTH),
        .C_S_AXI_ADDR_WIDTH(ADDR_WIDTH)
    ) dut_inst (
        // Clock and Reset
        .s_axi_aclk(clk),
        .s_axi_aresetn(rst_n),
        
        // Write Address Channel
        .s_axi_awid(axi_if.awid),
        .s_axi_awaddr(axi_if.awaddr),
        .s_axi_awlen(axi_if.awlen),
        .s_axi_awsize(axi_if.awsize),
        .s_axi_awburst(axi_if.awburst),
        .s_axi_awlock(axi_if.awlock),
        .s_axi_awcache(axi_if.awcache),
        .s_axi_awprot(axi_if.awprot),
        .s_axi_awqos(axi_if.awqos),
        .s_axi_awregion(axi_if.awregion),
        .s_axi_awuser(axi_if.awuser),
        .s_axi_awvalid(axi_if.awvalid),
        .s_axi_awready(axi_if.awready),
        
        // Write Data Channel
        .s_axi_wdata(axi_if.wdata),
        .s_axi_wstrb(axi_if.wstrb),
        .s_axi_wlast(axi_if.wlast),
        .s_axi_wuser(axi_if.wuser),
        .s_axi_wvalid(axi_if.wvalid),
        .s_axi_wready(axi_if.wready),
        
        // Write Response Channel
        .s_axi_bid(axi_if.bid),
        .s_axi_bresp(axi_if.bresp),
        .s_axi_buser(axi_if.buser),
        .s_axi_bvalid(axi_if.bvalid),
        .s_axi_bready(axi_if.bready),
        
        // Read Address Channel
        .s_axi_arid(axi_if.arid),
        .s_axi_araddr(axi_if.araddr),
        .s_axi_arlen(axi_if.arlen),
        .s_axi_arsize(axi_if.arsize),
        .s_axi_arburst(axi_if.arburst),
        .s_axi_arlock(axi_if.arlock),
        .s_axi_arcache(axi_if.arcache),
        .s_axi_arprot(axi_if.arprot),
        .s_axi_arqos(axi_if.arqos),
        .s_axi_arregion(axi_if.arregion),
        .s_axi_aruser(axi_if.aruser),
        .s_axi_arvalid(axi_if.arvalid),
        .s_axi_arready(axi_if.arready),
        
        // Read Data Channel
        .s_axi_rid(axi_if.rid),
        .s_axi_rdata(axi_if.rdata),
        .s_axi_rresp(axi_if.rresp),
        .s_axi_rlast(axi_if.rlast),
        .s_axi_ruser(axi_if.ruser),
        .s_axi_rvalid(axi_if.rvalid),
        .s_axi_rready(axi_if.rready)
    );
    
    // =========================================
    // INSTRUCTIONS FOR USE:
    // =========================================
    // 1. Replace 'your_axi_dut' with your actual module name
    // 2. Adjust parameter names if they differ from C_S_AXI_*
    // 3. Remove any signals your DUT doesn't use (e.g., user signals)
    // 4. Add any additional ports your DUT requires
    // 5. Update filelist.f to include your RTL files
    
    // =========================================
    // COMMON DUT PORT NAME MAPPINGS:
    // =========================================
    // If your DUT uses different port names, here are common variations:
    // - s_axi_aclk    → aclk, clk, ACLK
    // - s_axi_aresetn → aresetn, rst_n, ARESETn
    // - s_axi_*       → s_*, S_AXI_*, s_axi_*
    
endmodule
'''
    
    # Memory model is not needed as tim_axi4_vip includes axi4_slave_memory
    
    def _get_compile_script(self, simulator, mode):
        """Generate compilation script based on simulator"""
        if simulator == "vcs":
            return f'''#!/bin/bash
# VCS Compilation Script for {mode}

# Set environment
export VCS_HOME=$VCS_HOME

# Compile options
VCS_OPTS="-full64 -sverilog -debug_all +v2k -timescale=1ns/1ps -ntb_opts uvm"

# Compile design
vcs $VCS_OPTS \\
    -f filelist.f \\
    -o simv \\
    +define+{mode.upper()} \\
    +incdir+$VCS_HOME/etc/uvm-1.2/src \\
    $VCS_HOME/etc/uvm-1.2/src/uvm_pkg.sv

echo "Compilation complete!"
'''
        elif simulator == "questa":
            return f'''#!/bin/bash
# Questa Compilation Script for {mode}

# Create work library
vlib work

# Compile UVM
vlog -sv $QUESTA_HOME/verilog_src/uvm-1.2/src/uvm_pkg.sv

# Compile design
vlog -sv +define+{mode.upper()} \\
     +incdir+$QUESTA_HOME/verilog_src/uvm-1.2/src \\
     -f filelist.f

echo "Compilation complete!"
'''
        else:
            return f'''#!/bin/bash
# Generic Compilation Script for {mode}
echo "Please customize this script for your simulator"
'''
    
    def _get_run_script(self, simulator, mode):
        """Generate run script based on simulator"""
        if simulator == "vcs":
            return '''#!/bin/bash
# VCS Run Script

# Run simulation
./simv +UVM_TESTNAME=$1 -l sim.log

echo "Simulation complete! Check sim.log for results."
'''
        elif simulator == "questa":
            return '''#!/bin/bash
# Questa Run Script

# Run simulation
vsim -c -do "run -all; quit" top_tb +UVM_TESTNAME=$1 -l sim.log

echo "Simulation complete! Check sim.log for results."
'''
        else:
            return '''#!/bin/bash
# Generic Run Script
echo "Please customize this script for your simulator"
'''
    
    def _get_example_test_template(self, mode):
        """Generate example test based on mode using tim_axi4_vip"""
        if mode == "rtl_integration":
            return '''// Example test for RTL integration using tim_axi4_vip
// This test demonstrates basic read/write operations to your DUT

`ifndef AXI4_RTL_BASIC_TEST_SV
`define AXI4_RTL_BASIC_TEST_SV

class axi4_rtl_basic_test extends axi4_base_test;
    `uvm_component_utils(axi4_rtl_basic_test)
    
    // Virtual sequence handle
    axi4_virtual_write_read_seq virtual_seq;
    
    function new(string name = "axi4_rtl_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure test parameters
        uvm_config_db#(int)::set(this, "*", "no_of_write_trans", 10);
        uvm_config_db#(int)::set(this, "*", "no_of_read_trans", 10);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_name(), "Starting RTL integration test", UVM_LOW)
        
        // Create and start virtual sequence
        virtual_seq = axi4_virtual_write_read_seq::type_id::create("virtual_seq");
        virtual_seq.start(env.virtual_seqr);
        
        #1000ns;
        
        phase.drop_objection(this);
    endtask
    
endclass

`endif
'''
        else:
            return '''// Example test for VIP standalone mode using tim_axi4_vip
// This test uses the built-in memory model for verification

`ifndef AXI4_STANDALONE_TEST_SV
`define AXI4_STANDALONE_TEST_SV

class axi4_standalone_test extends axi4_write_read_test;
    `uvm_component_utils(axi4_standalone_test)
    
    function new(string name = "axi4_standalone_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure for memory model mode
        uvm_config_db#(bit)::set(this, "env.slave*", "slave_memory_mode_enable", 1'b1);
        
        // Set test parameters
        uvm_config_db#(int)::set(this, "*", "no_of_write_trans", 20);
        uvm_config_db#(int)::set(this, "*", "no_of_read_trans", 20);
    endfunction
    
    task run_phase(uvm_phase phase);
        `uvm_info(get_name(), "Starting VIP standalone test with memory model", UVM_LOW)
        
        // Base class handles the test execution
        super.run_phase(phase);
    endtask
    
endclass

`endif
'''
    
    def _get_documentation_template(self, mode):
        """Generate documentation template"""
        if mode == "rtl_integration":
            return f'''# RTL Integration Environment with tim_axi4_vip

This environment integrates the tim_axi4_vip (https://github.com/moonslide/tim_axi4_vip) with your RTL DUT.

## Directory Structure
- `tb/` - Testbench files
- `tb/tests/` - Test cases  
- `tim_axi4_vip/` - Symbolic link to tim_axi4_vip
- `rtl_wrapper/` - RTL wrapper with automated connections
- `scripts/` - Compilation and run scripts
- `configs/` - Configuration files

## Quick Start

1. **Add Your RTL DUT**
   - Copy your RTL files to the `rtl_wrapper/` directory
   - Edit `rtl_wrapper/dut_wrapper.sv`:
     - Replace 'your_axi_dut' with your module name
     - Adjust parameter names if needed
     - Remove unused signals (e.g., user signals)

2. **Update File List**
   - Edit `scripts/filelist.f`
   - Add your RTL files at the marked location

3. **Compile**
   ```bash
   cd scripts
   ./compile.sh
   ```

4. **Run Test**
   ```bash
   ./run_test.sh axi4_rtl_basic_test
   ```

## Available Tests
- `axi4_rtl_basic_test` - Basic read/write test
- All tests from tim_axi4_vip are available

## Configuration
- Bus Type: {self.gui.current_config.bus_type}
- Data Width: {self.gui.current_config.data_width} bits
- Address Width: {self.gui.current_config.addr_width} bits
- ID Width: {self.gui.current_config.masters[0].id_width if self.gui.current_config.masters else 4} bits
- Masters: {len(self.gui.current_config.masters)}
- Slaves: {len(self.gui.current_config.slaves)}

## Automated Features
- All AXI4 signals are pre-connected in the wrapper
- Standard parameter mappings are included
- Common port name variations are documented

## Troubleshooting
- If compilation fails, check that $VCS_HOME is set
- Ensure your DUT port names match the wrapper connections
- See tim_axi4_vip documentation for advanced features
'''
        else:
            return f'''# VIP Standalone Environment with tim_axi4_vip

This is a self-contained environment using tim_axi4_vip (https://github.com/moonslide/tim_axi4_vip) with built-in memory model.

## Directory Structure
- `tb/` - Testbench files
- `tb/tests/` - Test cases
- `tim_axi4_vip/` - Symbolic link to tim_axi4_vip
- `scripts/` - Compilation and run scripts
- `configs/` - Configuration files

## Quick Start

1. **Compile**
   ```bash
   cd scripts
   ./compile.sh
   ```

2. **Run Test**
   ```bash
   ./run_test.sh axi4_standalone_test
   ```

## Available Tests
- `axi4_standalone_test` - Basic test with memory model
- `axi4_write_read_test` - Write followed by read test
- `axi4_blocking_write_read_test` - Blocking transfers test
- All tests from tim_axi4_vip test directory

## Configuration
- Bus Type: {self.gui.current_config.bus_type}
- Data Width: {self.gui.current_config.data_width} bits
- Address Width: {self.gui.current_config.addr_width} bits
- ID Width: {self.gui.current_config.masters[0].id_width if self.gui.current_config.masters else 4} bits
- Masters: {len(self.gui.current_config.masters)}
- Slaves: {len(self.gui.current_config.slaves)}

## Features
- Uses tim_axi4_vip slave memory model
- Full protocol checking with assertions
- Coverage collection
- Extensive test library

## Running Different Tests
The tim_axi4_vip includes many pre-built tests:
```bash
# Run specific test
./run_test.sh axi4_non_blocking_write_read_test

# Run with waves
./run_test.sh axi4_standalone_test +waves
```

## Adding Custom Tests
1. Create new test in `tb/tests/`
2. Extend from `axi4_base_test`
3. Add to filelist.f
4. Run with test name
'''

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