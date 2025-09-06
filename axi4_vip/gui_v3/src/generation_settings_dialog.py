#!/usr/bin/env python3
"""
Generation Settings Dialog for AXI4 Generator
Provides comprehensive options for RTL and VIP generation
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import os
from datetime import datetime

class GenerationSettingsDialog(tk.Toplevel):
    """Dialog for configuring generation settings"""
    
    def __init__(self, parent, project_config, mode='both'):
        """
        Initialize generation settings dialog
        
        Args:
            parent: Parent window
            project_config: Current project configuration
            mode: 'rtl', 'vip', or 'both'
        """
        super().__init__(parent)
        self.parent = parent
        self.project = project_config
        self.mode = mode
        self.result = None
        
        # Configure window
        self.title("Generation Settings")
        self.geometry("900x800")  # Larger default size
        self.resizable(True, True)  # Allow user to resize
        self.minsize(800, 700)  # Minimum size to ensure usability
        
        # Make modal
        self.transient(parent)
        self.grab_set()
        
        # Create UI
        self.create_widgets()
        
        # Center window
        self.center_window()
        
    def center_window(self):
        """Center the dialog on screen"""
        self.update_idletasks()
        width = self.winfo_width()
        height = self.winfo_height()
        x = (self.winfo_screenwidth() // 2) - (width // 2)
        y = (self.winfo_screenheight() // 2) - (height // 2)
        self.geometry(f'{width}x{height}+{x}+{y}')
        
    def create_widgets(self):
        """Create all dialog widgets"""
        
        # Main container with padding
        main_frame = ttk.Frame(self, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # Top frame with title and buttons
        top_frame = ttk.Frame(main_frame)
        top_frame.pack(fill=tk.X, pady=(0, 10))
        
        # Title based on mode
        title_text = {
            'rtl': "Generate RTL",
            'vip': "Generate Verification IP",
            'both': "Generate RTL & VIP"
        }.get(self.mode, "Generate")
        
        title_label = ttk.Label(top_frame, text=title_text, 
                               font=('Arial', 16, 'bold'))
        title_label.pack(side=tk.LEFT)
        
        # Button frame at top right
        button_frame = ttk.Frame(top_frame)
        button_frame.pack(side=tk.RIGHT)
        
        # Buttons
        ttk.Button(button_frame, text="Generate", 
                  command=self.generate, width=15).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Cancel", 
                  command=self.cancel, width=15).pack(side=tk.LEFT)
        
        # Create notebook for tabs
        self.notebook = ttk.Notebook(main_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True, pady=(0, 10))
        
        # Add tabs based on mode
        if self.mode in ['rtl', 'both']:
            self.create_rtl_tab()
        if self.mode in ['vip', 'both']:
            self.create_vip_tab()
        
        # Common settings tab
        self.create_common_tab()
        
        # Output settings tab
        self.create_output_tab()
        
    def create_rtl_tab(self):
        """Create RTL generation settings tab"""
        rtl_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(rtl_frame, text="RTL Settings")
        
        # RTL Options
        options_frame = ttk.LabelFrame(rtl_frame, text="RTL Generation Options", padding="10")
        options_frame.pack(fill=tk.X, pady=(0, 10))
        
        # Checkboxes for RTL options
        self.rtl_gen_interconnect = tk.BooleanVar(value=True)
        ttk.Checkbutton(options_frame, text="Generate Interconnect", 
                       variable=self.rtl_gen_interconnect).pack(anchor='w', pady=2)
        
        self.rtl_gen_bridges = tk.BooleanVar(value=True)
        ttk.Checkbutton(options_frame, text="Generate Bridge Components", 
                       variable=self.rtl_gen_bridges).pack(anchor='w', pady=2)
        
        self.rtl_gen_cdc = tk.BooleanVar(value=True)
        ttk.Checkbutton(options_frame, text="Generate CDC Logic", 
                       variable=self.rtl_gen_cdc).pack(anchor='w', pady=2)
        
        self.rtl_gen_default_slave = tk.BooleanVar(value=True)
        ttk.Checkbutton(options_frame, text="Include Default Slave", 
                       variable=self.rtl_gen_default_slave).pack(anchor='w', pady=2)
        
        self.rtl_gen_assertions = tk.BooleanVar(value=False)
        ttk.Checkbutton(options_frame, text="Include Assertions", 
                       variable=self.rtl_gen_assertions).pack(anchor='w', pady=2)
        
        # Advanced RTL Settings
        advanced_frame = ttk.LabelFrame(rtl_frame, text="Advanced Settings", padding="10")
        advanced_frame.pack(fill=tk.X, pady=(0, 10))
        
        # Pipeline stages
        row = 0
        ttk.Label(advanced_frame, text="Pipeline Stages:").grid(row=row, column=0, sticky='w', pady=2)
        self.rtl_pipeline_stages = tk.Spinbox(advanced_frame, from_=0, to=5, width=10)
        self.rtl_pipeline_stages.delete(0, 'end')
        self.rtl_pipeline_stages.insert(0, '1')
        self.rtl_pipeline_stages.grid(row=row, column=1, sticky='w', pady=2)
        
        # Arbitration scheme
        row += 1
        ttk.Label(advanced_frame, text="Arbitration:").grid(row=row, column=0, sticky='w', pady=2)
        self.rtl_arbitration = ttk.Combobox(advanced_frame, values=['round_robin', 'fixed_priority', 
                                                                    'weighted', 'qos_based'], width=15)
        self.rtl_arbitration.set('round_robin')
        self.rtl_arbitration.grid(row=row, column=1, sticky='w', pady=2)
        
        # Outstanding transactions
        row += 1
        ttk.Label(advanced_frame, text="Max Outstanding:").grid(row=row, column=0, sticky='w', pady=2)
        self.rtl_max_outstanding = tk.Spinbox(advanced_frame, from_=1, to=32, width=10)
        self.rtl_max_outstanding.delete(0, 'end')
        self.rtl_max_outstanding.insert(0, '8')
        self.rtl_max_outstanding.grid(row=row, column=1, sticky='w', pady=2)
        
        # Optimization level
        row += 1
        ttk.Label(advanced_frame, text="Optimization:").grid(row=row, column=0, sticky='w', pady=2)
        self.rtl_optimization = ttk.Combobox(advanced_frame, values=['area', 'speed', 'balanced'], width=15)
        self.rtl_optimization.set('balanced')
        self.rtl_optimization.grid(row=row, column=1, sticky='w', pady=2)
        
    def create_vip_tab(self):
        """Create VIP generation settings tab"""
        vip_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(vip_frame, text="VIP Settings")
        
        # VIP Components
        components_frame = ttk.LabelFrame(vip_frame, text="VIP Components", padding="10")
        components_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.vip_gen_master_agent = tk.BooleanVar(value=True)
        ttk.Checkbutton(components_frame, text="Generate Master Agents", 
                       variable=self.vip_gen_master_agent).pack(anchor='w', pady=2)
        
        self.vip_gen_slave_agent = tk.BooleanVar(value=True)
        ttk.Checkbutton(components_frame, text="Generate Slave Agents", 
                       variable=self.vip_gen_slave_agent).pack(anchor='w', pady=2)
        
        self.vip_gen_monitor = tk.BooleanVar(value=True)
        ttk.Checkbutton(components_frame, text="Generate Monitor", 
                       variable=self.vip_gen_monitor).pack(anchor='w', pady=2)
        
        self.vip_gen_scoreboard = tk.BooleanVar(value=True)
        ttk.Checkbutton(components_frame, text="Generate Scoreboard", 
                       variable=self.vip_gen_scoreboard).pack(anchor='w', pady=2)
        
        self.vip_gen_coverage = tk.BooleanVar(value=True)
        ttk.Checkbutton(components_frame, text="Generate Coverage", 
                       variable=self.vip_gen_coverage).pack(anchor='w', pady=2)
        
        # Test Settings
        test_frame = ttk.LabelFrame(vip_frame, text="Test Generation", padding="10")
        test_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.vip_gen_base_test = tk.BooleanVar(value=True)
        ttk.Checkbutton(test_frame, text="Base Test", 
                       variable=self.vip_gen_base_test).pack(anchor='w', pady=2)
        
        self.vip_gen_random_test = tk.BooleanVar(value=True)
        ttk.Checkbutton(test_frame, text="Random Test", 
                       variable=self.vip_gen_random_test).pack(anchor='w', pady=2)
        
        self.vip_gen_directed_test = tk.BooleanVar(value=True)
        ttk.Checkbutton(test_frame, text="Directed Tests", 
                       variable=self.vip_gen_directed_test).pack(anchor='w', pady=2)
        
        self.vip_gen_stress_test = tk.BooleanVar(value=False)
        ttk.Checkbutton(test_frame, text="Stress Tests", 
                       variable=self.vip_gen_stress_test).pack(anchor='w', pady=2)
        
        # Sequences
        seq_frame = ttk.LabelFrame(vip_frame, text="Sequence Library", padding="10")
        seq_frame.pack(fill=tk.X)
        
        row = 0
        ttk.Label(seq_frame, text="Master Sequences:").grid(row=row, column=0, sticky='w', pady=2)
        self.vip_master_seq_count = tk.Spinbox(seq_frame, from_=5, to=50, width=10)
        self.vip_master_seq_count.delete(0, 'end')
        self.vip_master_seq_count.insert(0, '20')
        self.vip_master_seq_count.grid(row=row, column=1, sticky='w', pady=2)
        
        row += 1
        ttk.Label(seq_frame, text="Slave Sequences:").grid(row=row, column=0, sticky='w', pady=2)
        self.vip_slave_seq_count = tk.Spinbox(seq_frame, from_=5, to=50, width=10)
        self.vip_slave_seq_count.delete(0, 'end')
        self.vip_slave_seq_count.insert(0, '20')
        self.vip_slave_seq_count.grid(row=row, column=1, sticky='w', pady=2)
        
    def create_common_tab(self):
        """Create common settings tab"""
        common_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(common_frame, text="Common Settings")
        
        # Bus Configuration
        bus_frame = ttk.LabelFrame(common_frame, text="Bus Configuration", padding="10")
        bus_frame.pack(fill=tk.X, pady=(0, 10))
        
        row = 0
        ttk.Label(bus_frame, text="Data Width:").grid(row=row, column=0, sticky='w', pady=2)
        self.data_width = ttk.Combobox(bus_frame, values=['8', '16', '32', '64', '128', '256', '512', '1024'], width=10)
        # Get value from parent's start panel instead of project config
        data_width_value = self.parent.data_width_var.get() if hasattr(self.parent, 'data_width_var') else str(self.project.bus.data_width)
        self.data_width.set(data_width_value)
        self.data_width.grid(row=row, column=1, sticky='w', pady=2)
        
        row += 1
        ttk.Label(bus_frame, text="Address Width:").grid(row=row, column=0, sticky='w', pady=2)
        addr_frame = ttk.Frame(bus_frame)
        addr_frame.grid(row=row, column=1, sticky='w', pady=2)
        self.addr_width = tk.Spinbox(addr_frame, from_=8, to=64, width=10)
        self.addr_width.delete(0, 'end')
        # Get value from parent's start panel instead of project config
        addr_width_value = self.parent.addr_width_var.get() if hasattr(self.parent, 'addr_width_var') else str(self.project.bus.addr_width)
        self.addr_width.insert(0, addr_width_value)
        self.addr_width.pack(side='left')
        ttk.Label(addr_frame, text="bits (8-64)", font=('Arial', 9)).pack(side='left', padx=(5, 0))
        
        row += 1
        ttk.Label(bus_frame, text="ID Width:").grid(row=row, column=0, sticky='w', pady=2)
        self.id_width = tk.Spinbox(bus_frame, from_=1, to=16, width=10)
        self.id_width.delete(0, 'end')
        # Get value from parent's start panel instead of project config
        id_width_value = self.parent.id_width_var.get() if hasattr(self.parent, 'id_width_var') else str(self.project.bus.id_width)
        self.id_width.insert(0, id_width_value)
        self.id_width.grid(row=row, column=1, sticky='w', pady=2)
        
        row += 1
        ttk.Label(bus_frame, text="User Width:").grid(row=row, column=0, sticky='w', pady=2)
        self.user_width = tk.Spinbox(bus_frame, from_=0, to=256, width=10)
        self.user_width.delete(0, 'end')
        # Get value from parent's start panel instead of project config
        user_width_value = self.parent.user_width_var.get() if hasattr(self.parent, 'user_width_var') else str(self.project.bus.user_width)
        self.user_width.insert(0, user_width_value)
        self.user_width.grid(row=row, column=1, sticky='w', pady=2)
        
        row += 1
        ttk.Label(bus_frame, text="Burst Length:").grid(row=row, column=0, sticky='w', pady=2)
        burst_frame = ttk.Frame(bus_frame)
        burst_frame.grid(row=row, column=1, sticky='w', pady=2)
        self.burst_length = tk.Spinbox(burst_frame, from_=1, to=256, width=10)
        self.burst_length.delete(0, 'end')
        # Get value from parent's start panel instead of project config
        burst_length_value = self.parent.burst_length_var.get() if hasattr(self.parent, 'burst_length_var') else str(getattr(self.project.bus, 'burst_length', 256))
        self.burst_length.insert(0, burst_length_value)
        self.burst_length.pack(side='left')
        ttk.Label(burst_frame, text="(1-256)", font=('Arial', 9)).pack(side='left', padx=(5, 0))
        
        # Protocol Features
        protocol_frame = ttk.LabelFrame(common_frame, text="Protocol Features", padding="10")
        protocol_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.enable_qos = tk.BooleanVar(value=True)
        ttk.Checkbutton(protocol_frame, text="Enable QoS", 
                       variable=self.enable_qos).pack(anchor='w', pady=2)
        
        self.enable_region = tk.BooleanVar(value=True)
        ttk.Checkbutton(protocol_frame, text="Enable REGION", 
                       variable=self.enable_region).pack(anchor='w', pady=2)
        
        self.enable_exclusive = tk.BooleanVar(value=True)
        ttk.Checkbutton(protocol_frame, text="Enable Exclusive Access", 
                       variable=self.enable_exclusive).pack(anchor='w', pady=2)
        
        self.enable_user = tk.BooleanVar(value=False)
        ttk.Checkbutton(protocol_frame, text="Enable USER signals", 
                       variable=self.enable_user).pack(anchor='w', pady=2)
        
        self.enable_firewall = tk.BooleanVar(value=False)
        ttk.Checkbutton(protocol_frame, text="Enable Security Firewall", 
                       variable=self.enable_firewall).pack(anchor='w', pady=2)
        
        # ACE-Lite Coherency Features
        ace_frame = ttk.LabelFrame(common_frame, text="ACE-Lite Coherency", padding="10")
        ace_frame.pack(fill=tk.X, pady=(0, 10))
        
        # Auto-enable ACE-Lite if project has it enabled
        ace_lite_default = hasattr(self.project.bus, 'enable_ace_lite') and self.project.bus.enable_ace_lite
        self.enable_ace_lite = tk.BooleanVar(value=ace_lite_default)
        ace_enable_cb = ttk.Checkbutton(ace_frame, text="Enable ACE-Lite Coherency Protocol", 
                       variable=self.enable_ace_lite, command=self.update_ace_lite_widgets)
        ace_enable_cb.pack(anchor='w', pady=2)
        
        # ACE-Lite specific widgets (initially disabled)
        self.ace_widgets = []
        
        # Coherency Features
        coherency_subframe = ttk.Frame(ace_frame)
        coherency_subframe.pack(fill='x', padx=(20, 0), pady=(5, 0))
        
        # These features are always enabled when ACE-Lite is enabled (no user control)
        self.enable_snoop_filter = tk.BooleanVar(value=True)
        snoop_label = ttk.Label(coherency_subframe, text="✓ Enable Snoop Filter (Always enabled)")
        snoop_label.pack(anchor='w', pady=1)
        self.ace_widgets.append(snoop_label)
        
        self.enable_dvm = tk.BooleanVar(value=True)
        dvm_label = ttk.Label(coherency_subframe, text="✓ Enable DVM (Distributed Virtual Memory) (Always enabled)")
        dvm_label.pack(anchor='w', pady=1)
        self.ace_widgets.append(dvm_label)
        
        self.enable_barriers = tk.BooleanVar(value=True)
        barrier_label = ttk.Label(coherency_subframe, text="✓ Enable Barrier Transactions (Always enabled)")
        barrier_label.pack(anchor='w', pady=1)
        self.ace_widgets.append(barrier_label)
        
        self.enable_cache_maintenance = tk.BooleanVar(value=True)
        cache_label = ttk.Label(coherency_subframe, text="✓ Enable Advanced Cache Maintenance (Always enabled)")
        cache_label.pack(anchor='w', pady=1)
        self.ace_widgets.append(cache_label)
        
        # SD_xUSER Signal Configuration
        sduser_subframe = ttk.LabelFrame(ace_frame, text="SD_xUSER Signal Widths", padding="5")
        sduser_subframe.pack(fill='x', padx=(20, 0), pady=(5, 0))
        
        # SD_AWUSER Width
        row = 0
        sdaw_label = ttk.Label(sduser_subframe, text="SD_AWUSER Width:")
        sdaw_label.grid(row=row, column=0, sticky='w', pady=2)
        self.sd_awuser_width = tk.Spinbox(sduser_subframe, from_=1, to=32, width=10)
        self.sd_awuser_width.delete(0, 'end')
        # Get value from project config if available
        sd_awuser_value = str(getattr(self.project.bus, 'sd_awuser_width', 8))
        self.sd_awuser_width.insert(0, sd_awuser_value)
        self.sd_awuser_width.grid(row=row, column=1, sticky='w', pady=2, padx=(5, 0))
        bits_label1 = ttk.Label(sduser_subframe, text="bits", font=('Arial', 9))
        bits_label1.grid(row=row, column=2, sticky='w', pady=2, padx=(5, 0))
        self.ace_widgets.extend([sdaw_label, self.sd_awuser_width, bits_label1])
        
        # SD_WUSER Width
        row += 1
        sdw_label = ttk.Label(sduser_subframe, text="SD_WUSER Width:")
        sdw_label.grid(row=row, column=0, sticky='w', pady=2)
        self.sd_wuser_width = tk.Spinbox(sduser_subframe, from_=1, to=32, width=10)
        self.sd_wuser_width.delete(0, 'end')
        # Get value from project config if available
        sd_wuser_value = str(getattr(self.project.bus, 'sd_wuser_width', 8))
        self.sd_wuser_width.insert(0, sd_wuser_value)
        self.sd_wuser_width.grid(row=row, column=1, sticky='w', pady=2, padx=(5, 0))
        bits_label2 = ttk.Label(sduser_subframe, text="bits", font=('Arial', 9))
        bits_label2.grid(row=row, column=2, sticky='w', pady=2, padx=(5, 0))
        self.ace_widgets.extend([sdw_label, self.sd_wuser_width, bits_label2])
        
        # SD_BUSER Width
        row += 1
        sdb_label = ttk.Label(sduser_subframe, text="SD_BUSER Width:")
        sdb_label.grid(row=row, column=0, sticky='w', pady=2)
        self.sd_buser_width = tk.Spinbox(sduser_subframe, from_=1, to=32, width=10)
        self.sd_buser_width.delete(0, 'end')
        # Get value from project config if available
        sd_buser_value = str(getattr(self.project.bus, 'sd_buser_width', 8))
        self.sd_buser_width.insert(0, sd_buser_value)
        self.sd_buser_width.grid(row=row, column=1, sticky='w', pady=2, padx=(5, 0))
        bits_label3 = ttk.Label(sduser_subframe, text="bits", font=('Arial', 9))
        bits_label3.grid(row=row, column=2, sticky='w', pady=2, padx=(5, 0))
        self.ace_widgets.extend([sdb_label, self.sd_buser_width, bits_label3])
        
        # SD_ARUSER Width
        row += 1
        sdar_label = ttk.Label(sduser_subframe, text="SD_ARUSER Width:")
        sdar_label.grid(row=row, column=0, sticky='w', pady=2)
        self.sd_aruser_width = tk.Spinbox(sduser_subframe, from_=1, to=32, width=10)
        self.sd_aruser_width.delete(0, 'end')
        # Get value from project config if available
        sd_aruser_value = str(getattr(self.project.bus, 'sd_aruser_width', 8))
        self.sd_aruser_width.insert(0, sd_aruser_value)
        self.sd_aruser_width.grid(row=row, column=1, sticky='w', pady=2, padx=(5, 0))
        bits_label4 = ttk.Label(sduser_subframe, text="bits", font=('Arial', 9))
        bits_label4.grid(row=row, column=2, sticky='w', pady=2, padx=(5, 0))
        self.ace_widgets.extend([sdar_label, self.sd_aruser_width, bits_label4])
        
        # SD_RUSER Width
        row += 1
        sdr_label = ttk.Label(sduser_subframe, text="SD_RUSER Width:")
        sdr_label.grid(row=row, column=0, sticky='w', pady=2)
        self.sd_ruser_width = tk.Spinbox(sduser_subframe, from_=1, to=32, width=10)
        self.sd_ruser_width.delete(0, 'end')
        # Get value from project config if available
        sd_ruser_value = str(getattr(self.project.bus, 'sd_ruser_width', 8))
        self.sd_ruser_width.insert(0, sd_ruser_value)
        self.sd_ruser_width.grid(row=row, column=1, sticky='w', pady=2, padx=(5, 0))
        bits_label5 = ttk.Label(sduser_subframe, text="bits", font=('Arial', 9))
        bits_label5.grid(row=row, column=2, sticky='w', pady=2, padx=(5, 0))
        self.ace_widgets.extend([sdr_label, self.sd_ruser_width, bits_label5])
        
        # Initially disable ACE-Lite widgets
        self.update_ace_lite_widgets()
        
        # File Generation
        files_frame = ttk.LabelFrame(common_frame, text="File Generation", padding="10")
        files_frame.pack(fill=tk.X)
        
        self.gen_filelist = tk.BooleanVar(value=True)
        ttk.Checkbutton(files_frame, text="Generate filelist.f", 
                       variable=self.gen_filelist).pack(anchor='w', pady=2)
        
        self.gen_makefile = tk.BooleanVar(value=True)
        ttk.Checkbutton(files_frame, text="Generate Makefile", 
                       variable=self.gen_makefile).pack(anchor='w', pady=2)
        
        self.gen_scripts = tk.BooleanVar(value=True)
        ttk.Checkbutton(files_frame, text="Generate simulation scripts", 
                       variable=self.gen_scripts).pack(anchor='w', pady=2)
        
        self.gen_documentation = tk.BooleanVar(value=False)
        ttk.Checkbutton(files_frame, text="Generate documentation", 
                       variable=self.gen_documentation).pack(anchor='w', pady=2)
        
    def create_output_tab(self):
        """Create output settings tab"""
        output_frame = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(output_frame, text="Output Settings")
        
        # Output Directory
        dir_frame = ttk.LabelFrame(output_frame, text="Output Directory", padding="10")
        dir_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.output_dir = tk.StringVar(value=os.path.join(os.getcwd(), "generated"))
        
        dir_entry = ttk.Entry(dir_frame, textvariable=self.output_dir, width=50)
        dir_entry.pack(side=tk.LEFT, padx=(0, 5))
        
        ttk.Button(dir_frame, text="Browse...", 
                  command=self.browse_output_dir).pack(side=tk.LEFT)
        
        # Project Information
        project_frame = ttk.LabelFrame(output_frame, text="Project Information", padding="10")
        project_frame.pack(fill=tk.X, pady=(0, 10))
        
        row = 0
        ttk.Label(project_frame, text="Project Name:").grid(row=row, column=0, sticky='w', pady=2)
        self.project_name = ttk.Entry(project_frame, width=30)
        self.project_name.insert(0, self.project.name)
        self.project_name.grid(row=row, column=1, sticky='w', pady=2)
        
        row += 1
        ttk.Label(project_frame, text="Author:").grid(row=row, column=0, sticky='w', pady=2)
        self.author = ttk.Entry(project_frame, width=30)
        self.author.insert(0, os.environ.get('USER', 'Designer'))
        self.author.grid(row=row, column=1, sticky='w', pady=2)
        
        row += 1
        ttk.Label(project_frame, text="Company:").grid(row=row, column=0, sticky='w', pady=2)
        self.company = ttk.Entry(project_frame, width=30)
        self.company.grid(row=row, column=1, sticky='w', pady=2)
        
        # Simulator Selection
        sim_frame = ttk.LabelFrame(output_frame, text="Simulator", padding="10")
        sim_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.simulator = tk.StringVar(value="VCS")
        simulators = ["VCS", "Questa", "Xcelium", "Vivado", "ModelSim", "Icarus"]
        
        for i, sim in enumerate(simulators):
            ttk.Radiobutton(sim_frame, text=sim, variable=self.simulator, 
                          value=sim).grid(row=i//3, column=i%3, sticky='w', padx=10, pady=2)
        
        # Summary
        summary_frame = ttk.LabelFrame(output_frame, text="Generation Summary", padding="10")
        summary_frame.pack(fill=tk.BOTH, expand=True)
        
        self.summary_text = tk.Text(summary_frame, height=8, width=60, wrap=tk.WORD)
        self.summary_text.pack(fill=tk.BOTH, expand=True)
        
        self.update_summary()
        
    def browse_output_dir(self):
        """Browse for output directory"""
        dir_path = filedialog.askdirectory(title="Select Output Directory")
        if dir_path:
            self.output_dir.set(dir_path)
            
    def update_ace_lite_widgets(self):
        """Enable/disable ACE-Lite specific widgets based on checkbox state"""
        state = 'normal' if self.enable_ace_lite.get() else 'disabled'
        for widget in self.ace_widgets:
            try:
                widget.configure(state=state)
            except:
                # Some widgets might not support state configuration
                pass
    
    def update_summary(self):
        """Update generation summary"""
        self.summary_text.delete(1.0, tk.END)
        
        summary = f"Generation Summary\n"
        summary += f"=" * 50 + "\n"
        summary += f"Project: {self.project.name}\n"
        summary += f"Masters: {len(self.project.masters)}\n"
        summary += f"Slaves: {len(self.project.slaves)}\n"
        summary += f"Mode: {self.mode.upper()}\n"
        
        # Add ACE-Lite status if enabled
        if hasattr(self, 'enable_ace_lite') and self.enable_ace_lite.get():
            summary += f"ACE-Lite: ENABLED\n"
            if hasattr(self, 'enable_dvm') and self.enable_dvm.get():
                summary += f"  • DVM Support: YES\n"
            if hasattr(self, 'enable_barriers') and self.enable_barriers.get():
                summary += f"  • Barrier Transactions: YES\n"
            if hasattr(self, 'enable_cache_maintenance') and self.enable_cache_maintenance.get():
                summary += f"  • Cache Maintenance: YES\n"
        else:
            summary += f"ACE-Lite: DISABLED\n"
        
        summary += f"Timestamp: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        
        self.summary_text.insert(1.0, summary)
        
    def generate(self):
        """Handle generate button click"""
        # Validate settings
        if not self.output_dir.get():
            messagebox.showerror("Error", "Please select an output directory")
            return
            
        # Collect all settings
        self.result = {
            'output_dir': self.output_dir.get(),
            'project_name': self.project_name.get(),
            'author': self.author.get(),
            'company': self.company.get(),
            'simulator': self.simulator.get(),
            'mode': self.mode,
            'timestamp': datetime.now().isoformat()
        }
        
        # Add RTL settings if applicable
        if self.mode in ['rtl', 'both']:
            self.result['rtl'] = {
                'gen_interconnect': self.rtl_gen_interconnect.get(),
                'gen_bridges': self.rtl_gen_bridges.get(),
                'gen_cdc': self.rtl_gen_cdc.get(),
                'gen_default_slave': self.rtl_gen_default_slave.get(),
                'gen_assertions': self.rtl_gen_assertions.get(),
                'pipeline_stages': int(self.rtl_pipeline_stages.get()),
                'arbitration': self.rtl_arbitration.get(),
                'max_outstanding': int(self.rtl_max_outstanding.get()),
                'optimization': self.rtl_optimization.get()
            }
            
        # Add VIP settings if applicable
        if self.mode in ['vip', 'both']:
            self.result['vip'] = {
                'gen_master_agent': self.vip_gen_master_agent.get(),
                'gen_slave_agent': self.vip_gen_slave_agent.get(),
                'gen_monitor': self.vip_gen_monitor.get(),
                'gen_scoreboard': self.vip_gen_scoreboard.get(),
                'gen_coverage': self.vip_gen_coverage.get(),
                'gen_base_test': self.vip_gen_base_test.get(),
                'gen_random_test': self.vip_gen_random_test.get(),
                'gen_directed_test': self.vip_gen_directed_test.get(),
                'gen_stress_test': self.vip_gen_stress_test.get(),
                'master_seq_count': int(self.vip_master_seq_count.get()),
                'slave_seq_count': int(self.vip_slave_seq_count.get())
            }
            
        # Add common settings
        self.result['common'] = {
            'data_width': int(self.data_width.get()),
            'addr_width': int(self.addr_width.get()),
            'id_width': int(self.id_width.get()),
            'user_width': int(self.user_width.get()),
            'burst_length': int(self.burst_length.get()),
            'enable_qos': self.enable_qos.get(),
            'enable_region': self.enable_region.get(),
            'enable_exclusive': self.enable_exclusive.get(),
            'enable_user': self.enable_user.get(),
            'enable_firewall': self.enable_firewall.get(),
            'enable_cdc': getattr(self, 'rtl_gen_cdc', tk.BooleanVar(value=False)).get(),
            'gen_filelist': self.gen_filelist.get(),
            'gen_makefile': self.gen_makefile.get(),
            'gen_scripts': self.gen_scripts.get(),
            'gen_documentation': self.gen_documentation.get()
        }
        
        # Add ACE-Lite settings if available
        if hasattr(self, 'enable_ace_lite'):
            self.result['ace_lite'] = {
                'enable_ace_lite': self.enable_ace_lite.get(),
                'enable_snoop_filter': self.enable_snoop_filter.get(),
                'enable_dvm': self.enable_dvm.get(),
                'enable_barriers': self.enable_barriers.get(),
                'enable_cache_maintenance': self.enable_cache_maintenance.get(),
                'sd_awuser_width': int(self.sd_awuser_width.get()),
                'sd_wuser_width': int(self.sd_wuser_width.get()),
                'sd_buser_width': int(self.sd_buser_width.get()),
                'sd_aruser_width': int(self.sd_aruser_width.get()),
                'sd_ruser_width': int(self.sd_ruser_width.get())
            }
        
        self.destroy()
        
    def cancel(self):
        """Handle cancel button click"""
        self.result = None
        self.destroy()


# Test dialog
if __name__ == "__main__":
    from dataclasses import dataclass, field
    from typing import List
    
    @dataclass
    class BusConfig:
        addr_width: int = 32
        data_width: int = 64
        id_width: int = 4
        user_width: int = 0
        arbitration: str = "round_robin"
    
    @dataclass
    class ProjectConfig:
        name: str = "test_project"
        masters: List = field(default_factory=list)
        slaves: List = field(default_factory=list)
        bus: BusConfig = field(default_factory=BusConfig)
    
    root = tk.Tk()
    root.withdraw()
    
    project = ProjectConfig()
    dialog = GenerationSettingsDialog(root, project, mode='both')
    root.wait_window(dialog)
    
    if dialog.result:
        print("Generation settings:", dialog.result)
    else:
        print("Cancelled")
        
    root.destroy()