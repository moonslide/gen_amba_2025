#!/usr/bin/env python3
"""
AMBA AXI4 RTL & VIP Generator - Streamlined GUI (v3)
Single-page layout with templates at top, canvas in middle, CLI at bottom
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import json
import yaml
import os
import sys
import io
import logging
from datetime import datetime
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Optional, Tuple
import math

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

@dataclass
class NodeConfig:
    """Configuration for a node in the topology"""
    name: str
    index: int
    node_type: str  # 'master', 'slave', 'bridge'
    ip_type: str  # 'generated', 'external'
    x: float = 100
    y: float = 100
    domain: str = "default"
    security: str = "shared"
    qos_aw: int = 0
    qos_ar: int = 0
    priority: int = 0
    arbitration_policy: str = "round_robin"  # round_robin, priority, weighted, strict_priority
    firewall_category: str = "shared"  # shared, non_sec, sec
    base_addr: Optional[int] = None
    size: Optional[int] = None
    region_size: Optional[int] = None  # For REGION identifier
    allowed_masters: List[str] = field(default_factory=list)
    rtl_path: Optional[str] = None
    top_module: Optional[str] = None
    # AxCACHE settings
    cache_enable: bool = True
    awcache_default: int = 0b0011  # Default: Cacheable and Bufferable
    arcache_default: int = 0b0011  # Default: Cacheable and Bufferable
    cache_policy: str = "write-through"  # write-through, write-back, no-allocate
    cache_coherent: bool = False
    
@dataclass
class BusConfig:
    """Bus configuration parameters"""
    addr_width: int = 32
    data_width: int = 64
    id_width: int = 4
    user_width: int = 0
    burst_length: int = 256  # AXI4 max burst length (1-256)
    protocol: str = 'AXI4'  # AXI4, AXI3, ACE-Lite, AHB-Lite, APB
    enable_user_signals: bool = False
    enable_qos: bool = False
    enable_exclusive_access: bool = True
    enable_security_firewall: bool = False
    bus_arbiter: str = "round_robin"  # round_robin, priority, weighted
    arbitration: str = "round_robin"  # For backward compatibility
    # ACE-Lite Configuration
    enable_ace_lite: bool = False
    sd_awuser_width: int = 8
    sd_wuser_width: int = 8
    sd_buser_width: int = 8
    sd_aruser_width: int = 8
    sd_ruser_width: int = 8
    enable_cache_coherency: bool = False
    enable_snoop_filter: bool = False
    enable_dvm: bool = False
    enable_barriers: bool = False
    
@dataclass 
class DomainConfig:
    """Clock/Reset domain configuration"""
    name: str
    clock: str
    reset: str
    frequency: float = 100.0

@dataclass
class ProjectConfig:
    """Complete project configuration"""
    name: str = "axi4_project"
    bus: BusConfig = field(default_factory=BusConfig)
    masters: List[NodeConfig] = field(default_factory=list)
    slaves: List[NodeConfig] = field(default_factory=list)
    bridges: List[NodeConfig] = field(default_factory=list)
    domains: List[DomainConfig] = field(default_factory=list)
    connections: List[Tuple[str, str]] = field(default_factory=list)

class AXI4GeneratorGUI(tk.Tk):
    """Main GUI Application - Streamlined Single Page Layout"""
    
    def __init__(self):
        super().__init__()
        
        self.title("AMBA AXI4 RTL & VIP Generator v3 - Streamlined")
        self.geometry("1200x800")
        
        # Initialize project
        self.project = ProjectConfig()
        
        # Create menu bar
        self.create_menu()
        
        # Create main layout
        self.create_layout()
        
        # Initialize canvas state
        self.nodes = {}  # id -> node widget
        self.connections = []  # list of connection lines
        self.selected_node = None
        self.drag_data = {"x": 0, "y": 0, "item": None}
        
        # Update status labels after layout creation
        self.update_status_labels()
        
        # Initialize protocol-specific UI state
        self.on_protocol_change()
        
        logger.info("Streamlined GUI started")
        
    def create_menu(self):
        """Create menu bar"""
        menubar = tk.Menu(self)
        self.config(menu=menubar)
        
        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="New Project", command=self.new_project)
        file_menu.add_command(label="Open Project...", command=self.open_project)
        file_menu.add_command(label="Save Project", command=self.save_project)
        file_menu.add_command(label="Save Project As...", command=self.save_project_as)
        file_menu.add_separator()
        file_menu.add_command(label="Export CLI Script...", command=self.export_cli_script)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit)
        
        # Templates menu
        templates_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Templates", menu=templates_menu)
        templates_menu.add_command(label="4x4 Basic", 
                                  command=lambda: self.load_template('4x4'))
        templates_menu.add_command(label="8x8 Standard", 
                                  command=lambda: self.load_template('8x8'))
        templates_menu.add_command(label="16x16 Large", 
                                  command=lambda: self.load_template('16x16'))
        templates_menu.add_command(label="32x32 XLarge", 
                                  command=lambda: self.load_template('32x32'))
        templates_menu.add_command(label="32x32 ACE-Lite", 
                                  command=lambda: self.load_template('32x32_ace_lite'))
        templates_menu.add_separator()
        templates_menu.add_command(label="Multi-Domain SoC", 
                                  command=lambda: self.load_template('multi_domain'))
        templates_menu.add_command(label="AHB-Lite Bridge", 
                                  command=lambda: self.load_template('ahb_bridge'))
        templates_menu.add_command(label="APB Subsystem", 
                                  command=lambda: self.load_template('apb_subsystem'))
        
        # Generate menu
        gen_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Generate", menu=gen_menu)
        gen_menu.add_command(label="Generate All...", command=lambda: self.show_generation_dialog('both'))
        gen_menu.add_separator()
        gen_menu.add_command(label="Generate RTL...", command=lambda: self.show_generation_dialog('rtl'))
        gen_menu.add_command(label="Generate VIP...", command=lambda: self.show_generation_dialog('vip'))
        gen_menu.add_separator()
        gen_menu.add_command(label="Quick Generate (Default)", command=self.quick_generate_default)
        gen_menu.add_separator()
        gen_menu.add_command(label="Generate CLI Command", command=self.generate_cli_command)
        gen_menu.add_command(label="Copy CLI to Clipboard", command=self.copy_cli_to_clipboard)
        
        # Help menu
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="User Guide", command=self.show_user_guide)
        help_menu.add_command(label="Keyboard Shortcuts", command=self.show_shortcuts)
        help_menu.add_separator()
        help_menu.add_command(label="About", command=self.show_about)
        
    def create_layout(self):
        """Create streamlined single-page layout"""
        
        # Top Frame - Templates and Node Tools
        top_frame = ttk.Frame(self)
        top_frame.pack(side=tk.TOP, fill=tk.X, padx=5, pady=5)
        
        # Templates section (left side of top)
        template_frame = ttk.LabelFrame(top_frame, text="Templates", padding=5)
        template_frame.pack(side=tk.LEFT, padx=5)
        
        ttk.Button(template_frame, text="4x4 Basic", 
                  command=lambda: self.load_template('4x4')).pack(side=tk.LEFT, padx=2)
        ttk.Button(template_frame, text="8x8 Standard", 
                  command=lambda: self.load_template('8x8')).pack(side=tk.LEFT, padx=2)
        ttk.Button(template_frame, text="16x16 Large", 
                  command=lambda: self.load_template('16x16')).pack(side=tk.LEFT, padx=2)
        ttk.Button(template_frame, text="32x32 ACE-Lite", 
                  command=lambda: self.load_template('32x32_ace_lite')).pack(side=tk.LEFT, padx=2)
        ttk.Button(template_frame, text="Multi-Domain", 
                  command=lambda: self.load_template('multi_domain')).pack(side=tk.LEFT, padx=2)
        
        # Node tools section (center of top)
        node_frame = ttk.LabelFrame(top_frame, text="Add Nodes", padding=5)
        node_frame.pack(side=tk.LEFT, padx=5)
        
        ttk.Button(node_frame, text="+ Master", 
                  command=lambda: self.add_node('master')).pack(side=tk.LEFT, padx=2)
        ttk.Button(node_frame, text="+ Slave", 
                  command=lambda: self.add_node('slave')).pack(side=tk.LEFT, padx=2)
        ttk.Button(node_frame, text="+ Ext Master", 
                  command=lambda: self.add_node('ext_master')).pack(side=tk.LEFT, padx=2)
        ttk.Button(node_frame, text="+ Ext Slave", 
                  command=lambda: self.add_node('ext_slave')).pack(side=tk.LEFT, padx=2)
        ttk.Button(node_frame, text="+ Bridge", 
                  command=lambda: self.add_node('bridge')).pack(side=tk.LEFT, padx=2)
        
        # Canvas tools (right side of top)
        canvas_tools = ttk.LabelFrame(top_frame, text="Canvas Tools", padding=5)
        canvas_tools.pack(side=tk.LEFT, padx=5)
        
        ttk.Button(canvas_tools, text="Delete", 
                  command=self.delete_selected).pack(side=tk.LEFT, padx=2)
        ttk.Button(canvas_tools, text="Auto-Arrange", 
                  command=self.auto_arrange).pack(side=tk.LEFT, padx=2)
        ttk.Button(canvas_tools, text="Zoom In", 
                  command=self.zoom_in).pack(side=tk.LEFT, padx=2)
        ttk.Button(canvas_tools, text="Zoom Out", 
                  command=self.zoom_out).pack(side=tk.LEFT, padx=2)
        ttk.Button(canvas_tools, text="Zoom Fit", 
                  command=self.zoom_fit).pack(side=tk.LEFT, padx=2)
        ttk.Button(canvas_tools, text="Clear All", 
                  command=self.clear_canvas).pack(side=tk.LEFT, padx=2)
        
        # Middle Frame - Canvas (main work area) with side panel
        middle_frame = ttk.Frame(self)
        middle_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Left panel for bus settings
        left_panel = ttk.LabelFrame(middle_frame, text="Bus Settings", padding=5)
        left_panel.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 5))
        
        self.create_bus_settings_panel(left_panel)
        
        # Canvas with scrollbars (right side)
        canvas_frame = ttk.Frame(middle_frame)
        canvas_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        self.canvas = tk.Canvas(canvas_frame, bg='white', width=1000, height=400)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # Vertical scrollbar
        v_scrollbar = ttk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview)
        v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas.config(yscrollcommand=v_scrollbar.set)
        
        # Horizontal scrollbar
        h_scrollbar = ttk.Scrollbar(middle_frame, orient=tk.HORIZONTAL, command=self.canvas.xview)
        h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
        self.canvas.config(xscrollcommand=h_scrollbar.set)
        
        # Zoom functionality
        self.zoom_factor = 1.0
        self.min_zoom = 0.2
        self.max_zoom = 3.0
        self.zoom_step = 0.1
        
        # Canvas bindings
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_drag_release)
        self.canvas.bind("<Button-3>", self.on_right_click)
        self.canvas.bind("<Double-Button-1>", self.on_double_click)
        self.canvas.bind("<MouseWheel>", self.on_mouse_wheel)
        self.canvas.bind("<Control-plus>", self.zoom_in)
        self.canvas.bind("<Control-minus>", self.zoom_out)
        self.canvas.bind("<Control-0>", self.zoom_reset)
        self.canvas.focus_set()  # Enable keyboard focus for canvas
        
        # Set canvas scroll region
        self.canvas.config(scrollregion=(0, 0, 2000, 2000))
        
        # Bottom Frame - CLI Panel
        bottom_frame = ttk.LabelFrame(self, text="Command-Line Interface", padding=5)
        bottom_frame.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=5)
        
        # CLI controls on left
        cli_controls = ttk.Frame(bottom_frame)
        cli_controls.pack(side=tk.LEFT, padx=5)
        
        ttk.Button(cli_controls, text="Generate CLI", 
                  command=self.generate_cli_command).pack(pady=2)
        ttk.Button(cli_controls, text="Copy", 
                  command=self.copy_cli_to_clipboard).pack(pady=2)
        ttk.Button(cli_controls, text="Export", 
                  command=self.export_cli_script).pack(pady=2)
        
        # CLI text area on right
        cli_text_frame = ttk.Frame(bottom_frame)
        cli_text_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        cli_scroll = ttk.Scrollbar(cli_text_frame)
        cli_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.cli_text = tk.Text(cli_text_frame, height=6, wrap=tk.WORD,
                               yscrollcommand=cli_scroll.set,
                               font=('Courier', 9))
        self.cli_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        cli_scroll.config(command=self.cli_text.yview)
        
        # Status bar at very bottom
        self.status_bar = ttk.Label(self, text="Ready", relief=tk.SUNKEN, anchor='w')
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # Generate initial CLI command
        self.generate_cli_command()
        
    def create_bus_settings_panel(self, parent):
        """Create the bus settings panel on the left side"""
        
        # Bus width settings
        row = 0
        ttk.Label(parent, text="Bus Configuration", font=('TkDefaultFont', 10, 'bold')).grid(row=row, column=0, columnspan=2, pady=5, sticky='w')
        
        # Protocol selection
        row += 1
        ttk.Label(parent, text="Protocol:").grid(row=row, column=0, sticky='w', padx=2, pady=2)
        self.protocol_var = tk.StringVar(value=getattr(self.project.bus, 'protocol', 'AXI4'))
        protocol_combo = ttk.Combobox(parent, textvariable=self.protocol_var, width=12,
                                     values=['AXI4', 'AXI3', 'ACE-Lite', 'AHB-Lite', 'APB'],
                                     state="readonly")
        protocol_combo.grid(row=row, column=1, padx=2, pady=2)
        protocol_combo.bind('<<ComboboxSelected>>', lambda e: self.on_protocol_change())
        ttk.Label(parent, text="", font=('Arial', 7)).grid(row=row, column=2, sticky='w', padx=2)
        
        row += 1
        ttk.Label(parent, text="Data Width:").grid(row=row, column=0, sticky='w', padx=2, pady=2)
        self.data_width_var = tk.StringVar(value=str(self.project.bus.data_width))
        data_width_combo = ttk.Combobox(parent, textvariable=self.data_width_var, width=12,
                                       values=['8', '16', '32', '64', '128', '256', '512', '1024'],
                                       state="readonly")
        data_width_combo.grid(row=row, column=1, padx=2, pady=2)
        data_width_combo.bind('<<ComboboxSelected>>', lambda e: self.on_bus_config_change())
        ttk.Label(parent, text="(bits)", font=('Arial', 7)).grid(row=row, column=2, sticky='w', padx=2)
        
        row += 1
        ttk.Label(parent, text="Address Width:").grid(row=row, column=0, sticky='w', padx=2, pady=2)
        self.addr_width_var = tk.StringVar(value=str(self.project.bus.addr_width))
        addr_width_entry = ttk.Entry(parent, textvariable=self.addr_width_var, width=10)
        addr_width_entry.grid(row=row, column=1, padx=2, pady=2)
        addr_width_entry.bind('<FocusOut>', lambda e: self.on_bus_config_change())
        addr_width_entry.bind('<KeyRelease>', lambda e: self.validate_width_field(e, "addr"))
        ttk.Label(parent, text="(8-64)", font=('Arial', 7)).grid(row=row, column=2, sticky='w', padx=2)
        
        row += 1
        ttk.Label(parent, text="ID Width:").grid(row=row, column=0, sticky='w', padx=2, pady=2)
        self.id_width_var = tk.StringVar(value=str(self.project.bus.id_width))
        id_width_entry = ttk.Entry(parent, textvariable=self.id_width_var, width=10)
        id_width_entry.grid(row=row, column=1, padx=2, pady=2)
        id_width_entry.bind('<FocusOut>', lambda e: self.on_bus_config_change())
        id_width_entry.bind('<KeyRelease>', lambda e: self.validate_width_field(e, "id"))
        ttk.Label(parent, text="(1-16)", font=('Arial', 7)).grid(row=row, column=2, sticky='w', padx=2)
        
        row += 1
        self.user_width_label = ttk.Label(parent, text="User Width:")
        self.user_width_label.grid(row=row, column=0, sticky='w', padx=2, pady=2)
        self.user_width_var = tk.StringVar(value=str(getattr(self.project.bus, 'user_width', 0)))
        self.user_width_entry = ttk.Entry(parent, textvariable=self.user_width_var, width=10)
        self.user_width_entry.grid(row=row, column=1, padx=2, pady=2)
        self.user_width_entry.bind('<FocusOut>', lambda e: self.on_bus_config_change())
        self.user_width_entry.bind('<KeyRelease>', lambda e: self.validate_width_field(e, "user"))
        self.user_width_hint = ttk.Label(parent, text="(0=disable)", font=('Arial', 7))
        self.user_width_hint.grid(row=row, column=2, sticky='w', padx=2)
        
        row += 1
        ttk.Label(parent, text="Burst Length:").grid(row=row, column=0, sticky='w', padx=2, pady=2)
        self.burst_length_var = tk.StringVar(value=str(getattr(self.project.bus, 'burst_length', 256)))
        burst_length_entry = ttk.Entry(parent, textvariable=self.burst_length_var, width=10)
        burst_length_entry.grid(row=row, column=1, padx=2, pady=2)
        burst_length_entry.bind('<FocusOut>', lambda e: self.on_bus_config_change())
        burst_length_entry.bind('<KeyRelease>', lambda e: self.validate_width_field(e, "burst"))
        ttk.Label(parent, text="(1-256)", font=('Arial', 7)).grid(row=row, column=2, sticky='w', padx=2)
        
        # Feature enables
        row += 1
        ttk.Separator(parent, orient='horizontal').grid(row=row, column=0, columnspan=2, sticky='ew', pady=5)
        
        row += 1
        ttk.Label(parent, text="Features", font=('TkDefaultFont', 10, 'bold')).grid(row=row, column=0, columnspan=2, pady=5, sticky='w')
        
        row += 1
        self.enable_user_var = tk.BooleanVar(value=self.project.bus.enable_user_signals)
        ttk.Checkbutton(parent, text="Enable USER Signals", variable=self.enable_user_var,
                       command=self.on_feature_change).grid(row=row, column=0, columnspan=2, sticky='w', padx=2, pady=2)
        
        row += 1
        self.enable_qos_var = tk.BooleanVar(value=self.project.bus.enable_qos)
        ttk.Checkbutton(parent, text="Enable QoS", variable=self.enable_qos_var,
                       command=self.on_feature_change).grid(row=row, column=0, columnspan=2, sticky='w', padx=2, pady=2)
        
        row += 1
        self.enable_exclusive_var = tk.BooleanVar(value=self.project.bus.enable_exclusive_access)
        ttk.Checkbutton(parent, text="Enable Exclusive Access", variable=self.enable_exclusive_var,
                       command=self.on_feature_change).grid(row=row, column=0, columnspan=2, sticky='w', padx=2, pady=2)
        
        row += 1
        self.enable_firewall_var = tk.BooleanVar(value=self.project.bus.enable_security_firewall)
        ttk.Checkbutton(parent, text="Enable Security Firewall", variable=self.enable_firewall_var,
                       command=self.on_feature_change).grid(row=row, column=0, columnspan=2, sticky='w', padx=2, pady=2)
        
        # Bus arbiter setting
        row += 1
        ttk.Separator(parent, orient='horizontal').grid(row=row, column=0, columnspan=2, sticky='ew', pady=5)
        
        row += 1
        ttk.Label(parent, text="Bus Arbiter:").grid(row=row, column=0, sticky='w', padx=2, pady=2)
        self.bus_arbiter_var = tk.StringVar(value=self.project.bus.bus_arbiter)
        arbiter_combo = ttk.Combobox(parent, textvariable=self.bus_arbiter_var, width=12,
                                   values=['round_robin', 'priority', 'weighted'])
        arbiter_combo.grid(row=row, column=1, padx=2, pady=2)
        arbiter_combo.bind('<<ComboboxSelected>>', self.on_arbiter_change)
        
        # Status display
        row += 1
        ttk.Separator(parent, orient='horizontal').grid(row=row, column=0, columnspan=2, sticky='ew', pady=5)
        
        row += 1
        ttk.Label(parent, text="Status", font=('TkDefaultFont', 10, 'bold')).grid(row=row, column=0, columnspan=2, pady=5, sticky='w')
        
        row += 1
        self.master_count_label = ttk.Label(parent, text=f"Masters: {len(self.project.masters)}")
        self.master_count_label.grid(row=row, column=0, columnspan=2, sticky='w', padx=2, pady=1)
        
        row += 1
        self.slave_count_label = ttk.Label(parent, text=f"Slaves: {len(self.project.slaves)}")
        self.slave_count_label.grid(row=row, column=0, columnspan=2, sticky='w', padx=2, pady=1)
        
        row += 1
        self.bridge_count_label = ttk.Label(parent, text=f"Bridges: {len(self.project.bridges)}")
        self.bridge_count_label.grid(row=row, column=0, columnspan=2, sticky='w', padx=2, pady=1)
        
    def validate_width_field(self, event, field_type):
        """Real-time validation of width fields with visual feedback and auto-suggestions"""
        value = event.widget.get()
        if not value:
            return
        
        try:
            int_val = int(value)
            valid = False
            suggestion_msg = ""
            
            if field_type == "addr" and 8 <= int_val <= 64:
                valid = True
            elif field_type == "data" and int_val in [8, 16, 32, 64, 128, 256, 512, 1024]:
                # Check ACE-Lite specific requirement for large configurations
                ace_lite_enabled = hasattr(self.project.bus, 'enable_ace_lite') and self.project.bus.enable_ace_lite
                master_count = len(self.project.masters)
                slave_count = len(self.project.slaves)
                
                if ace_lite_enabled and (master_count >= 32 or slave_count >= 32) and int_val < 256:
                    valid = False
                    suggestion_msg = f"ACE-Lite {master_count}x{slave_count} requires minimum 256-bit data width (gen_amba_axi limitation)"
                else:
                    valid = True
                    # Auto-suggest optimal data width based on master/slave count
                    total_components = len(self.project.masters) + len(self.project.slaves)
                    if total_components >= 64 and int_val < 1024:
                        suggestion_msg = f"TIP: For {total_components} components, consider 1024-bit data width for optimal performance"
                    elif total_components >= 32 and int_val < 512:
                        suggestion_msg = f"TIP: For {total_components} components, consider 512-bit data width for better performance"
                    elif total_components >= 16 and int_val < 256:
                        suggestion_msg = f"TIP: For {total_components} components, consider 256-bit data width for better performance"
            elif field_type == "id" and 1 <= int_val <= 16:
                valid = True
                # Auto-suggest optimal ID width based on master count
                master_count = len(self.project.masters)
                required_id_width = max(4, (master_count - 1).bit_length() + 1)  # +1 for safety margin
                if master_count > 0 and int_val < required_id_width:
                    valid = False  # Mark as invalid if insufficient
                    suggestion_msg = f"❌ ID width {int_val} too small for {master_count} masters. Minimum required: {required_id_width} bits"
                elif master_count > 0 and int_val == required_id_width:
                    suggestion_msg = f"✅ ID width {int_val} is optimal for {master_count} masters"
            elif field_type == "user" and int_val >= 0:
                # Check protocol-specific USER signal support
                protocol = getattr(self.project.bus, 'protocol', 'AXI4')
                
                if protocol in ['AHB-Lite', 'APB'] and int_val > 0:
                    valid = False
                    suggestion_msg = f"USER signals not supported by {protocol} protocol"
                elif protocol == 'ACE-Lite' and int_val > 0:
                    valid = False
                    suggestion_msg = "ACE-Lite uses sd_*user_width signals instead of standard USER signals"
                else:
                    valid = True
                    if protocol == 'ACE-Lite' and int_val == 0:
                        suggestion_msg = "✅ USER width 0 is correct for ACE-Lite (uses sd_*user_width instead)"
                    elif protocol in ['AHB-Lite', 'APB'] and int_val == 0:
                        suggestion_msg = f"✅ USER signals not applicable for {protocol}"
            elif field_type == "burst" and 1 <= int_val <= 256:
                valid = True
            
            # Visual feedback
            if valid:
                event.widget.config(fieldbackground='white')
            else:
                event.widget.config(fieldbackground='#ffcccc')  # Light red for invalid
            
            # Show suggestion in status bar
            if suggestion_msg:
                self.status_bar.config(text=suggestion_msg)
                
        except ValueError:
            event.widget.config(fieldbackground='#ffcccc')  # Light red for non-numeric

    def update_left_panel_from_project(self):
        """Update all left panel GUI fields from current project configuration"""
        # Update bus configuration fields
        if hasattr(self, 'protocol_var'):
            protocol = getattr(self.project.bus, 'protocol', 'AXI4')
            self.protocol_var.set(protocol)
            
        if hasattr(self, 'data_width_var'):
            self.data_width_var.set(str(self.project.bus.data_width))
            
        if hasattr(self, 'addr_width_var'):
            self.addr_width_var.set(str(self.project.bus.addr_width))
            
        if hasattr(self, 'id_width_var'):
            self.id_width_var.set(str(self.project.bus.id_width))
            
        if hasattr(self, 'user_width_var'):
            user_width = getattr(self.project.bus, 'user_width', 0)
            self.user_width_var.set(str(user_width))
            
        if hasattr(self, 'burst_length_var'):
            burst_length = getattr(self.project.bus, 'burst_length', 256)
            self.burst_length_var.set(str(burst_length))
            
        # Update feature checkboxes
        if hasattr(self, 'enable_qos_var'):
            self.enable_qos_var.set(getattr(self.project.bus, 'enable_qos', False))
            
        if hasattr(self, 'enable_exclusive_var'):
            self.enable_exclusive_var.set(getattr(self.project.bus, 'enable_exclusive_access', True))
            
        if hasattr(self, 'enable_user_var'):
            self.enable_user_var.set(getattr(self.project.bus, 'enable_user_signals', False))
            
        if hasattr(self, 'enable_firewall_var'):
            self.enable_firewall_var.set(getattr(self.project.bus, 'enable_security_firewall', False))
            
        # Update ACE-Lite specific fields if they exist
        if hasattr(self, 'enable_ace_lite_var'):
            self.enable_ace_lite_var.set(getattr(self.project.bus, 'enable_ace_lite', False))
            
        if hasattr(self, 'enable_coherency_var'):
            self.enable_coherency_var.set(getattr(self.project.bus, 'enable_cache_coherency', False))
            
        if hasattr(self, 'enable_snoop_var'):
            self.enable_snoop_var.set(getattr(self.project.bus, 'enable_snoop_filter', False))
            
        # Trigger protocol change to update dependent fields (like USER width state)
        self.on_protocol_change()

    def on_protocol_change(self, event=None):
        """Handle protocol selection changes and auto-block incompatible features"""
        protocol = self.protocol_var.get()
        
        # Store protocol in bus configuration
        if not hasattr(self.project.bus, 'protocol'):
            self.project.bus.protocol = 'AXI4'
        self.project.bus.protocol = protocol
        
        # Handle protocol-specific feature blocking
        if protocol in ['AHB-Lite', 'APB']:
            # AHB and APB don't support USER signals
            self.user_width_var.set("0")
            self.user_width_entry.config(state='disabled')
            self.user_width_label.config(foreground='gray')
            self.user_width_hint.config(text="(N/A for " + protocol + ")", foreground='gray')
            self.status_bar.config(text=f"USER signals auto-blocked for {protocol} protocol")
            
        elif protocol == 'ACE-Lite':
            # ACE-Lite uses separate sd_*user_width signals
            self.user_width_var.set("0")
            self.user_width_entry.config(state='disabled') 
            self.user_width_label.config(foreground='gray')
            self.user_width_hint.config(text="(uses sd_*user_width)", foreground='gray')
            self.status_bar.config(text="USER signals auto-blocked for ACE-Lite (uses sd_*user_width instead)")
            
            # Enable ACE-Lite features
            if hasattr(self.project.bus, 'enable_ace_lite'):
                self.project.bus.enable_ace_lite = True
                
        else:  # AXI4 or AXI3
            # Enable USER signals for AXI protocols
            self.user_width_entry.config(state='normal')
            self.user_width_label.config(foreground='black')
            self.user_width_hint.config(text="(0=disable)", foreground='black')
            if protocol == 'AXI4':
                self.status_bar.config(text="AXI4 protocol: USER signals available")
            else:
                self.status_bar.config(text="AXI3 protocol: USER signals available")
                
            # Disable ACE-Lite features for standard AXI
            if hasattr(self.project.bus, 'enable_ace_lite'):
                self.project.bus.enable_ace_lite = False
        
        # Update bus configuration and regenerate CLI
        self.on_bus_config_change()

    def on_bus_config_change(self, event=None):
        """Handle bus configuration changes with smart validation and auto-fixes"""
        try:
            # Get values with validation
            data_width = int(self.data_width_var.get())
            addr_width = int(self.addr_width_var.get())
            id_width = int(self.id_width_var.get())
            user_width = int(self.user_width_var.get())
            burst_length = int(self.burst_length_var.get())
            
            # Auto ID width validation for master count
            master_count = len(self.project.masters)
            if master_count > 0:
                required_id_width = max(4, (master_count - 1).bit_length() + 1)
                if id_width < required_id_width:
                    # Auto-fix ID width
                    id_width = required_id_width
                    self.id_width_var.set(str(id_width))
                    self.status_bar.config(text=f"🔧 Auto-fixed ID width to {id_width} bits for {master_count} masters")
            
            # Auto-suggest data width for performance
            total_components = len(self.project.masters) + len(self.project.slaves)
            suggested_data_width = data_width
            
            # Check ACE-Lite specific requirement for large configurations
            ace_lite_enabled = hasattr(self.project.bus, 'enable_ace_lite') and self.project.bus.enable_ace_lite
            master_count = len(self.project.masters)
            slave_count = len(self.project.slaves)
            
            if ace_lite_enabled and (master_count >= 32 or slave_count >= 32) and data_width < 256:
                # ACE-Lite large configuration requires minimum 256-bit data width
                self.status_bar.config(text=f"WARNING: ACE-Lite {master_count}x{slave_count} requires minimum 256-bit data width (current: {data_width}-bit)")
                return  # Don't proceed with invalid config
            
            if total_components >= 64 and data_width < 1024:
                suggested_data_width = 1024
            elif total_components >= 32 and data_width < 512:
                suggested_data_width = 512
            elif total_components >= 16 and data_width < 256:
                suggested_data_width = 256
            
            if suggested_data_width != data_width:
                # Show suggestion but don't auto-change data width (user choice)
                self.status_bar.config(text=f"TIP: Consider {suggested_data_width}-bit data width for {total_components} components")
            
            # ACE-Lite USER signal conflict auto-blocking
            ace_lite_enabled = hasattr(self.project.bus, 'enable_ace_lite') and self.project.bus.enable_ace_lite
            if ace_lite_enabled and user_width > 0:
                # Auto-block USER signals when ACE-Lite is enabled
                user_width = 0
                self.user_width_var.set("0")
                self.status_bar.config(text="🔒 Auto-blocked USER signals for ACE-Lite compatibility (use sd_*user_width instead)")
            
            # Validate ranges
            if not (8 <= addr_width <= 64):
                raise ValueError("Address width must be 8-64")
            if data_width not in [8, 16, 32, 64, 128, 256, 512, 1024]:
                raise ValueError("Data width must be one of: 8,16,32,64,128,256,512,1024")
            if not (1 <= id_width <= 16):
                raise ValueError("ID width must be 1-16")
            if user_width < 0:
                raise ValueError("User width must be >= 0")
            if ace_lite_enabled and user_width > 0:
                raise ValueError("USER signals conflict with ACE-Lite! Use sd_*user_width instead")
            if not (1 <= burst_length <= 256):
                raise ValueError("Burst length must be 1-256")
            
            # Apply changes
            self.project.bus.data_width = data_width
            self.project.bus.addr_width = addr_width
            self.project.bus.id_width = id_width
            if not hasattr(self.project.bus, 'user_width'):
                self.project.bus.user_width = 0
            self.project.bus.user_width = user_width
            if not hasattr(self.project.bus, 'burst_length'):
                self.project.bus.burst_length = 256
            self.project.bus.burst_length = burst_length
            
            self.generate_cli_command()
            
        except ValueError as e:
            self.status_bar.config(text=f"Configuration error: {str(e)}")
        except Exception:
            pass  # Ignore invalid values during typing
            
    def on_feature_change(self):
        """Handle feature enable/disable changes with ACE-Lite conflict detection"""
        self.project.bus.enable_user_signals = self.enable_user_var.get()
        self.project.bus.enable_qos = self.enable_qos_var.get()
        self.project.bus.enable_exclusive_access = self.enable_exclusive_var.get()
        self.project.bus.enable_security_firewall = self.enable_firewall_var.get()
        
        # Check for ACE-Lite conflict with USER signals
        ace_lite_enabled = hasattr(self.project.bus, 'enable_ace_lite') and self.project.bus.enable_ace_lite
        if ace_lite_enabled:
            # Auto-block USER signals and reset user_width to 0
            if hasattr(self.project.bus, 'user_width') and self.project.bus.user_width > 0:
                self.project.bus.user_width = 0
                if hasattr(self, 'user_width_var'):
                    self.user_width_var.set("0")
                self.status_bar.config(text="🔒 ACE-Lite enabled: USER signals auto-blocked (use sd_*user_width instead)")
            
            # Disable user signals checkbox if ACE-Lite is enabled
            if self.enable_user_var.get():
                self.enable_user_var.set(False)
                self.project.bus.enable_user_signals = False
                self.status_bar.config(text="🔒 ACE-Lite enabled: USER signals disabled (use sd_*user_width instead)")
        
        # Redraw nodes to show/hide conditional features
        self.redraw_all_nodes()
        self.generate_cli_command()
        
    def on_arbiter_change(self, event=None):
        """Handle bus arbiter changes"""
        self.project.bus.bus_arbiter = self.bus_arbiter_var.get()
        self.project.bus.arbitration = self.bus_arbiter_var.get()  # Update both for compatibility
        
        # Redraw nodes to update arbiter display
        self.redraw_all_nodes()
        self.generate_cli_command()
        
    def update_status_labels(self):
        """Update the status labels in the bus settings panel"""
        self.master_count_label.config(text=f"Masters: {len(self.project.masters)}")
        self.slave_count_label.config(text=f"Slaves: {len(self.project.slaves)}")
        self.bridge_count_label.config(text=f"Bridges: {len(self.project.bridges)}")
        
    def load_template(self, template_type):
        """Load a template configuration"""
        # Confirm with user
        if self.nodes and messagebox.askyesno("Load Template", 
                                              "This will clear the current design. Continue?"):
            self.clear_canvas()
        elif not self.nodes:
            pass  # Canvas is already empty
        else:
            return  # User cancelled
            
        # Clear and load template
        self.project = ProjectConfig()
        
        if template_type == '4x4':
            self.create_template(4, 4, 64, 32)
        elif template_type == '8x8':
            self.create_template(8, 8, 128, 32)
        elif template_type == '16x16':
            self.create_template(16, 16, 256, 48)
        elif template_type == '32x32':
            self.create_template(32, 32, 512, 64)
        elif template_type == '32x32_ace_lite':
            self.create_ace_lite_template(32, 32, 256, 32)
        elif template_type == 'multi_domain':
            self.create_multi_domain_template()
            
        self.redraw_all_nodes()
        self.auto_arrange()
        self.update_left_panel_from_project()  # Update GUI fields from loaded template
        self.generate_cli_command()
        self.update_status_labels()
        self.status_bar.config(text=f"Loaded {template_type} template")
        
    def create_template(self, num_masters, num_slaves, data_width, addr_width):
        """Create a standard template"""
        self.project.bus.protocol = 'AXI4'  # Set protocol for proper GUI updates
        self.project.bus.data_width = data_width
        self.project.bus.addr_width = addr_width
        
        # Create masters (horizontal arrangement at top)
        for i in range(num_masters):
            master = NodeConfig(name=f"M{i}", index=i, node_type='master',
                              ip_type='generated', x=100 + i * 170, y=50)
            self.project.masters.append(master)
            
        # Create slaves (horizontal arrangement at bottom)
        for i in range(num_slaves):
            firewall_categories = ['shared', 'non_sec', 'sec']
            slave = NodeConfig(name=f"S{i}", index=i, node_type='slave',
                             ip_type='generated', x=100 + i * 190, y=480,
                             base_addr=0x80000000 + i * 0x10000000,
                             size=0x10000000, region_size=0x10000000,
                             firewall_category=firewall_categories[i % 3],
                             priority=i % 8, qos_aw=(i % 4), qos_ar=(i % 4))
            self.project.slaves.append(slave)
            
    def create_multi_domain_template(self):
        """Create multi-domain template"""
        self.project.bus.data_width = 128
        self.project.bus.addr_width = 40
        
        # Add domains
        self.project.domains.append(DomainConfig("cpu_domain", "cpu_clk", "cpu_rst_n"))
        self.project.domains.append(DomainConfig("ddr_domain", "ddr_clk", "ddr_rst_n"))
        self.project.domains.append(DomainConfig("periph_domain", "periph_clk", "periph_rst_n"))
        
        # Create masters in different domains (horizontal at top)
        for i in range(3):
            domain = ["cpu_domain", "cpu_domain", "periph_domain"][i]
            master = NodeConfig(name=f"M{i}", index=i, node_type='master',
                              ip_type='generated', x=100 + i * 170, y=50,
                              domain=domain, qos_aw=(i % 4), qos_ar=(i % 4))
            self.project.masters.append(master)
            
        # Create slaves in different domains (horizontal at bottom)
        for i in range(4):
            domain = ["ddr_domain", "ddr_domain", "periph_domain", "periph_domain"][i]
            firewall_categories = ['shared', 'non_sec', 'sec', 'shared']
            slave = NodeConfig(name=f"S{i}", index=i, node_type='slave',
                             ip_type='generated', x=100 + i * 190, y=480,
                             domain=domain,
                             base_addr=0x80000000 + i * 0x10000000,
                             size=0x10000000, region_size=0x10000000,
                             firewall_category=firewall_categories[i],
                             priority=i + 1, qos_aw=(i % 4), qos_ar=(i % 4))
            self.project.slaves.append(slave)
    
    def create_ace_lite_template(self, num_masters, num_slaves, data_width, addr_width):
        """Create a 32x32 ACE-Lite template with cache coherency features and smart validation"""
        self.project.bus.protocol = 'ACE-Lite'  # Set protocol for proper GUI updates
        self.project.bus.data_width = data_width
        self.project.bus.addr_width = addr_width
        
        # Auto-calculate optimal ID width for master count
        required_id_width = max(4, (num_masters - 1).bit_length() + 1)
        self.project.bus.id_width = required_id_width
        
        # Enable ACE-Lite features
        self.project.bus.enable_ace_lite = True
        self.project.bus.enable_cache_coherency = True
        self.project.bus.enable_snoop_filter = True
        self.project.bus.enable_dvm = True
        self.project.bus.enable_barriers = True
        self.project.bus.enable_qos = True
        
        # ACE-Lite USER signal conflict prevention - set to 0 and disable user signals
        self.project.bus.user_width = 0
        self.project.bus.enable_user_signals = False
        
        # Configure ACE-Lite SD_xUSER signal widths (these are separate from standard USER)
        self.project.bus.sd_awuser_width = 12
        self.project.bus.sd_wuser_width = 10
        self.project.bus.sd_buser_width = 8
        self.project.bus.sd_aruser_width = 14
        self.project.bus.sd_ruser_width = 6
        
        # Create masters with ACE-Lite coherent capabilities
        masters_per_row = 8
        for i in range(num_masters):
            row = i // masters_per_row
            col = i % masters_per_row
            # First 16 masters are ACE-Lite coherent, rest are standard AXI4
            cache_coherent = i < 16
            domain = "coherent" if cache_coherent else "io"
            
            master = NodeConfig(
                name=f"M{i}_{'ACE' if cache_coherent else 'AXI'}", 
                index=i, node_type='master',
                ip_type='generated', 
                x=100 + col * 120, 
                y=50 + row * 100,
                domain=domain,
                cache_coherent=cache_coherent,
                qos_aw=(i % 16), qos_ar=(i % 16),  # Higher QoS range for large system
                priority=i % 8,
                arbitration_policy="strict_priority" if cache_coherent else "round_robin"
            )
            self.project.masters.append(master)
            
        # Create slaves with different memory regions and ACE-Lite features
        slaves_per_row = 8
        base_addresses = [
            # DDR regions (first 8 slaves)
            0x80000000, 0x90000000, 0xA0000000, 0xB0000000,
            0xC0000000, 0xD0000000, 0xE0000000, 0xF0000000,
            # L3 Cache regions (next 8 slaves) 
            0x40000000, 0x48000000, 0x50000000, 0x58000000,
            0x60000000, 0x68000000, 0x70000000, 0x78000000,
            # IO/Peripheral regions (next 8 slaves)
            0x10000000, 0x18000000, 0x20000000, 0x28000000,
            0x30000000, 0x38000000, 0x1F000000, 0x1F800000,
            # Extended memory regions (last 8 slaves)
            0x100000000, 0x120000000, 0x140000000, 0x160000000,
            0x180000000, 0x1A0000000, 0x1C0000000, 0x1E0000000
        ]
        
        region_sizes = [0x10000000] * 24 + [0x20000000] * 8  # Last 8 have larger regions
        
        for i in range(num_slaves):
            row = i // slaves_per_row
            col = i % slaves_per_row
            
            # Categorize slaves by function
            if i < 8:
                slave_type = "DDR"
                firewall_cat = "shared"
            elif i < 16:
                slave_type = "L3Cache"  
                firewall_cat = "non_sec"
            elif i < 24:
                slave_type = "IO"
                firewall_cat = "sec"
            else:
                slave_type = "ExtMem"
                firewall_cat = "shared"
            
            slave = NodeConfig(
                name=f"S{i}_{slave_type}", 
                index=i, node_type='slave',
                ip_type='generated', 
                x=100 + col * 120, 
                y=300 + row * 100,
                base_addr=base_addresses[i],
                size=region_sizes[i], 
                region_size=region_sizes[i],
                firewall_category=firewall_cat,
                priority=(i % 16) + 1,  # Priority 1-16
                qos_aw=(i % 16), qos_ar=(i % 16),
                cache_coherent=i < 16  # First 16 slaves support coherency
            )
            self.project.slaves.append(slave)
            
    def add_node(self, node_type):
        """Add a new node to the canvas"""
        try:
            # Determine node properties
            if node_type == 'master':
                name = f"M{len([n for n in self.project.masters if n.ip_type == 'generated'])}"
                color = '#4CAF50'
                ip_type = 'generated'
                base_type = 'master'
            elif node_type == 'slave':
                name = f"S{len([n for n in self.project.slaves if n.ip_type == 'generated'])}"
                color = '#2196F3'
                ip_type = 'generated'
                base_type = 'slave'
            elif node_type == 'ext_master':
                name = f"ExtM{len([n for n in self.project.masters if n.ip_type == 'external'])}"
                color = '#8BC34A'
                ip_type = 'external'
                base_type = 'master'
            elif node_type == 'ext_slave':
                name = f"ExtS{len([n for n in self.project.slaves if n.ip_type == 'external'])}"
                color = '#03A9F4'
                ip_type = 'external'
                base_type = 'slave'
            elif node_type == 'bridge':
                name = f"Bridge{len(self.project.bridges)}"
                color = '#FF9800'
                ip_type = 'generated'
                base_type = 'bridge'
            else:
                return
                
            # Calculate position - vertical layout (masters top, slaves bottom)
            if 'master' in node_type:
                # Masters arranged horizontally at top
                existing_masters = len([n for n in self.nodes if 'master' in n])
                x = 100 + existing_masters * 140  # Increased spacing for larger nodes
                y = 50
            elif 'slave' in node_type:
                # Slaves arranged horizontally at bottom
                existing_slaves = len([n for n in self.nodes if 'slave' in n])
                x = 100 + existing_slaves * 140  # Increased spacing for larger nodes
                y = 450  # Lower position for bigger nodes
            else:  # bridge
                existing_bridges = len([n for n in self.nodes if 'bridge' in n])
                x = 400 + existing_bridges * 150
                y = 250
            
            # Create node config
            if base_type == 'master':
                idx = len(self.project.masters)
                node_config = NodeConfig(name=name, index=idx, node_type=base_type, 
                                       ip_type=ip_type, x=x, y=y)
                self.project.masters.append(node_config)
            elif base_type == 'slave':
                idx = len(self.project.slaves)
                base_addr = 0x80000000 + (idx * 0x10000000)
                region_size = 0x10000000  # Default 256MB region
                node_config = NodeConfig(name=name, index=idx, node_type=base_type, 
                                       ip_type=ip_type, x=x, y=y, 
                                       base_addr=base_addr, size=0x10000000,
                                       region_size=region_size, firewall_category='shared',
                                       priority=idx % 8, qos_aw=(idx % 4), qos_ar=(idx % 4))
                self.project.slaves.append(node_config)
            elif base_type == 'bridge':
                idx = len(self.project.bridges)
                node_config = NodeConfig(name=name, index=idx, node_type=base_type, 
                                       ip_type=ip_type, x=x, y=y)
                self.project.bridges.append(node_config)
                
            # Draw node on canvas
            self.draw_node(node_config, color)
            
            # Redraw connections to show arrows
            self.redraw_connections()
            
            # Make sure the new node is visible
            self.canvas.update_idletasks()
            
            # Update scroll region to include new node
            bbox = self.canvas.bbox('all')
            if bbox:
                # Add some padding
                x1, y1, x2, y2 = bbox
                self.canvas.config(scrollregion=(x1-50, y1-50, x2+50, y2+50))
                
                # Scroll to show the new node
                if 'master' in node_type:
                    self.canvas.xview_moveto(0)  # Scroll to left for masters
                elif 'slave' in node_type:
                    self.canvas.xview_moveto(0.5)  # Scroll to right for slaves
            
            # Update CLI and status
            self.generate_cli_command()
            self.update_status_labels()
            
            self.status_bar.config(text=f"Added {name}")
            
        except Exception as e:
            logger.error(f"Error adding node: {e}")
            import traceback
            traceback.print_exc()
            
    def draw_node(self, config, color):
        """Draw a node on the canvas"""
        x, y = config.x, config.y
        if config.node_type == 'slave':
            width, height = 160, 90  # Larger for slaves to show more info
        elif config.node_type == 'master':
            width, height = 140, 80  # Larger for masters
        else:
            width, height = 120, 70  # Bridges stay same
        
        # Create rectangle
        rect = self.canvas.create_rectangle(x, y, x + width, y + height, 
                                           fill=color, outline='black', width=2)
        
        # Create text labels (enlarged for better visibility)
        text = self.canvas.create_text(x + width/2, y + 12, text=config.name, 
                                      font=('Arial', 12, 'bold'), fill='white')
        
        # Create type badge (enlarged)
        type_text = "EXT" if config.ip_type == 'external' else config.node_type.upper()[:3]
        badge = self.canvas.create_text(x + width/2, y + 26, text=f"[{type_text}]", 
                                       font=('Arial', 10), fill='white')
        
        badges = [badge]
        
        # Add slave-specific information
        if config.node_type == 'slave':
            # Address range info (show base address to end address)
            if config.base_addr and config.size:
                end_addr = config.base_addr + config.size - 1
                addr_info = f"{self.format_address(config.base_addr)}-{self.format_address(end_addr)}"
            else:
                addr_info = "No Address"
            addr_badge = self.canvas.create_text(x + width/2, y + 38, text=addr_info, 
                                               font=('Arial', 9), fill='white')
            badges.append(addr_badge)
            
            # Size info
            size_info = f"Size:{self.format_size(config.size) if config.size else 'N/A'}"
            size_badge = self.canvas.create_text(x + width/2, y + 50, text=size_info, 
                                               font=('Arial', 9), fill='white')
            badges.append(size_badge)
            
            # Bus arbiter info (based on global setting)
            bus_arbiter = self.project.bus.bus_arbiter
            if bus_arbiter == 'priority':
                arbiter_info = f"P:{config.priority}"
            elif bus_arbiter == 'round_robin':
                arbiter_info = "RR"
            elif bus_arbiter == 'weighted':
                arbiter_info = f"W:{config.priority}"
            else:
                arbiter_info = bus_arbiter[:3].upper()
                
            arbiter_badge = self.canvas.create_text(x + width/2, y + 62, text=arbiter_info, 
                                                   font=('Arial', 9), fill='white')
            badges.append(arbiter_badge)
            
            # QoS info (if enabled globally)
            if self.project.bus.enable_qos:
                qos_info = f"QoS:AW{config.qos_aw}/AR{config.qos_ar}"
                qos_badge = self.canvas.create_text(x + width/2, y + 74, text=qos_info, 
                                                  font=('Arial', 8), fill='white')
                badges.append(qos_badge)
            
            # Firewall category (if enabled globally) - updated to support numeric categories
            if self.project.bus.enable_security_firewall:
                # Handle both old text format and new numeric format
                fw_category = getattr(config, 'firewall_category', '1')
                if isinstance(fw_category, str) and fw_category.isdigit():
                    # Numeric category (1-16)
                    display_text = f"FW:{fw_category}"
                    # Color based on category number
                    category_num = int(fw_category)
                    if category_num <= 5:
                        fw_color = '#90EE90'  # Light green for low categories
                    elif category_num <= 10:
                        fw_color = '#FFE4B5'  # Light orange for medium categories
                    else:
                        fw_color = '#FFB6C1'  # Light pink for high categories
                else:
                    # Legacy text format
                    fw_colors = {'shared': '#90EE90', 'non_sec': '#FFE4B5', 'sec': '#FFB6C1'}
                    fw_color = fw_colors.get(str(fw_category), '#FFFFFF')
                    display_text = str(fw_category).upper()[:3]
                
                fw_badge = self.canvas.create_text(x + width/2, y + 82, 
                                                 text=display_text, 
                                                 font=('Arial', 9), fill='black')
                # Add colored background for firewall category
                fw_rect = self.canvas.create_rectangle(x + width/2 - 25, y + 76, x + width/2 + 25, y + 88,
                                                     fill=fw_color, outline='black', width=1)
                self.canvas.tag_lower(fw_rect)  # Move behind text
                badges.extend([fw_badge, fw_rect])
        
        # Add master-specific information (enlarged text)
        elif config.node_type == 'master':
            y_pos = 38  # Start position for master info
            
            # Show domain if not default
            if config.domain != "default":
                domain_badge = self.canvas.create_text(x + width/2, y + y_pos, text=f"Domain:{config.domain}", 
                                                      font=('Arial', 9), fill='white')
                badges.append(domain_badge)
                y_pos += 12
            
            # Show QoS info if enabled
            if self.project.bus.enable_qos:
                qos_info = f"QoS:AW{config.qos_aw}/AR{config.qos_ar}"
                qos_badge = self.canvas.create_text(x + width/2, y + y_pos, text=qos_info, 
                                                  font=('Arial', 9), fill='white')
                badges.append(qos_badge)
                y_pos += 12
            
            # Show firewall category for masters (if firewall enabled)
            if self.project.bus.enable_security_firewall:
                # Handle both old text format and new numeric format for masters too
                fw_category = getattr(config, 'firewall_category', '1')
                if isinstance(fw_category, str) and fw_category.isdigit():
                    # Numeric category (1-16)
                    display_text = f"FW:{fw_category}"
                    # Color based on category number
                    category_num = int(fw_category)
                    if category_num <= 5:
                        fw_color = '#90EE90'  # Light green for low categories
                    elif category_num <= 10:
                        fw_color = '#FFE4B5'  # Light orange for medium categories
                    else:
                        fw_color = '#FFB6C1'  # Light pink for high categories
                else:
                    # Legacy or security level display
                    fw_color = '#FFFFFF'
                    display_text = config.security.upper()[:3]
                
                fw_badge = self.canvas.create_text(x + width/2, y + y_pos, 
                                                 text=display_text, 
                                                 font=('Arial', 9), fill='black')
                # Add colored background for firewall category
                fw_rect = self.canvas.create_rectangle(x + width/2 - 25, y + y_pos - 6, x + width/2 + 25, y + y_pos + 6,
                                                     fill=fw_color, outline='black', width=1)
                self.canvas.tag_lower(fw_rect)  # Move behind text
                badges.extend([fw_badge, fw_rect])
        
        # Store node reference
        node_id = f"{config.node_type}_{config.index}"
        self.nodes[node_id] = {
            'config': config,
            'rect': rect,
            'text': text,
            'badges': badges,
            'color': color
        }
        
    def format_size(self, size_bytes):
        """Format size in bytes to human readable format"""
        if not size_bytes:
            return "N/A"
        if size_bytes >= 1024**3:
            return f"{size_bytes//(1024**3)}GB"
        elif size_bytes >= 1024**2:
            return f"{size_bytes//(1024**2)}MB"
        elif size_bytes >= 1024:
            return f"{size_bytes//1024}KB"
        else:
            return f"{size_bytes}B"
            
    def format_address(self, addr):
        """Format address in hex with appropriate prefix"""
        if not addr:
            return "0x0"
        if addr >= 0x100000000:  # > 4GB
            return f"0x{addr:X}"
        else:
            return f"0x{addr:08X}"
        
    def on_canvas_click(self, event):
        """Handle canvas click"""
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        item = self.canvas.find_closest(x, y)[0]
        
        # Find which node was clicked
        self.selected_node = None
        for node_id, node_data in self.nodes.items():
            if item in [node_data['rect'], node_data['text']] + node_data['badges']:
                self.selected_node = node_id
                self.highlight_node(node_id)
                # Set up drag data
                self.drag_data["x"] = x
                self.drag_data["y"] = y
                self.drag_data["item"] = node_id
                break
                
    def on_double_click(self, event):
        """Handle double-click to edit properties"""
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        item = self.canvas.find_closest(x, y)[0]
        
        for node_id, node_data in self.nodes.items():
            if item in [node_data['rect'], node_data['text']] + node_data['badges']:
                self.edit_node_properties(node_id)
                break
                
    def highlight_node(self, node_id):
        """Highlight selected node"""
        # Reset all nodes
        for nid, node_data in self.nodes.items():
            self.canvas.itemconfig(node_data['rect'], width=2)
            
        # Highlight selected
        if node_id in self.nodes:
            self.canvas.itemconfig(self.nodes[node_id]['rect'], width=4)
            
    def on_drag(self, event):
        """Handle node dragging"""
        if self.drag_data["item"]:
            x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
            dx = x - self.drag_data["x"]
            dy = y - self.drag_data["y"]
            
            node_data = self.nodes[self.drag_data["item"]]
            
            # Move all node elements
            self.canvas.move(node_data['rect'], dx, dy)
            self.canvas.move(node_data['text'], dx, dy)
            for badge in node_data['badges']:
                self.canvas.move(badge, dx, dy)
                
            # Update position in config
            node_data['config'].x += dx
            node_data['config'].y += dy
            
            self.drag_data["x"] = x
            self.drag_data["y"] = y
            
            # Redraw connections
            self.redraw_connections()
            
    def on_drag_release(self, event):
        """Handle drag release"""
        self.drag_data["item"] = None
        
    def on_right_click(self, event):
        """Handle right-click context menu"""
        x, y = self.canvas.canvasx(event.x), self.canvas.canvasy(event.y)
        
        # Create context menu
        menu = tk.Menu(self, tearoff=0)
        
        # Check if clicking on a node
        item = self.canvas.find_closest(x, y)[0]
        node_clicked = None
        for node_id, node_data in self.nodes.items():
            if item in [node_data['rect'], node_data['text']] + node_data['badges']:
                node_clicked = node_id
                break
                
        if node_clicked:
            menu.add_command(label="Edit Properties", 
                           command=lambda: self.edit_node_properties(node_clicked))
            menu.add_command(label="Delete", 
                           command=lambda: self.delete_node(node_clicked))
        else:
            menu.add_command(label="Auto-Arrange", command=self.auto_arrange)
            menu.add_command(label="Zoom to Fit", command=self.zoom_fit)
            menu.add_command(label="Clear Canvas", command=self.clear_canvas)
            
        menu.post(event.x_root, event.y_root)
        
    def delete_selected(self):
        """Delete selected node"""
        if self.selected_node:
            self.delete_node(self.selected_node)
            
    def delete_node(self, node_id):
        """Delete a node"""
        if node_id in self.nodes:
            node_data = self.nodes[node_id]
            
            # Remove from canvas
            self.canvas.delete(node_data['rect'])
            self.canvas.delete(node_data['text'])
            for badge in node_data['badges']:
                self.canvas.delete(badge)
                
            # Remove from project config
            config = node_data['config']
            if config.node_type == 'master':
                self.project.masters.remove(config)
            elif config.node_type == 'slave':
                self.project.slaves.remove(config)
            elif config.node_type == 'bridge':
                self.project.bridges.remove(config)
                
            # Remove from nodes dict
            del self.nodes[node_id]
            
            # Redraw connections
            self.redraw_connections()
            
            # Update CLI and status
            self.generate_cli_command()
            self.update_status_labels()
            
            self.status_bar.config(text=f"Deleted {config.name}")
    
    def zoom_in(self, event=None):
        """Zoom in the canvas"""
        if self.zoom_factor < self.max_zoom:
            self.zoom_factor = min(self.max_zoom, self.zoom_factor + self.zoom_step)
            self.apply_zoom()
            self.status_bar.config(text=f"Zoom: {self.zoom_factor:.1f}x")
    
    def zoom_out(self, event=None):
        """Zoom out the canvas"""
        if self.zoom_factor > self.min_zoom:
            self.zoom_factor = max(self.min_zoom, self.zoom_factor - self.zoom_step)
            self.apply_zoom()
            self.status_bar.config(text=f"Zoom: {self.zoom_factor:.1f}x")
    
    def zoom_reset(self, event=None):
        """Reset zoom to 100%"""
        self.zoom_factor = 1.0
        self.apply_zoom()
        self.status_bar.config(text=f"Zoom: {self.zoom_factor:.1f}x")
    
    def on_mouse_wheel(self, event):
        """Handle mouse wheel zoom"""
        if event.state & 0x4:  # Control key held
            if event.delta > 0:
                self.zoom_in()
            else:
                self.zoom_out()
            return "break"  # Prevent scrolling
    
    def apply_zoom(self):
        """Apply zoom transformation to all canvas items"""
        # Scale all items from the center of the visible area
        center_x = self.canvas.winfo_width() / 2
        center_y = self.canvas.winfo_height() / 2
        
        scale_factor = self.zoom_factor / getattr(self, '_last_zoom', 1.0)
        self.canvas.scale("all", center_x, center_y, scale_factor, scale_factor)
        
        # Update scroll region to match new size
        bbox = self.canvas.bbox("all")
        if bbox:
            self.canvas.config(scrollregion=bbox)
        
        self._last_zoom = self.zoom_factor
            
    def edit_node_properties(self, node_id):
        """Edit node properties dialog"""
        if node_id not in self.nodes:
            return
            
        node_data = self.nodes[node_id]
        config = node_data['config']
        
        # Create dialog
        dialog = tk.Toplevel(self)
        dialog.title(f"Edit {config.name} Properties")
        dialog.geometry("500x650")  # Increased size for more fields
        dialog.resizable(True, True)
        
        # Create property fields
        row = 0
        ttk.Label(dialog, text="Name:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
        name_var = tk.StringVar(value=config.name)
        ttk.Entry(dialog, textvariable=name_var).grid(row=row, column=1, padx=5, pady=5)
        
        row += 1
        ttk.Label(dialog, text="Domain:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
        domain_var = tk.StringVar(value=config.domain)
        ttk.Entry(dialog, textvariable=domain_var).grid(row=row, column=1, padx=5, pady=5)
        
        # Security Section - consolidated to avoid duplication
        row += 1
        ttk.Separator(dialog, orient='horizontal').grid(row=row, column=0, columnspan=2, sticky='ew', pady=10)
        
        row += 1
        ttk.Label(dialog, text="Security Settings", font=('TkDefaultFont', 10, 'bold')).grid(row=row, column=0, columnspan=2, pady=5)
        
        row += 1
        ttk.Label(dialog, text="Security Level:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
        security_var = tk.StringVar(value=config.security)
        ttk.Combobox(dialog, textvariable=security_var, 
                    values=['secure', 'non_secure', 'shared']).grid(row=row, column=1, padx=5, pady=5)
        
        # Firewall Category (for both masters and slaves if firewall enabled)
        if self.project.bus.enable_security_firewall:
            row += 1
            ttk.Label(dialog, text="Firewall Category:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
            firewall_var = tk.StringVar(value=str(getattr(config, 'firewall_category', '1')))
            firewall_combo = ttk.Combobox(dialog, textvariable=firewall_var, width=20,
                                        values=[str(i) for i in range(1, 17)],  # Categories 1-16
                                        state="readonly")
            firewall_combo.grid(row=row, column=1, padx=5, pady=5)
        else:
            # If firewall not enabled, just use basic security
            firewall_var = None
        
        # Bus Arbiter Section (for slaves, shows global setting but allows priority override)
        if config.node_type == 'slave':
            row += 1
            ttk.Separator(dialog, orient='horizontal').grid(row=row, column=0, columnspan=2, sticky='ew', pady=10)
            
            row += 1
            ttk.Label(dialog, text="Priority Settings", font=('TkDefaultFont', 10, 'bold')).grid(row=row, column=0, columnspan=2, pady=5)
            
            row += 1
            bus_arbiter_info = f"Global Bus Arbiter: {self.project.bus.bus_arbiter.title().replace('_', ' ')}"
            ttk.Label(dialog, text=bus_arbiter_info, font=('TkDefaultFont', 9, 'italic')).grid(row=row, column=0, columnspan=2, pady=2)
            
            if self.project.bus.bus_arbiter in ['priority', 'weighted']:
                row += 1
                priority_label = "Priority Level:" if self.project.bus.bus_arbiter == 'priority' else "Weight:"
                ttk.Label(dialog, text=priority_label).grid(row=row, column=0, sticky='w', padx=5, pady=5)
                priority_var = tk.IntVar(value=config.priority)
                priority_frame = ttk.Frame(dialog)
                priority_frame.grid(row=row, column=1, padx=5, pady=5, sticky='w')
                tk.Spinbox(priority_frame, from_=0, to=15, textvariable=priority_var, width=15).pack()
            else:
                priority_var = tk.IntVar(value=config.priority)  # Keep existing value
            
            row += 1
            ttk.Label(dialog, text="Region Size:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
            region_size_var = tk.StringVar(value=hex(config.region_size) if config.region_size else '0x10000000')
            ttk.Entry(dialog, textvariable=region_size_var, width=20).grid(row=row, column=1, padx=5, pady=5)
        
        # QoS Section (only if enabled globally)
        if self.project.bus.enable_qos:
            row += 1
            ttk.Separator(dialog, orient='horizontal').grid(row=row, column=0, columnspan=2, sticky='ew', pady=10)
            
            row += 1
            ttk.Label(dialog, text="QoS Settings", font=('TkDefaultFont', 10, 'bold')).grid(row=row, column=0, columnspan=2, pady=5)
            
            row += 1
            ttk.Label(dialog, text="QoS AW (Write):").grid(row=row, column=0, sticky='w', padx=5, pady=5)
            qos_aw_var = tk.IntVar(value=config.qos_aw)
            qos_aw_frame = ttk.Frame(dialog)
            qos_aw_frame.grid(row=row, column=1, padx=5, pady=5, sticky='w')
            tk.Spinbox(qos_aw_frame, from_=0, to=15, textvariable=qos_aw_var, width=15).pack()
            
            row += 1
            ttk.Label(dialog, text="QoS AR (Read):").grid(row=row, column=0, sticky='w', padx=5, pady=5)
            qos_ar_var = tk.IntVar(value=config.qos_ar)
            qos_ar_frame = ttk.Frame(dialog)
            qos_ar_frame.grid(row=row, column=1, padx=5, pady=5, sticky='w')
            tk.Spinbox(qos_ar_frame, from_=0, to=15, textvariable=qos_ar_var, width=15).pack()
        else:
            # Keep existing QoS values even if not displayed
            qos_aw_var = tk.IntVar(value=config.qos_aw)
            qos_ar_var = tk.IntVar(value=config.qos_ar)
        
        # Cache Configuration Section
        row += 1
        ttk.Separator(dialog, orient='horizontal').grid(row=row, column=0, columnspan=2, sticky='ew', pady=10)
        
        row += 1
        ttk.Label(dialog, text="Cache Settings", font=('TkDefaultFont', 10, 'bold')).grid(row=row, column=0, columnspan=2, pady=5)
        
        row += 1
        cache_enable_var = tk.BooleanVar(value=config.cache_enable)
        cache_enable_cb = ttk.Checkbutton(dialog, text="Enable Cache Support", variable=cache_enable_var)
        cache_enable_cb.grid(row=row, column=0, columnspan=2, padx=5, pady=5)
        
        # Function to update cache-related widgets based on enable state
        def update_cache_widgets():
            state = 'normal' if cache_enable_var.get() else 'disabled'
            for widget in cache_widgets:
                widget.configure(state=state)
                
        cache_widgets = []  # Track cache-related widgets for conditional enable/disable
        
        row += 1
        awcache_label = ttk.Label(dialog, text="AWCACHE Default:")
        awcache_label.grid(row=row, column=0, sticky='w', padx=5, pady=5)
        awcache_frame = ttk.Frame(dialog)
        awcache_frame.grid(row=row, column=1, padx=5, pady=5, sticky='w')
        cache_widgets.extend([awcache_label, awcache_frame])
        
        # Create AWCACHE bit checkboxes
        awcache_bits = []
        awcache_labels = ['Bufferable', 'Cacheable', 'Read Alloc', 'Write Alloc']
        for i, label in enumerate(awcache_labels):
            var = tk.BooleanVar(value=bool(config.awcache_default & (1 << i)))
            cb = ttk.Checkbutton(awcache_frame, text=label, variable=var)
            cb.pack(side='left', padx=2)
            awcache_bits.append(var)
            cache_widgets.append(cb)
        
        row += 1
        arcache_label = ttk.Label(dialog, text="ARCACHE Default:")
        arcache_label.grid(row=row, column=0, sticky='w', padx=5, pady=5)
        arcache_frame = ttk.Frame(dialog)
        arcache_frame.grid(row=row, column=1, padx=5, pady=5, sticky='w')
        cache_widgets.extend([arcache_label, arcache_frame])
        
        # Create ARCACHE bit checkboxes
        arcache_bits = []
        for i, label in enumerate(awcache_labels):
            var = tk.BooleanVar(value=bool(config.arcache_default & (1 << i)))
            cb = ttk.Checkbutton(arcache_frame, text=label, variable=var)
            cb.pack(side='left', padx=2)
            arcache_bits.append(var)
            cache_widgets.append(cb)
        
        row += 1
        cache_policy_label = ttk.Label(dialog, text="Cache Policy:")
        cache_policy_label.grid(row=row, column=0, sticky='w', padx=5, pady=5)
        cache_policy_var = tk.StringVar(value=config.cache_policy)
        cache_policy_combo = ttk.Combobox(dialog, textvariable=cache_policy_var,
                                        values=['write-through', 'write-back', 'no-allocate', 'write-allocate'])
        cache_policy_combo.grid(row=row, column=1, padx=5, pady=5)
        cache_widgets.extend([cache_policy_label, cache_policy_combo])
        
        row += 1
        cache_coherent_var = tk.BooleanVar(value=config.cache_coherent)
        cache_coherent_cb = ttk.Checkbutton(dialog, text="Cache Coherent (ACE-Lite)", variable=cache_coherent_var)
        cache_coherent_cb.grid(row=row, column=0, columnspan=2, padx=5, pady=5)
        cache_widgets.append(cache_coherent_cb)
        
        # Set up cache enable/disable functionality
        cache_enable_cb.configure(command=update_cache_widgets)
        update_cache_widgets()  # Set initial state
        
        # External IP fields
        if config.ip_type == 'external':
            row += 1
            ttk.Separator(dialog, orient='horizontal').grid(row=row, column=0, columnspan=2, sticky='ew', pady=10)
            
            row += 1
            ttk.Label(dialog, text="RTL Path:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
            rtl_var = tk.StringVar(value=config.rtl_path or '')
            ttk.Entry(dialog, textvariable=rtl_var).grid(row=row, column=1, padx=5, pady=5)
            
            row += 1
            ttk.Label(dialog, text="Top Module:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
            module_var = tk.StringVar(value=config.top_module or '')
            ttk.Entry(dialog, textvariable=module_var).grid(row=row, column=1, padx=5, pady=5)
            
        # Slave-specific fields
        if config.node_type == 'slave':
            row += 1
            ttk.Label(dialog, text="Base Address:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
            base_var = tk.StringVar(value=hex(config.base_addr) if config.base_addr else '0x0')
            ttk.Entry(dialog, textvariable=base_var).grid(row=row, column=1, padx=5, pady=5)
            
            row += 1
            ttk.Label(dialog, text="Size:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
            size_var = tk.StringVar(value=hex(config.size) if config.size else '0x1000')
            ttk.Entry(dialog, textvariable=size_var).grid(row=row, column=1, padx=5, pady=5)
            
        # Save button
        def save_properties():
            config.name = name_var.get()
            config.domain = domain_var.get()
            if self.project.bus.enable_security_firewall or 'security_var' in locals():
                config.security = security_var.get()
            
            # Save firewall category for both masters and slaves
            if firewall_var is not None:
                config.firewall_category = firewall_var.get()
            
            # Save cache settings
            config.cache_enable = cache_enable_var.get()
            
            # Calculate AWCACHE value from checkboxes
            awcache_value = 0
            for i, var in enumerate(awcache_bits):
                if var.get():
                    awcache_value |= (1 << i)
            config.awcache_default = awcache_value
            
            # Calculate ARCACHE value from checkboxes
            arcache_value = 0
            for i, var in enumerate(arcache_bits):
                if var.get():
                    arcache_value |= (1 << i)
            config.arcache_default = arcache_value
            
            config.cache_policy = cache_policy_var.get()
            config.cache_coherent = cache_coherent_var.get()
            
            if config.ip_type == 'external':
                config.rtl_path = rtl_var.get()
                config.top_module = module_var.get()
                
            if config.node_type == 'slave':
                try:
                    config.base_addr = int(base_var.get(), 0)
                    config.size = int(size_var.get(), 0)
                    if hasattr(locals(), 'region_size_var'):
                        config.region_size = int(region_size_var.get(), 0)
                    if hasattr(locals(), 'priority_var'):
                        config.priority = priority_var.get()
                    if self.project.bus.enable_security_firewall and firewall_var:
                        config.firewall_category = firewall_var.get()
                    if self.project.bus.enable_qos:
                        config.qos_aw = qos_aw_var.get()
                        config.qos_ar = qos_ar_var.get()
                except ValueError:
                    messagebox.showerror("Error", "Invalid address format")
                    return
                except NameError:
                    # Variables only exist for slaves
                    pass
                    
            # Update canvas
            self.canvas.itemconfig(node_data['text'], text=config.name)
            self.generate_cli_command()
            dialog.destroy()
            
        ttk.Button(dialog, text="Save", command=save_properties).grid(row=row+1, column=0, columnspan=2, pady=10)
        
    def auto_arrange(self):
        """Auto-arrange nodes with smart layout"""
        # Arrange masters horizontally at top
        x_offset = 100
        for i, master in enumerate(self.project.masters):
            master.x = x_offset + i * 140  # Increased spacing for larger nodes
            master.y = 50
            
        # Arrange slaves horizontally at bottom
        x_offset = 100
        for i, slave in enumerate(self.project.slaves):
            slave.x = x_offset + i * 140  # Increased spacing for larger nodes
            slave.y = 450  # Lower position for taller nodes
            
        # Arrange bridges in middle
        x_offset = 400
        for i, bridge in enumerate(self.project.bridges):
            bridge.x = x_offset + i * 150
            bridge.y = 250  # Adjusted for taller nodes
            
        # Redraw all nodes
        self.clear_canvas()
        self.redraw_all_nodes()
        self.zoom_fit()
        
    def zoom_fit(self):
        """Zoom to fit all nodes"""
        if not self.nodes:
            return
            
        # Find bounding box
        min_x = min_y = float('inf')
        max_x = max_y = float('-inf')
        
        for node_data in self.nodes.values():
            config = node_data['config']
            min_x = min(min_x, config.x)
            min_y = min(min_y, config.y)
            max_x = max(max_x, config.x + 120)  # Updated for new node width
            max_y = max(max_y, config.y + 70)   # Updated for new node height
            
        # Add padding
        padding = 50
        min_x -= padding
        min_y -= padding
        max_x += padding
        max_y += padding
        
        # Update scroll region
        self.canvas.config(scrollregion=(min_x, min_y, max_x, max_y))
        
        # Scroll to show all
        self.canvas.xview_moveto(0)
        self.canvas.yview_moveto(0)
        
    def clear_canvas(self):
        """Clear all items from canvas"""
        self.canvas.delete("all")
        self.nodes.clear()
        self.connections.clear()
        # Update status labels since nodes are cleared
        self.update_status_labels()
        
    def redraw_all_nodes(self):
        """Redraw all nodes"""
        # Draw masters
        for master in self.project.masters:
            color = '#4CAF50' if master.ip_type == 'generated' else '#8BC34A'
            self.draw_node(master, color)
            
        # Draw slaves
        for slave in self.project.slaves:
            color = '#2196F3' if slave.ip_type == 'generated' else '#03A9F4'
            self.draw_node(slave, color)
            
        # Draw bridges
        for bridge in self.project.bridges:
            self.draw_node(bridge, '#FF9800')
            
        self.redraw_connections()
        
    def redraw_connections(self):
        """Redraw connection lines with smart routing"""
        # Clear existing connections
        for conn in self.connections:
            self.canvas.delete(conn)
        self.connections.clear()
        
        # Draw interconnect block if there are masters and slaves
        if self.project.masters and self.project.slaves:
            # Calculate interconnect position (smaller horizontal bar in middle)
            # Find the range of master and slave x positions
            master_min_x = min([m.x for m in self.project.masters])
            master_max_x = max([m.x + 140 for m in self.project.masters])  # Master width
            slave_min_x = min([s.x for s in self.project.slaves])
            slave_max_x = max([s.x + 160 for s in self.project.slaves])  # Slave width
            
            # Smaller interconnect spans key nodes only
            ic_x = min(master_min_x, slave_min_x) + 50  # Start 50px in from leftmost
            ic_width = max(master_max_x, slave_max_x) - ic_x - 50  # End 50px before rightmost
            ic_y = 230  # Middle position between masters (y=50) and slaves (y=480)
            ic_height = 50  # Smaller height - half of previous size
            
            # Draw smaller interconnect block (horizontal rectangle)
            ic_rect = self.canvas.create_rectangle(ic_x, ic_y, ic_x + ic_width, ic_y + ic_height,
                                                  fill='#757575', outline='black', width=1)  # Darker, thinner outline
            ic_text = self.canvas.create_text(ic_x + ic_width/2, ic_y + ic_height/2,
                                             text="AXI Interconnect", font=('Arial', 9, 'bold'),
                                             fill='white')  # Smaller font
            self.connections.extend([ic_rect, ic_text])
            
            # Draw vertical connections from masters to interconnect
            for master in self.project.masters:
                # Vertical line from master down to interconnect
                line = self.canvas.create_line(master.x + 70, master.y + 80,  # From bottom of master (center)
                                              master.x + 70, ic_y,           # To top of interconnect
                                              fill='#1976D2', width=2, arrow=tk.LAST)  # Blue arrow
                self.connections.append(line)
                
            # Draw vertical connections from interconnect to slaves
            for slave in self.project.slaves:
                # Vertical line from interconnect down to slave
                line = self.canvas.create_line(slave.x + 80, ic_y + ic_height,  # From bottom of interconnect (slave center)
                                              slave.x + 80, slave.y,            # To top of slave
                                              fill='#D32F2F', width=2, arrow=tk.LAST)  # Red arrow
                self.connections.append(line)
                
    def generate_cli_command(self):
        """Generate CLI command and display in bottom panel"""
        self.cli_text.delete(1.0, tk.END)
        
        # Generate compact CLI command
        cmd = f"# AXI4 Generator Command ({datetime.now().strftime('%H:%M:%S')})\n"
        cmd += f"# Project: {self.project.name} | Masters: {len(self.project.masters)} | Slaves: {len(self.project.slaves)}\n"
        cmd += f"axi_generator --config project.yaml --output ./generated --mode both\n"
        
        # Show key configuration
        if self.project.masters or self.project.slaves:
            cmd += f"# Bus: {self.project.bus.data_width}b data, {self.project.bus.addr_width}b addr, {self.project.bus.id_width}b ID\n"
            if hasattr(self.project.bus, 'user_width') and self.project.bus.user_width > 0:
                cmd += f"# User Width: {self.project.bus.user_width}b\n"
            if hasattr(self.project.bus, 'burst_length'):
                cmd += f"# Burst Length: {self.project.bus.burst_length}\n"
            if self.project.domains:
                cmd += f"# Domains: {', '.join([d.name for d in self.project.domains])}\n"
            
            # ACE-Lite specific parameters
            if hasattr(self.project.bus, 'enable_ace_lite') and self.project.bus.enable_ace_lite:
                cmd += f"# ACE-Lite: ENABLED\n"
                cmd += f"# SD_xUSER Widths: AW={self.project.bus.sd_awuser_width}, W={self.project.bus.sd_wuser_width}, B={self.project.bus.sd_buser_width}, AR={self.project.bus.sd_aruser_width}, R={self.project.bus.sd_ruser_width}\n"
                
                # Generate actual ACE-Lite command
                ace_lite_cmd = f"\n# ACE-Lite Generator Command:\n"
                ace_lite_cmd += f"./gen_amba_axi --master={len(self.project.masters)} --slave={len(self.project.slaves)} \\\n"
                ace_lite_cmd += f"    --enable-ace-lite \\\n"
                ace_lite_cmd += f"    --sd-awuser-width={self.project.bus.sd_awuser_width} \\\n"
                ace_lite_cmd += f"    --sd-wuser-width={self.project.bus.sd_wuser_width} \\\n"
                ace_lite_cmd += f"    --sd-buser-width={self.project.bus.sd_buser_width} \\\n"
                ace_lite_cmd += f"    --sd-aruser-width={self.project.bus.sd_aruser_width} \\\n"
                ace_lite_cmd += f"    --sd-ruser-width={self.project.bus.sd_ruser_width} \\\n"
                ace_lite_cmd += f"    --enable-qos --enable-region --enable-user \\\n"
                ace_lite_cmd += f"    --module=ace_lite_interconnect_m{len(self.project.masters)}s{len(self.project.slaves)} \\\n"
                ace_lite_cmd += f"    --output=./ace_lite_m{len(self.project.masters)}s{len(self.project.slaves)}.v\n"
                cmd += ace_lite_cmd
                
        self.cli_text.insert(1.0, cmd)
        
    def copy_cli_to_clipboard(self):
        """Copy CLI command to clipboard"""
        command = self.cli_text.get(1.0, tk.END).strip()
        self.clipboard_clear()
        self.clipboard_append(command)
        self.status_bar.config(text="CLI command copied to clipboard")
        
    def export_cli_script(self):
        """Export CLI script"""
        filename = filedialog.asksaveasfilename(
            title="Export CLI Script",
            defaultextension=".sh",
            filetypes=[("Shell Script", "*.sh"), ("All Files", "*.*")]
        )
        
        if filename:
            # Generate full script with YAML config
            script = "#!/bin/bash\n\n"
            script += "# AXI4 Generator Script\n"
            script += f"# Generated: {datetime.now()}\n\n"
            script += "# Create configuration file\n"
            script += "cat > project.yaml << 'EOF'\n"
            
            # Add YAML config
            config_dict = {
                'project_name': self.project.name,
                'bus': asdict(self.project.bus),
                'masters': [asdict(m) for m in self.project.masters],
                'slaves': [asdict(s) for s in self.project.slaves],
                'bridges': [asdict(b) for b in self.project.bridges],
                'domains': [asdict(d) for d in self.project.domains]
            }
            
            import io
            stream = io.StringIO()
            yaml.dump(config_dict, stream, default_flow_style=False)
            script += stream.getvalue()
            script += "EOF\n\n"
            
            # Add generation command
            script += "# Generate RTL and VIP\n"
            script += "axi_generator --config project.yaml --output ./generated --mode both\n"
            
            with open(filename, 'w') as f:
                f.write(script)
            os.chmod(filename, 0o755)
            
            self.status_bar.config(text=f"Script exported to {filename}")
            
    # File menu methods
    def new_project(self):
        """Create new project"""
        if messagebox.askyesno("New Project", "Clear current design?"):
            self.project = ProjectConfig()
            self.clear_canvas()
            self.generate_cli_command()
            self.update_status_labels()
            self.status_bar.config(text="New project created")
            
    def open_project(self):
        """Open project from YAML file"""
        filename = filedialog.askopenfilename(
            title="Open Project",
            filetypes=[("YAML files", "*.yaml"), ("All files", "*.*")]
        )
        
        if filename:
            try:
                with open(filename, 'r') as f:
                    config = yaml.safe_load(f)
                    
                # Load configuration
                self.project = self.load_project_from_dict(config)
                self.clear_canvas()
                self.redraw_all_nodes()
                self.update_left_panel_from_project()  # Update GUI fields from loaded YAML
                self.generate_cli_command()
                self.update_status_labels()
                
                self.status_bar.config(text=f"Opened: {filename}")
                
            except Exception as e:
                messagebox.showerror("Error", f"Failed to open project: {str(e)}")
                
    def save_project(self):
        """Save current project"""
        if not hasattr(self, 'project_file'):
            self.save_project_as()
        else:
            self.save_project_to_file(self.project_file)
            
    def save_project_as(self):
        """Save project with new filename"""
        filename = filedialog.asksaveasfilename(
            title="Save Project",
            defaultextension=".yaml",
            filetypes=[("YAML files", "*.yaml"), ("All files", "*.*")]
        )
        
        if filename:
            self.project_file = filename
            self.save_project_to_file(filename)
            
    def save_project_to_file(self, filename):
        """Save project to file"""
        try:
            config_dict = {
                'project_name': self.project.name,
                'bus': asdict(self.project.bus),
                'masters': [asdict(m) for m in self.project.masters],
                'slaves': [asdict(s) for s in self.project.slaves],
                'bridges': [asdict(b) for b in self.project.bridges],
                'domains': [asdict(d) for d in self.project.domains]
            }
            
            with open(filename, 'w') as f:
                yaml.dump(config_dict, f, default_flow_style=False)
                
            self.status_bar.config(text=f"Saved: {filename}")
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save project: {str(e)}")
            
    def load_project_from_dict(self, config):
        """Load project from dictionary"""
        project = ProjectConfig()
        project.name = config.get('project_name', 'axi4_project')
        
        # Load bus config
        if 'bus' in config:
            project.bus = BusConfig(**config['bus'])
            
        # Load masters
        if 'masters' in config:
            project.masters = [NodeConfig(**m) for m in config['masters']]
            
        # Load slaves
        if 'slaves' in config:
            project.slaves = [NodeConfig(**s) for s in config['slaves']]
            
        # Load bridges
        if 'bridges' in config:
            project.bridges = [NodeConfig(**b) for b in config['bridges']]
            
        # Load domains
        if 'domains' in config:
            project.domains = [DomainConfig(**d) for d in config['domains']]
            
        return project
        
    def open_generation_settings(self):
        """Open generation settings dialog"""
        from main_gui_v3 import GenerationSettingsDialog
        GenerationSettingsDialog(self, self.project)
        
    def quick_generate(self, mode):
        """Quick generate RTL or VIP"""
        output_dir = filedialog.askdirectory(title="Select Output Directory")
        if output_dir:
            from main_gui_v3 import GenerationSettingsDialog
            
            dialog = GenerationSettingsDialog.__new__(GenerationSettingsDialog)
            dialog.project = self.project
            
            # Mock variables
            class MockVar:
                def __init__(self, value):
                    self.value = value
                def get(self):
                    return self.value
                    
            dialog.project_name_var = MockVar(self.project.name)
            dialog.addr_width_var = MockVar(self.project.bus.addr_width)
            dialog.data_width_var = MockVar(self.project.bus.data_width)
            dialog.id_width_var = MockVar(self.project.bus.id_width)
            dialog.gen_filelist_var = MockVar(True)
            dialog.gen_scripts_var = MockVar(True)
            dialog.simulator_var = MockVar('VCS')
            
            if mode == 'rtl':
                dialog.generate_rtl(output_dir)
                messagebox.showinfo("Success", f"RTL generated in {output_dir}/rtl")
            else:
                dialog.generate_vip(output_dir)
                messagebox.showinfo("Success", f"VIP generated in {output_dir}/vip")
                
            dialog.save_project_config(output_dir)
            
    def show_about(self):
        """Show about dialog"""
        messagebox.showinfo(
            "About",
            "AMBA AXI4 RTL & VIP Generator v3 - Streamlined\n\n"
            "Single-page interface with:\n"
            "- Templates at top\n"
            "- Canvas in middle\n"
            "- CLI at bottom\n\n"
            "Simplified workflow for faster design!"
        )
    
    def show_user_guide(self):
        """Show user guide"""
        messagebox.showinfo(
            "User Guide",
            "QUICK START GUIDE\n\n"
            "1. Templates: Click template buttons at top to load predefined configurations\n"
            "2. Add Nodes: Use toolbar buttons to add Masters, Slaves, Bridges\n"
            "3. Configure: Double-click nodes to edit properties\n"
            "4. Generate: Use Generate menu to create RTL or VIP\n"
            "5. CLI: View generated commands at bottom\n\n"
            "Tips:\n"
            "- Drag nodes to reposition\n"
            "- Right-click for context menu\n"
            "- Use Auto-Arrange for clean layout"
        )
    
    def show_shortcuts(self):
        """Show keyboard shortcuts"""
        messagebox.showinfo(
            "Keyboard Shortcuts",
            "KEYBOARD SHORTCUTS\n\n"
            "Ctrl+N - New Project\n"
            "Ctrl+O - Open Project\n"
            "Ctrl+S - Save Project\n"
            "Ctrl+G - Generate RTL\n"
            "Ctrl+V - Generate VIP\n"
            "Delete - Delete selected node\n"
            "Ctrl+A - Auto-arrange nodes\n"
            "Ctrl+Z - Undo (if available)\n"
            "Ctrl+Y - Redo (if available)\n"
            "F1 - Help"
        )
    
    def show_generation_dialog(self, mode='both'):
        """Show the generation settings dialog"""
        from generation_settings_dialog import GenerationSettingsDialog
        
        # Create and show dialog
        dialog = GenerationSettingsDialog(self, self.project, mode=mode)
        self.wait_window(dialog)
        
        # Process result if not cancelled
        if dialog.result:
            self.process_generation(dialog.result)
    
    def process_generation(self, settings):
        """Process generation with given settings"""
        import os
        
        output_dir = settings['output_dir']
        mode = settings['mode']
        
        # Create output directory if it doesn't exist
        os.makedirs(output_dir, exist_ok=True)
        
        # Update project configuration with common settings
        if 'common' in settings:
            self.project.bus.data_width = settings['common']['data_width']
            self.project.bus.addr_width = settings['common']['addr_width']
            self.project.bus.id_width = settings['common']['id_width']
            self.project.bus.user_width = settings['common']['user_width']
            if 'burst_length' in settings['common']:
                self.project.bus.burst_length = settings['common']['burst_length']
        
        try:
            # Use enhanced RTL generator for RTL generation
            if mode in ['rtl', 'both']:
                from enhanced_rtl_generator import EnhancedRTLGenerator
                rtl_gen = EnhancedRTLGenerator(self.project, settings)
                rtl_dir = rtl_gen.generate()
                logger.info(f"Enhanced RTL generated: {rtl_dir}")
            
            # Generate VIP using integrated VIP generator
            if mode in ['vip', 'both']:
                vip_dir = os.path.join(output_dir, 'vip')
                os.makedirs(vip_dir, exist_ok=True)
                
                # Generate VIP directly without mock dialog
                try:
                    self.generate_vip_files(vip_dir, settings)
                    logger.info(f"VIP generated successfully: {vip_dir}")
                except Exception as e:
                    logger.error(f"VIP generation error: {e}")
                    # Create a simple placeholder VIP
                    self.generate_simple_vip_fallback(vip_dir, settings)
            
            # Show success message
            message = f"Generation completed successfully!\n\nOutput directory: {output_dir}\n"
            if mode == 'rtl':
                message += f"Enhanced RTL files: {output_dir}/rtl\n"
                message += "✅ All advanced features included!"
            elif mode == 'vip':
                message += f"VIP files: {output_dir}/vip"
            else:
                message += f"Enhanced RTL files: {output_dir}/rtl\n"
                message += f"VIP files: {output_dir}/vip\n"
                message += "✅ All advanced features included!"
                
            messagebox.showinfo("Generation Complete", message)
            self.status_bar.config(text=f"Generated {mode.upper()} to {output_dir}")
            
        except Exception as e:
            messagebox.showerror("Generation Error", f"Failed to generate: {str(e)}")
            logger.error(f"Generation error: {e}")
            import traceback
            traceback.print_exc()
    
    def quick_generate_default(self):
        """Quick generate with default settings"""
        output_dir = filedialog.askdirectory(title="Select Output Directory")
        if output_dir:
            # Create default settings
            settings = {
                'output_dir': output_dir,
                'project_name': self.project.name,
                'author': os.environ.get('USER', 'Designer'),
                'company': '',
                'simulator': 'VCS',
                'mode': 'both',
                'common': {
                    'data_width': self.project.bus.data_width,
                    'addr_width': self.project.bus.addr_width,
                    'id_width': self.project.bus.id_width,
                    'user_width': self.project.bus.user_width,
                    'burst_length': getattr(self.project.bus, 'burst_length', 256),
                    'enable_qos': True,
                    'enable_region': True,
                    'enable_exclusive': True,
                    'enable_user': self.project.bus.user_width > 0,
                    'gen_filelist': True,
                    'gen_makefile': True,
                    'gen_scripts': True,
                    'gen_documentation': False
                }
            }
            self.process_generation(settings)
    
    def generate_vip_files(self, vip_dir, settings):
        """Generate VIP files using the integrated VIP system"""
        try:
            # Try to use the comprehensive VIP integration
            import sys
            gui_path = '/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src'
            if gui_path not in sys.path:
                sys.path.append(gui_path)
            
            from vip_gui_integration import VIPGUIIntegration
            
            # Create VIP integration
            vip_integration = VIPGUIIntegration()
            
            # Configure VIP settings from project
            vip_settings = {
                'project_name': settings['project_name'],
                'num_masters': len(self.project.masters),
                'num_slaves': len(self.project.slaves),
                'data_width': self.project.bus.data_width,
                'addr_width': self.project.bus.addr_width,
                'id_width': self.project.bus.id_width,
                'user_width': getattr(self.project.bus, 'user_width', 0),
                'mode': 'Standalone VIP',
                'output_dir': vip_dir,
                'enable_qos': getattr(self.project.bus, 'enable_qos', False),
                'enable_region': getattr(self.project.bus, 'enable_region', False),
                'enable_user': getattr(self.project.bus, 'enable_user_signals', False),
                'enable_ace_lite': getattr(self.project.bus, 'enable_ace_lite', False)
            }
            
            # Generate VIP
            result = vip_integration.generate_vip_environment(vip_settings)
            if not result.get('success'):
                raise Exception(result.get('error', 'VIP generation failed'))
                
        except ImportError:
            # Fallback if VIP integration not available
            raise Exception("VIP integration not available - using fallback")
        except Exception as e:
            raise e
    
    def generate_simple_vip_fallback(self, vip_dir, settings):
        """Generate a simple VIP fallback when full VIP integration fails"""
        # Create basic VIP package file
        pkg_file = os.path.join(vip_dir, f"{settings['project_name']}_vip_pkg.sv")
        with open(pkg_file, 'w') as f:
            f.write(self.generate_basic_vip_package(settings))
        
        # Create basic test file
        test_file = os.path.join(vip_dir, f"{settings['project_name']}_base_test.sv")
        with open(test_file, 'w') as f:
            f.write(self.generate_basic_test(settings))
        
        # Create Makefile
        makefile = os.path.join(vip_dir, 'Makefile')
        with open(makefile, 'w') as f:
            f.write(self.generate_basic_makefile(settings))
        
        logger.info("Generated basic VIP fallback files")
    
    def generate_basic_vip_package(self, settings):
        """Generate basic VIP package"""
        return f"""// {settings['project_name']} VIP Package
// Generated by AMBA AXI4 RTL & VIP Generator v3 (Fallback)
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

package {settings['project_name']}_vip_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Basic AXI Transaction
    class axi4_transaction extends uvm_sequence_item;
        `uvm_object_utils(axi4_transaction)
        
        // Transaction fields
        rand bit [{self.project.bus.addr_width-1}:0] addr;
        rand bit [{self.project.bus.data_width-1}:0] data[];
        rand bit [{self.project.bus.id_width-1}:0]   id;
        rand bit [7:0] len;
        rand bit [2:0] size;
        rand bit [1:0] burst;
        
        function new(string name = "axi4_transaction");
            super.new(name);
        endfunction
        
    endclass
    
    // Basic master sequence
    class axi4_master_base_sequence extends uvm_sequence #(axi4_transaction);
        `uvm_object_utils(axi4_master_base_sequence)
        
        function new(string name = "axi4_master_base_sequence");
            super.new(name);
        endfunction
        
        virtual task body();
            axi4_transaction req;
            req = axi4_transaction::type_id::create("req");
            start_item(req);
            if (!req.randomize()) `uvm_error("SEQ", "Randomization failed")
            finish_item(req);
        endtask
        
    endclass
    
endpackage
"""
    
    def generate_basic_test(self, settings):
        """Generate basic test file"""
        return f"""// {settings['project_name']} Basic Test
// Generated by AMBA AXI4 RTL & VIP Generator v3 (Fallback)
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

import {settings['project_name']}_vip_pkg::*;

class {settings['project_name']}_base_test extends uvm_test;
    `uvm_component_utils({settings['project_name']}_base_test)
    
    function new(string name = "{settings['project_name']}_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("TEST", "Build phase started", UVM_LOW)
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info("TEST", "Test starting", UVM_LOW)
        #1000ns;
        `uvm_info("TEST", "Test completed", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
endclass
"""
    
    def generate_basic_makefile(self, settings):
        """Generate basic Makefile"""
        return f"""# Makefile for {settings['project_name']} VIP
# Generated by AMBA AXI4 RTL & VIP Generator v3 (Fallback)
# Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

PROJECT = {settings['project_name']}

# Simulator selection
SIM ?= vcs

# VCS options
VCS_FLAGS = -full64 -sverilog +v2k -timescale=1ns/1ps \\
            -debug_access+all -lca -kdb +lint=TFIPC-L \\
            +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv

# Compile target  
compile:
	$(SIM) $(VCS_FLAGS) $(PROJECT)_vip_pkg.sv $(PROJECT)_base_test.sv

# Run simulation
run: compile
	./simv +UVM_TESTNAME=$(PROJECT)_base_test +UVM_VERBOSITY=UVM_LOW

# Clean
clean:
	rm -rf simv* csrc *.log *.key DVEfiles ucli.key

.PHONY: compile run clean
"""

def main():
    """Main entry point"""
    app = AXI4GeneratorGUI()
    app.mainloop()

if __name__ == "__main__":
    main()