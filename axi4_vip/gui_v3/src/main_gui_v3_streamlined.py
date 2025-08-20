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
    base_addr: Optional[int] = None
    size: Optional[int] = None
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
    arbitration: str = "round_robin"
    
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
        ttk.Button(canvas_tools, text="Zoom Fit", 
                  command=self.zoom_fit).pack(side=tk.LEFT, padx=2)
        ttk.Button(canvas_tools, text="Clear All", 
                  command=self.clear_canvas).pack(side=tk.LEFT, padx=2)
        
        # Middle Frame - Canvas (main work area)
        middle_frame = ttk.Frame(self)
        middle_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Canvas with scrollbars
        canvas_frame = ttk.Frame(middle_frame)
        canvas_frame.pack(fill=tk.BOTH, expand=True)
        
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
        
        # Canvas bindings
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_drag_release)
        self.canvas.bind("<Button-3>", self.on_right_click)
        self.canvas.bind("<Double-Button-1>", self.on_double_click)
        
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
        elif template_type == 'multi_domain':
            self.create_multi_domain_template()
            
        self.redraw_all_nodes()
        self.auto_arrange()
        self.generate_cli_command()
        self.status_bar.config(text=f"Loaded {template_type} template")
        
    def create_template(self, num_masters, num_slaves, data_width, addr_width):
        """Create a standard template"""
        self.project.bus.data_width = data_width
        self.project.bus.addr_width = addr_width
        
        # Create masters (horizontal arrangement at top)
        for i in range(num_masters):
            master = NodeConfig(name=f"M{i}", index=i, node_type='master',
                              ip_type='generated', x=100 + i * 120, y=50)
            self.project.masters.append(master)
            
        # Create slaves (horizontal arrangement at bottom)
        for i in range(num_slaves):
            slave = NodeConfig(name=f"S{i}", index=i, node_type='slave',
                             ip_type='generated', x=100 + i * 120, y=400,
                             base_addr=0x80000000 + i * 0x10000000,
                             size=0x10000000)
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
                              ip_type='generated', x=100 + i * 120, y=50,
                              domain=domain)
            self.project.masters.append(master)
            
        # Create slaves in different domains (horizontal at bottom)
        for i in range(4):
            domain = ["ddr_domain", "ddr_domain", "periph_domain", "periph_domain"][i]
            slave = NodeConfig(name=f"S{i}", index=i, node_type='slave',
                             ip_type='generated', x=100 + i * 120, y=400,
                             domain=domain,
                             base_addr=0x80000000 + i * 0x10000000,
                             size=0x10000000)
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
                x = 100 + existing_masters * 120
                y = 50
            elif 'slave' in node_type:
                # Slaves arranged horizontally at bottom
                existing_slaves = len([n for n in self.nodes if 'slave' in n])
                x = 100 + existing_slaves * 120
                y = 400
            else:  # bridge
                existing_bridges = len([n for n in self.nodes if 'bridge' in n])
                x = 400 + existing_bridges * 150
                y = 225
            
            # Create node config
            if base_type == 'master':
                idx = len(self.project.masters)
                node_config = NodeConfig(name=name, index=idx, node_type=base_type, 
                                       ip_type=ip_type, x=x, y=y)
                self.project.masters.append(node_config)
            elif base_type == 'slave':
                idx = len(self.project.slaves)
                base_addr = 0x80000000 + (idx * 0x10000000)
                node_config = NodeConfig(name=name, index=idx, node_type=base_type, 
                                       ip_type=ip_type, x=x, y=y, 
                                       base_addr=base_addr, size=0x10000000)
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
            
            # Update CLI
            self.generate_cli_command()
            
            self.status_bar.config(text=f"Added {name}")
            
        except Exception as e:
            logger.error(f"Error adding node: {e}")
            import traceback
            traceback.print_exc()
            
    def draw_node(self, config, color):
        """Draw a node on the canvas"""
        x, y = config.x, config.y
        width, height = 100, 50
        
        # Create rectangle
        rect = self.canvas.create_rectangle(x, y, x + width, y + height, 
                                           fill=color, outline='black', width=2)
        
        # Create text labels
        text = self.canvas.create_text(x + width/2, y + 15, text=config.name, 
                                      font=('Arial', 10, 'bold'), fill='white')
        
        # Create type badge
        type_text = "EXT" if config.ip_type == 'external' else config.node_type.upper()[:3]
        badge = self.canvas.create_text(x + width/2, y + 35, text=f"[{type_text}]", 
                                       font=('Arial', 8), fill='white')
        
        # Store node reference
        node_id = f"{config.node_type}_{config.index}"
        self.nodes[node_id] = {
            'config': config,
            'rect': rect,
            'text': text,
            'badges': [badge],
            'color': color
        }
        
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
            
            # Update CLI
            self.generate_cli_command()
            
            self.status_bar.config(text=f"Deleted {config.name}")
            
    def edit_node_properties(self, node_id):
        """Edit node properties dialog"""
        if node_id not in self.nodes:
            return
            
        node_data = self.nodes[node_id]
        config = node_data['config']
        
        # Create dialog
        dialog = tk.Toplevel(self)
        dialog.title(f"Edit {config.name} Properties")
        dialog.geometry("400x400")
        
        # Create property fields
        row = 0
        ttk.Label(dialog, text="Name:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
        name_var = tk.StringVar(value=config.name)
        ttk.Entry(dialog, textvariable=name_var).grid(row=row, column=1, padx=5, pady=5)
        
        row += 1
        ttk.Label(dialog, text="Domain:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
        domain_var = tk.StringVar(value=config.domain)
        ttk.Entry(dialog, textvariable=domain_var).grid(row=row, column=1, padx=5, pady=5)
        
        row += 1
        ttk.Label(dialog, text="Security:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
        security_var = tk.StringVar(value=config.security)
        ttk.Combobox(dialog, textvariable=security_var, 
                    values=['secure', 'non_secure', 'shared']).grid(row=row, column=1, padx=5, pady=5)
        
        # Cache Configuration Section
        row += 1
        ttk.Separator(dialog, orient='horizontal').grid(row=row, column=0, columnspan=2, sticky='ew', pady=10)
        
        row += 1
        ttk.Label(dialog, text="Cache Settings", font=('TkDefaultFont', 10, 'bold')).grid(row=row, column=0, columnspan=2, pady=5)
        
        row += 1
        cache_enable_var = tk.BooleanVar(value=config.cache_enable)
        ttk.Checkbutton(dialog, text="Enable Cache Support", variable=cache_enable_var).grid(row=row, column=0, columnspan=2, padx=5, pady=5)
        
        row += 1
        ttk.Label(dialog, text="AWCACHE Default:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
        awcache_frame = ttk.Frame(dialog)
        awcache_frame.grid(row=row, column=1, padx=5, pady=5, sticky='w')
        
        # Create AWCACHE bit checkboxes
        awcache_bits = []
        awcache_labels = ['Bufferable', 'Cacheable', 'Read Alloc', 'Write Alloc']
        for i, label in enumerate(awcache_labels):
            var = tk.BooleanVar(value=bool(config.awcache_default & (1 << i)))
            cb = ttk.Checkbutton(awcache_frame, text=label, variable=var)
            cb.pack(side='left', padx=2)
            awcache_bits.append(var)
        
        row += 1
        ttk.Label(dialog, text="ARCACHE Default:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
        arcache_frame = ttk.Frame(dialog)
        arcache_frame.grid(row=row, column=1, padx=5, pady=5, sticky='w')
        
        # Create ARCACHE bit checkboxes
        arcache_bits = []
        for i, label in enumerate(awcache_labels):
            var = tk.BooleanVar(value=bool(config.arcache_default & (1 << i)))
            cb = ttk.Checkbutton(arcache_frame, text=label, variable=var)
            cb.pack(side='left', padx=2)
            arcache_bits.append(var)
        
        row += 1
        ttk.Label(dialog, text="Cache Policy:").grid(row=row, column=0, sticky='w', padx=5, pady=5)
        cache_policy_var = tk.StringVar(value=config.cache_policy)
        ttk.Combobox(dialog, textvariable=cache_policy_var,
                    values=['write-through', 'write-back', 'no-allocate', 'write-allocate']).grid(row=row, column=1, padx=5, pady=5)
        
        row += 1
        cache_coherent_var = tk.BooleanVar(value=config.cache_coherent)
        ttk.Checkbutton(dialog, text="Cache Coherent (ACE-Lite)", variable=cache_coherent_var).grid(row=row, column=0, columnspan=2, padx=5, pady=5)
        
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
            config.security = security_var.get()
            
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
                except ValueError:
                    messagebox.showerror("Error", "Invalid address format")
                    return
                    
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
            master.x = x_offset + i * 120
            master.y = 50
            
        # Arrange slaves horizontally at bottom
        x_offset = 100
        for i, slave in enumerate(self.project.slaves):
            slave.x = x_offset + i * 120
            slave.y = 400
            
        # Arrange bridges in middle
        x_offset = 400
        for i, bridge in enumerate(self.project.bridges):
            bridge.x = x_offset + i * 150
            bridge.y = 225
            
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
            max_x = max(max_x, config.x + 100)
            max_y = max(max_y, config.y + 50)
            
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
            # Calculate interconnect position (horizontal bar in middle)
            # Find the range of master and slave x positions
            master_min_x = min([m.x for m in self.project.masters])
            master_max_x = max([m.x + 100 for m in self.project.masters])
            slave_min_x = min([s.x for s in self.project.slaves])
            slave_max_x = max([s.x + 100 for s in self.project.slaves])
            
            # Interconnect spans from leftmost to rightmost node
            ic_x = min(master_min_x, slave_min_x) - 20
            ic_width = max(master_max_x, slave_max_x) - ic_x + 20
            ic_y = 200  # Middle position between masters (y=50) and slaves (y=400)
            ic_height = 100  # Height of the interconnect block
            
            # Draw interconnect block (horizontal rectangle)
            ic_rect = self.canvas.create_rectangle(ic_x, ic_y, ic_x + ic_width, ic_y + ic_height,
                                                  fill='#9E9E9E', outline='black', width=2)
            ic_text = self.canvas.create_text(ic_x + ic_width/2, ic_y + ic_height/2,
                                             text="AXI Interconnect", font=('Arial', 12, 'bold'),
                                             fill='white')
            self.connections.extend([ic_rect, ic_text])
            
            # Draw vertical connections from masters to interconnect
            for master in self.project.masters:
                # Vertical line from master down to interconnect
                line = self.canvas.create_line(master.x + 50, master.y + 50,  # From bottom of master
                                              master.x + 50, ic_y,           # To top of interconnect
                                              fill='blue', width=2, arrow=tk.LAST)
                self.connections.append(line)
                
            # Draw vertical connections from interconnect to slaves
            for slave in self.project.slaves:
                # Vertical line from interconnect down to slave
                line = self.canvas.create_line(slave.x + 50, ic_y + ic_height,  # From bottom of interconnect
                                              slave.x + 50, slave.y,            # To top of slave
                                              fill='blue', width=2, arrow=tk.LAST)
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
            cmd += f"# Bus: {self.project.bus.data_width}b data, {self.project.bus.addr_width}b addr\n"
            if self.project.domains:
                cmd += f"# Domains: {', '.join([d.name for d in self.project.domains])}\n"
                
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
                self.generate_cli_command()
                
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
        
        try:
            # Use enhanced RTL generator for RTL generation
            if mode in ['rtl', 'both']:
                from enhanced_rtl_generator import EnhancedRTLGenerator
                rtl_gen = EnhancedRTLGenerator(self.project, settings)
                rtl_dir = rtl_gen.generate()
                logger.info(f"Enhanced RTL generated: {rtl_dir}")
            
            # Use existing VIP generator for VIP generation
            if mode in ['vip', 'both']:
                from generation_dialog import GenerationDialog
                
                # Create generation dialog helper for VIP
                class MockDialog:
                    pass
                dialog = MockDialog()
                
                class MockVar:
                    def __init__(self, value):
                        self.value = value
                    def get(self):
                        return self.value
                
                # Set up dialog variables
                dialog.project_name_var = MockVar(settings['project_name'])
                dialog.addr_width_var = MockVar(self.project.bus.addr_width)
                dialog.data_width_var = MockVar(self.project.bus.data_width)
                dialog.id_width_var = MockVar(self.project.bus.id_width)
                dialog.gen_filelist_var = MockVar(settings['common']['gen_filelist'])
                dialog.gen_scripts_var = MockVar(settings['common']['gen_scripts'])
                dialog.simulator_var = MockVar(settings['simulator'])
                
                vip_dir = os.path.join(output_dir, 'vip')
                dialog.generate_vip(vip_dir)
                
                # Save project configuration
                dialog.save_project_config(output_dir)
            
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
                    'enable_qos': True,
                    'enable_region': True,
                    'enable_exclusive': True,
                    'enable_user': False,
                    'gen_filelist': True,
                    'gen_makefile': True,
                    'gen_scripts': True,
                    'gen_documentation': False
                }
            }
            self.process_generation(settings)

def main():
    """Main entry point"""
    app = AXI4GeneratorGUI()
    app.mainloop()

if __name__ == "__main__":
    main()