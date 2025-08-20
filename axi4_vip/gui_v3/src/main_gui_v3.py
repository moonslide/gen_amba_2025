#!/usr/bin/env python3
"""
AMBA AXI4 RTL & VIP Generator - Main GUI (v3)
Implements consolidated specification with Templates tab
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

class TemplateGallery(ttk.Frame):
    """Template gallery for the Templates tab"""
    
    def __init__(self, parent, on_load_template):
        super().__init__(parent)
        self.on_load_template = on_load_template
        self.templates = self.load_templates()
        self.create_widgets()
        
    def load_templates(self):
        """Load available templates"""
        return [
            {
                'name': 'AXI 4x4 Basic',
                'description': '4 Masters x 4 Slaves basic interconnect',
                'config': {
                    'masters': 4,
                    'slaves': 4,
                    'data_width': 64,
                    'addr_width': 32
                }
            },
            {
                'name': 'AXI 8x8 Standard', 
                'description': '8 Masters x 8 Slaves with QoS',
                'config': {
                    'masters': 8,
                    'slaves': 8,
                    'data_width': 128,
                    'addr_width': 32,
                    'qos_enabled': True
                }
            },
            {
                'name': 'AXI 16x16 Large',
                'description': '16 Masters x 16 Slaves enterprise system',
                'config': {
                    'masters': 16,
                    'slaves': 16,
                    'data_width': 256,
                    'addr_width': 48
                }
            },
            {
                'name': 'AHB-Lite Bridge',
                'description': 'AXI to AHB-Lite bridge configuration',
                'config': {
                    'masters': 2,
                    'slaves': 2,
                    'bridges': ['ahb_lite'],
                    'data_width': 32,
                    'addr_width': 32
                }
            },
            {
                'name': 'Multi-Domain SoC',
                'description': 'Multiple clock domains with CDC',
                'config': {
                    'masters': 6,
                    'slaves': 8,
                    'domains': ['cpu', 'ddr', 'periph'],
                    'data_width': 128,
                    'addr_width': 40
                }
            }
        ]
        
    def create_widgets(self):
        """Create template gallery widgets"""
        # Title
        title = ttk.Label(self, text="Project Templates", font=('Arial', 14, 'bold'))
        title.pack(pady=10)
        
        # Description
        desc = ttk.Label(self, text="Select a template to start your design")
        desc.pack(pady=5)
        
        # Template list frame with scrollbar
        list_frame = ttk.Frame(self)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        scrollbar = ttk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Template listbox
        self.template_list = tk.Listbox(list_frame, yscrollcommand=scrollbar.set, height=10)
        self.template_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=self.template_list.yview)
        
        # Populate templates
        for template in self.templates:
            self.template_list.insert(tk.END, template['name'])
            
        self.template_list.bind('<<ListboxSelect>>', self.on_template_select)
        
        # Details frame
        details_frame = ttk.LabelFrame(self, text="Template Details", padding=10)
        details_frame.pack(fill=tk.X, padx=20, pady=10)
        
        self.details_text = tk.Text(details_frame, height=6, wrap=tk.WORD)
        self.details_text.pack(fill=tk.BOTH, expand=True)
        
        # Load button
        self.load_btn = ttk.Button(self, text="Load Template", command=self.load_selected_template)
        self.load_btn.pack(pady=10)
        self.load_btn.config(state='disabled')
        
    def on_template_select(self, event):
        """Handle template selection"""
        selection = self.template_list.curselection()
        if selection:
            idx = selection[0]
            template = self.templates[idx]
            
            # Update details
            self.details_text.delete(1.0, tk.END)
            details = f"{template['description']}\n\n"
            config = template['config']
            details += f"Masters: {config.get('masters', 'N/A')}\n"
            details += f"Slaves: {config.get('slaves', 'N/A')}\n"
            details += f"Data Width: {config.get('data_width', 'N/A')} bits\n"
            details += f"Address Width: {config.get('addr_width', 'N/A')} bits"
            self.details_text.insert(1.0, details)
            
            self.load_btn.config(state='normal')
            
    def load_selected_template(self):
        """Load the selected template"""
        selection = self.template_list.curselection()
        if selection:
            idx = selection[0]
            template = self.templates[idx]
            
            # Confirm with user
            result = messagebox.askyesno(
                "Load Template",
                "Loading this template will clear the current design on the canvas.\n"
                "Are you sure you want to continue?"
            )
            
            if result:
                self.on_load_template(template)

class CanvasTab(ttk.Frame):
    """Main canvas for topology design"""
    
    def __init__(self, parent, project):
        super().__init__(parent)
        self.project = project
        self.nodes = {}  # id -> node widget
        self.connections = []  # list of connection lines
        self.selected_node = None
        self.drag_data = {"x": 0, "y": 0, "item": None}
        
        self.create_widgets()
        
    def create_widgets(self):
        """Create canvas widgets"""
        # Toolbar
        toolbar = ttk.Frame(self)
        toolbar.pack(side=tk.TOP, fill=tk.X, padx=5, pady=5)
        
        ttk.Button(toolbar, text="+ Master", command=lambda: self.add_node('master')).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="+ Slave", command=lambda: self.add_node('slave')).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="+ External Master", command=lambda: self.add_node('ext_master')).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="+ External Slave", command=lambda: self.add_node('ext_slave')).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="+ Bridge", command=lambda: self.add_node('bridge')).pack(side=tk.LEFT, padx=2)
        ttk.Separator(toolbar, orient='vertical').pack(side=tk.LEFT, fill=tk.Y, padx=5)
        ttk.Button(toolbar, text="Delete", command=self.delete_selected).pack(side=tk.LEFT, padx=2)
        ttk.Separator(toolbar, orient='vertical').pack(side=tk.LEFT, fill=tk.Y, padx=5)
        ttk.Button(toolbar, text="Auto-Arrange", command=self.auto_arrange).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Zoom Fit", command=self.zoom_fit).pack(side=tk.LEFT, padx=2)
        
        # Canvas
        canvas_frame = ttk.Frame(self)
        canvas_frame.pack(fill=tk.BOTH, expand=True)
        
        self.canvas = tk.Canvas(canvas_frame, bg='white', width=1000, height=600)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # Scrollbars
        v_scrollbar = ttk.Scrollbar(canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview)
        v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas.config(yscrollcommand=v_scrollbar.set)
        
        h_scrollbar = ttk.Scrollbar(self, orient=tk.HORIZONTAL, command=self.canvas.xview)
        h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
        self.canvas.config(xscrollcommand=h_scrollbar.set)
        
        # Canvas bindings
        self.canvas.bind("<Button-1>", self.on_canvas_click)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_drag_release)
        self.canvas.bind("<Button-3>", self.on_right_click)
        
        # Set canvas scroll region
        self.canvas.config(scrollregion=(0, 0, 2000, 2000))
        
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
                
            # Calculate position
            x = 100 if 'master' in node_type else 700 if 'slave' in node_type else 400
            y = 100 + len(self.nodes) * 80
            
            # Create node config
            if base_type == 'master':
                idx = len(self.project.masters)
                node_config = NodeConfig(name=name, index=idx, node_type=base_type, ip_type=ip_type, x=x, y=y)
                self.project.masters.append(node_config)
            elif base_type == 'slave':
                idx = len(self.project.slaves)
                base_addr = 0x80000000 + (idx * 0x10000000)
                node_config = NodeConfig(name=name, index=idx, node_type=base_type, ip_type=ip_type, 
                                       x=x, y=y, base_addr=base_addr, size=0x10000000)
                self.project.slaves.append(node_config)
            elif base_type == 'bridge':
                idx = len(self.project.bridges)
                node_config = NodeConfig(name=name, index=idx, node_type=base_type, ip_type=ip_type, x=x, y=y)
                self.project.bridges.append(node_config)
                
            # Draw node on canvas
            self.draw_node(node_config, color)
            
        except Exception as e:
            logger.error(f"Error adding node: {e}")
            import traceback
            traceback.print_exc()
        
    def draw_node(self, config, color):
        """Draw a node on the canvas"""
        x, y = config.x, config.y
        width, height = 120, 60
        
        # Create rectangle
        rect = self.canvas.create_rectangle(x, y, x + width, y + height, 
                                           fill=color, outline='black', width=2)
        
        # Create text labels
        text = self.canvas.create_text(x + width/2, y + 20, text=config.name, 
                                      font=('Arial', 10, 'bold'), fill='white')
        
        # Create badges
        badges = []
        if config.ip_type == 'external':
            badge = self.canvas.create_text(x + width/2, y + 40, text="[EXT]", 
                                          font=('Arial', 8), fill='white')
            badges.append(badge)
            
        # Store node reference
        node_id = f"{config.node_type}_{config.index}"
        self.nodes[node_id] = {
            'config': config,
            'rect': rect,
            'text': text,
            'badges': badges,
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
            menu.add_command(label="Edit Properties", command=lambda: self.edit_node_properties(node_clicked))
            menu.add_command(label="Delete", command=lambda: self.delete_node(node_clicked))
        else:
            menu.add_command(label="Auto-Arrange", command=self.auto_arrange)
            menu.add_command(label="Zoom to Fit", command=self.zoom_fit)
            
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
            
    def edit_node_properties(self, node_id):
        """Edit node properties dialog"""
        if node_id not in self.nodes:
            return
            
        node_data = self.nodes[node_id]
        config = node_data['config']
        
        # Create dialog
        dialog = tk.Toplevel(self)
        dialog.title(f"Edit {config.name} Properties")
        dialog.geometry("400x500")
        
        # Create property fields
        ttk.Label(dialog, text="Name:").grid(row=0, column=0, sticky='w', padx=5, pady=5)
        name_var = tk.StringVar(value=config.name)
        ttk.Entry(dialog, textvariable=name_var).grid(row=0, column=1, padx=5, pady=5)
        
        ttk.Label(dialog, text="Domain:").grid(row=1, column=0, sticky='w', padx=5, pady=5)
        domain_var = tk.StringVar(value=config.domain)
        ttk.Entry(dialog, textvariable=domain_var).grid(row=1, column=1, padx=5, pady=5)
        
        ttk.Label(dialog, text="Security:").grid(row=2, column=0, sticky='w', padx=5, pady=5)
        security_var = tk.StringVar(value=config.security)
        ttk.Combobox(dialog, textvariable=security_var, 
                    values=['secure', 'non_secure', 'shared']).grid(row=2, column=1, padx=5, pady=5)
        
        ttk.Label(dialog, text="AW QoS:").grid(row=3, column=0, sticky='w', padx=5, pady=5)
        qos_aw_var = tk.IntVar(value=config.qos_aw)
        ttk.Spinbox(dialog, from_=0, to=15, textvariable=qos_aw_var).grid(row=3, column=1, padx=5, pady=5)
        
        ttk.Label(dialog, text="AR QoS:").grid(row=4, column=0, sticky='w', padx=5, pady=5)
        qos_ar_var = tk.IntVar(value=config.qos_ar)
        ttk.Spinbox(dialog, from_=0, to=15, textvariable=qos_ar_var).grid(row=4, column=1, padx=5, pady=5)
        
        # External IP fields
        if config.ip_type == 'external':
            ttk.Label(dialog, text="RTL Path:").grid(row=5, column=0, sticky='w', padx=5, pady=5)
            rtl_var = tk.StringVar(value=config.rtl_path or '')
            ttk.Entry(dialog, textvariable=rtl_var).grid(row=5, column=1, padx=5, pady=5)
            
            ttk.Label(dialog, text="Top Module:").grid(row=6, column=0, sticky='w', padx=5, pady=5)
            module_var = tk.StringVar(value=config.top_module or '')
            ttk.Entry(dialog, textvariable=module_var).grid(row=6, column=1, padx=5, pady=5)
            
        # Slave-specific fields
        if config.node_type == 'slave':
            ttk.Label(dialog, text="Base Address:").grid(row=7, column=0, sticky='w', padx=5, pady=5)
            base_var = tk.StringVar(value=hex(config.base_addr) if config.base_addr else '0x0')
            ttk.Entry(dialog, textvariable=base_var).grid(row=7, column=1, padx=5, pady=5)
            
            ttk.Label(dialog, text="Size:").grid(row=8, column=0, sticky='w', padx=5, pady=5)
            size_var = tk.StringVar(value=hex(config.size) if config.size else '0x1000')
            ttk.Entry(dialog, textvariable=size_var).grid(row=8, column=1, padx=5, pady=5)
            
        # Save button
        def save_properties():
            config.name = name_var.get()
            config.domain = domain_var.get()
            config.security = security_var.get()
            config.qos_aw = qos_aw_var.get()
            config.qos_ar = qos_ar_var.get()
            
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
            dialog.destroy()
            
        ttk.Button(dialog, text="Save", command=save_properties).grid(row=10, column=0, columnspan=2, pady=10)
        
    def auto_arrange(self):
        """Auto-arrange nodes with smart layout"""
        # Arrange masters on left
        y_offset = 100
        for i, master in enumerate(self.project.masters):
            master.x = 100
            master.y = y_offset + i * 100
            
        # Arrange slaves on right
        y_offset = 100
        for i, slave in enumerate(self.project.slaves):
            slave.x = 700
            slave.y = y_offset + i * 100
            
        # Arrange bridges in middle
        y_offset = 100
        for i, bridge in enumerate(self.project.bridges):
            bridge.x = 400
            bridge.y = y_offset + i * 150
            
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
            max_x = max(max_x, config.x + 120)
            max_y = max(max_y, config.y + 60)
            
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
        
        # Draw interconnect block
        if self.project.masters and self.project.slaves:
            # Calculate interconnect position
            masters_right = max([m.x + 120 for m in self.project.masters])
            slaves_left = min([s.x for s in self.project.slaves])
            
            ic_x = masters_right + 50
            ic_width = slaves_left - masters_right - 100
            ic_y = 50
            ic_height = max(len(self.project.masters), len(self.project.slaves)) * 100 + 100
            
            # Draw interconnect block
            ic_rect = self.canvas.create_rectangle(ic_x, ic_y, ic_x + ic_width, ic_y + ic_height,
                                                  fill='#9E9E9E', outline='black', width=2)
            ic_text = self.canvas.create_text(ic_x + ic_width/2, ic_y + ic_height/2,
                                             text="AXI\nInterconnect", font=('Arial', 12, 'bold'),
                                             fill='white')
            self.connections.extend([ic_rect, ic_text])
            
            # Draw connections from masters to interconnect
            for master in self.project.masters:
                line = self.canvas.create_line(master.x + 120, master.y + 30,
                                              ic_x, master.y + 30,
                                              fill='blue', width=2, arrow=tk.LAST)
                self.connections.append(line)
                
            # Draw connections from interconnect to slaves
            for slave in self.project.slaves:
                line = self.canvas.create_line(ic_x + ic_width, slave.y + 30,
                                              slave.x, slave.y + 30,
                                              fill='blue', width=2, arrow=tk.LAST)
                self.connections.append(line)
                
    def load_template(self, template):
        """Load a template configuration"""
        # Clear current design
        self.clear_canvas()
        self.project.masters.clear()
        self.project.slaves.clear()
        self.project.bridges.clear()
        
        # Load template configuration
        config = template['config']
        
        # Create masters
        for i in range(config.get('masters', 4)):
            name = f"M{i}"
            master = NodeConfig(name=name, index=i, node_type='master', 
                              ip_type='generated', x=100, y=100 + i * 100)
            self.project.masters.append(master)
            
        # Create slaves
        for i in range(config.get('slaves', 4)):
            name = f"S{i}"
            base_addr = 0x80000000 + (i * 0x10000000)
            slave = NodeConfig(name=name, index=i, node_type='slave',
                             ip_type='generated', x=700, y=100 + i * 100,
                             base_addr=base_addr, size=0x10000000)
            self.project.slaves.append(slave)
            
        # Update bus config
        self.project.bus.data_width = config.get('data_width', 64)
        self.project.bus.addr_width = config.get('addr_width', 32)
        
        # Redraw
        self.redraw_all_nodes()
        self.zoom_fit()
        
        logger.info(f"Loaded template: {template['name']}")

class GenerationSettingsDialog(tk.Toplevel):
    """Advanced generation settings dialog"""
    
    def __init__(self, parent, project):
        super().__init__(parent)
        self.project = project
        self.title("Generation Settings")
        self.geometry("600x500")
        
        # Create notebook for tabs
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create tabs
        self.create_general_tab()
        self.create_rtl_tab()
        self.create_vip_tab()
        
        # Buttons
        button_frame = ttk.Frame(self)
        button_frame.pack(side=tk.BOTTOM, pady=10)
        
        ttk.Button(button_frame, text="Generate", command=self.generate).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Cancel", command=self.destroy).pack(side=tk.LEFT, padx=5)
        
    def create_general_tab(self):
        """Create general settings tab"""
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="General")
        
        # Output directory
        ttk.Label(tab, text="Output Directory:").grid(row=0, column=0, sticky='w', padx=5, pady=5)
        self.output_dir_var = tk.StringVar(value="./generated")
        ttk.Entry(tab, textvariable=self.output_dir_var, width=40).grid(row=0, column=1, padx=5, pady=5)
        ttk.Button(tab, text="Browse...", command=self.browse_output_dir).grid(row=0, column=2, padx=5, pady=5)
        
        # Project name
        ttk.Label(tab, text="Project Name:").grid(row=1, column=0, sticky='w', padx=5, pady=5)
        self.project_name_var = tk.StringVar(value=self.project.name)
        ttk.Entry(tab, textvariable=self.project_name_var, width=40).grid(row=1, column=1, padx=5, pady=5)
        
        # Bus parameters
        bus_frame = ttk.LabelFrame(tab, text="Bus Parameters", padding=10)
        bus_frame.grid(row=2, column=0, columnspan=3, sticky='ew', padx=5, pady=10)
        
        ttk.Label(bus_frame, text="Address Width:").grid(row=0, column=0, sticky='w', padx=5, pady=5)
        self.addr_width_var = tk.IntVar(value=self.project.bus.addr_width)
        ttk.Spinbox(bus_frame, from_=16, to=64, textvariable=self.addr_width_var).grid(row=0, column=1, padx=5, pady=5)
        
        ttk.Label(bus_frame, text="Data Width:").grid(row=1, column=0, sticky='w', padx=5, pady=5)
        self.data_width_var = tk.IntVar(value=self.project.bus.data_width)
        ttk.Combobox(bus_frame, textvariable=self.data_width_var,
                    values=[32, 64, 128, 256, 512]).grid(row=1, column=1, padx=5, pady=5)
        
        ttk.Label(bus_frame, text="ID Width:").grid(row=2, column=0, sticky='w', padx=5, pady=5)
        self.id_width_var = tk.IntVar(value=self.project.bus.id_width)
        ttk.Spinbox(bus_frame, from_=1, to=16, textvariable=self.id_width_var).grid(row=2, column=1, padx=5, pady=5)
        
    def create_rtl_tab(self):
        """Create RTL settings tab"""
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="RTL Settings")
        
        # Output language
        ttk.Label(tab, text="Output Language:").grid(row=0, column=0, sticky='w', padx=5, pady=5)
        self.rtl_lang_var = tk.StringVar(value="Verilog")
        ttk.Combobox(tab, textvariable=self.rtl_lang_var,
                    values=["Verilog", "SystemVerilog"]).grid(row=0, column=1, padx=5, pady=5)
        
        # File structure
        ttk.Label(tab, text="File Structure:").grid(row=1, column=0, sticky='w', padx=5, pady=5)
        self.file_struct_var = tk.StringVar(value="File per Module")
        ttk.Combobox(tab, textvariable=self.file_struct_var,
                    values=["Single File", "File per Module"]).grid(row=1, column=1, padx=5, pady=5)
        
        # Synthesis target
        ttk.Label(tab, text="Target Technology:").grid(row=2, column=0, sticky='w', padx=5, pady=5)
        self.target_tech_var = tk.StringVar(value="FPGA")
        ttk.Combobox(tab, textvariable=self.target_tech_var,
                    values=["ASIC", "FPGA"]).grid(row=2, column=1, padx=5, pady=5)
        
        # Generate options
        options_frame = ttk.LabelFrame(tab, text="Generate Options", padding=10)
        options_frame.grid(row=3, column=0, columnspan=2, sticky='ew', padx=5, pady=10)
        
        self.gen_filelist_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(options_frame, text="Generate Filelist", 
                       variable=self.gen_filelist_var).pack(anchor='w')
        
        self.gen_header_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(options_frame, text="Add Generated Header", 
                       variable=self.gen_header_var).pack(anchor='w')
        
        self.gen_cdc_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(options_frame, text="Generate CDC Logic", 
                       variable=self.gen_cdc_var).pack(anchor='w')
        
    def create_vip_tab(self):
        """Create VIP settings tab"""
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="VIP Settings")
        
        # Methodology
        ttk.Label(tab, text="Verification Methodology:").grid(row=0, column=0, sticky='w', padx=5, pady=5)
        self.vip_method_var = tk.StringVar(value="UVM")
        ttk.Combobox(tab, textvariable=self.vip_method_var,
                    values=["UVM", "Simple Testbench"]).grid(row=0, column=1, padx=5, pady=5)
        
        # Simulator
        ttk.Label(tab, text="Target Simulator:").grid(row=1, column=0, sticky='w', padx=5, pady=5)
        self.simulator_var = tk.StringVar(value="VCS")
        ttk.Combobox(tab, textvariable=self.simulator_var,
                    values=["VCS", "Xcelium", "Questa", "Vivado"]).grid(row=1, column=1, padx=5, pady=5)
        
        # Integration level
        ttk.Label(tab, text="Integration Level:").grid(row=2, column=0, sticky='w', padx=5, pady=5)
        self.integration_var = tk.StringVar(value="Generated RTL")
        ttk.Combobox(tab, textvariable=self.integration_var,
                    values=["VIP Only", "Generated RTL", "External IPs Only", 
                           "Generated RTL & External IPs"]).grid(row=2, column=1, padx=5, pady=5)
        
        # Component generation
        comp_frame = ttk.LabelFrame(tab, text="Component Generation", padding=10)
        comp_frame.grid(row=3, column=0, columnspan=2, sticky='ew', padx=5, pady=10)
        
        self.gen_agents_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(comp_frame, text="Generate Agents", 
                       variable=self.gen_agents_var).pack(anchor='w')
        
        self.gen_env_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(comp_frame, text="Generate Environment", 
                       variable=self.gen_env_var).pack(anchor='w')
        
        self.gen_coverage_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(comp_frame, text="Generate Coverage", 
                       variable=self.gen_coverage_var).pack(anchor='w')
        
        self.gen_scripts_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(comp_frame, text="Generate Makefile/Scripts", 
                       variable=self.gen_scripts_var).pack(anchor='w')
        
        # Test sequences
        seq_frame = ttk.LabelFrame(tab, text="Test Sequences", padding=10)
        seq_frame.grid(row=4, column=0, columnspan=2, sticky='ew', padx=5, pady=10)
        
        self.gen_basic_test_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(seq_frame, text="Basic Read/Write", 
                       variable=self.gen_basic_test_var).pack(anchor='w')
        
        self.gen_random_test_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(seq_frame, text="Random Test", 
                       variable=self.gen_random_test_var).pack(anchor='w')
        
        self.gen_stress_test_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(seq_frame, text="Stress Test", 
                       variable=self.gen_stress_test_var).pack(anchor='w')
        
    def browse_output_dir(self):
        """Browse for output directory"""
        dir_path = filedialog.askdirectory(title="Select Output Directory")
        if dir_path:
            self.output_dir_var.set(dir_path)
            
    def generate(self):
        """Generate RTL and/or VIP"""
        # Update project configuration
        self.project.name = self.project_name_var.get()
        self.project.bus.addr_width = self.addr_width_var.get()
        self.project.bus.data_width = self.data_width_var.get()
        self.project.bus.id_width = self.id_width_var.get()
        
        # Create output directory
        output_dir = self.output_dir_var.get()
        os.makedirs(output_dir, exist_ok=True)
        
        # Generate RTL
        if self.gen_filelist_var.get() or True:  # Always generate some RTL
            self.generate_rtl(output_dir)
            
        # Generate VIP
        if self.vip_method_var.get() == "UVM":
            self.generate_vip(output_dir)
            
        # Save project configuration
        self.save_project_config(output_dir)
        
        messagebox.showinfo("Success", f"Generation complete!\nOutput: {output_dir}")
        self.destroy()
        
    def generate_rtl(self, output_dir):
        """Generate RTL files"""
        rtl_dir = os.path.join(output_dir, "rtl")
        os.makedirs(rtl_dir, exist_ok=True)
        
        # Generate interconnect module
        interconnect_file = os.path.join(rtl_dir, f"{self.project.name}_interconnect.v")
        with open(interconnect_file, 'w') as f:
            f.write(self.generate_interconnect_rtl())
            
        # Generate filelist
        if self.gen_filelist_var.get():
            filelist_file = os.path.join(rtl_dir, "filelist.f")
            with open(filelist_file, 'w') as f:
                f.write(f"{self.project.name}_interconnect.v\n")
                
        logger.info(f"Generated RTL in {rtl_dir}")
        
    def generate_interconnect_rtl(self):
        """Generate interconnect RTL code"""
        num_masters = len(self.project.masters)
        num_slaves = len(self.project.slaves)
        
        rtl = f"""// {self.project.name} AXI4 Interconnect
// Generated by AMBA AXI4 RTL & VIP Generator v3
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

module {self.project.name}_interconnect #(
    parameter ADDR_WIDTH = {self.project.bus.addr_width},
    parameter DATA_WIDTH = {self.project.bus.data_width},
    parameter ID_WIDTH = {self.project.bus.id_width},
    parameter USER_WIDTH = {self.project.bus.user_width}
)(
    input wire aclk,
    input wire aresetn"""
        
        # Add master interfaces
        for i, master in enumerate(self.project.masters):
            rtl += f"""
    
    // Master {i}: {master.name}
    // AXI4 Master Interface
    input  wire [ID_WIDTH-1:0]     m{i}_awid,
    input  wire [ADDR_WIDTH-1:0]   m{i}_awaddr,
    input  wire [7:0]               m{i}_awlen,
    input  wire [2:0]               m{i}_awsize,
    input  wire [1:0]               m{i}_awburst,
    input  wire                     m{i}_awvalid,
    output wire                     m{i}_awready,
    
    input  wire [DATA_WIDTH-1:0]   m{i}_wdata,
    input  wire [DATA_WIDTH/8-1:0] m{i}_wstrb,
    input  wire                     m{i}_wlast,
    input  wire                     m{i}_wvalid,
    output wire                     m{i}_wready,
    
    output wire [ID_WIDTH-1:0]     m{i}_bid,
    output wire [1:0]               m{i}_bresp,
    output wire                     m{i}_bvalid,
    input  wire                     m{i}_bready,
    
    input  wire [ID_WIDTH-1:0]     m{i}_arid,
    input  wire [ADDR_WIDTH-1:0]   m{i}_araddr,
    input  wire [7:0]               m{i}_arlen,
    input  wire [2:0]               m{i}_arsize,
    input  wire [1:0]               m{i}_arburst,
    input  wire                     m{i}_arvalid,
    output wire                     m{i}_arready,
    
    output wire [ID_WIDTH-1:0]     m{i}_rid,
    output wire [DATA_WIDTH-1:0]   m{i}_rdata,
    output wire [1:0]               m{i}_rresp,
    output wire                     m{i}_rlast,
    output wire                     m{i}_rvalid,
    input  wire                     m{i}_rready,"""
            
        # Add slave interfaces
        for i, slave in enumerate(self.project.slaves):
            rtl += f"""
    
    // Slave {i}: {slave.name}
    // Base: 0x{slave.base_addr:08X}, Size: 0x{slave.size:08X}
    output wire [ID_WIDTH-1:0]     s{i}_awid,
    output wire [ADDR_WIDTH-1:0]   s{i}_awaddr,
    output wire [7:0]               s{i}_awlen,
    output wire [2:0]               s{i}_awsize,
    output wire [1:0]               s{i}_awburst,
    output wire                     s{i}_awvalid,
    input  wire                     s{i}_awready,
    
    output wire [DATA_WIDTH-1:0]   s{i}_wdata,
    output wire [DATA_WIDTH/8-1:0] s{i}_wstrb,
    output wire                     s{i}_wlast,
    output wire                     s{i}_wvalid,
    input  wire                     s{i}_wready,
    
    input  wire [ID_WIDTH-1:0]     s{i}_bid,
    input  wire [1:0]               s{i}_bresp,
    input  wire                     s{i}_bvalid,
    output wire                     s{i}_bready,
    
    output wire [ID_WIDTH-1:0]     s{i}_arid,
    output wire [ADDR_WIDTH-1:0]   s{i}_araddr,
    output wire [7:0]               s{i}_arlen,
    output wire [2:0]               s{i}_arsize,
    output wire [1:0]               s{i}_arburst,
    output wire                     s{i}_arvalid,
    input  wire                     s{i}_arready,
    
    input  wire [ID_WIDTH-1:0]     s{i}_rid,
    input  wire [DATA_WIDTH-1:0]   s{i}_rdata,
    input  wire [1:0]               s{i}_rresp,
    input  wire                     s{i}_rlast,
    input  wire                     s{i}_rvalid,
    output wire                     s{i}_rready,"""
            
        # Remove last comma
        rtl = rtl.rstrip(',')
        
        rtl += """
);

    // Interconnect implementation
    // This is a placeholder for the actual interconnect logic
    // The full implementation would include:
    // - Address decoding
    // - Arbitration logic
    // - ID management
    // - CDC FIFOs if needed
    // - Security firewalls
    // - QoS handling
    
    // CDC logic will be inserted for cross-domain connections
    // axi_cdc_fifo instances will be generated for domain crossings
    
endmodule
"""
        return rtl
        
    def generate_vip(self, output_dir):
        """Generate VIP files"""
        vip_dir = os.path.join(output_dir, "vip")
        os.makedirs(vip_dir, exist_ok=True)
        
        # Generate package file
        pkg_file = os.path.join(vip_dir, f"{self.project.name}_vip_pkg.sv")
        with open(pkg_file, 'w') as f:
            f.write(self.generate_vip_package())
            
        # Generate test file
        test_file = os.path.join(vip_dir, f"{self.project.name}_base_test.sv")
        with open(test_file, 'w') as f:
            f.write(self.generate_base_test())
            
        # Generate Makefile
        if self.gen_scripts_var.get():
            makefile = os.path.join(vip_dir, "Makefile")
            with open(makefile, 'w') as f:
                f.write(self.generate_makefile())
                
        logger.info(f"Generated VIP in {vip_dir}")
        
    def generate_vip_package(self):
        """Generate UVM package"""
        return f"""// {self.project.name} VIP Package
// Generated by AMBA AXI4 RTL & VIP Generator v3

package {self.project.name}_vip_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Transaction class
    class axi_transaction extends uvm_sequence_item;
        `uvm_object_utils(axi_transaction)
        
        rand bit [{self.project.bus.addr_width-1}:0] addr;
        rand bit [{self.project.bus.data_width-1}:0] data[];
        rand bit [7:0] len;
        rand bit [2:0] size;
        rand bit [1:0] burst;
        rand bit write;
        
        function new(string name = "axi_transaction");
            super.new(name);
        endfunction
    endclass
    
    // Include other VIP components here
    
endpackage
"""
        
    def generate_base_test(self):
        """Generate base test"""
        return f"""// {self.project.name} Base Test
// Generated by AMBA AXI4 RTL & VIP Generator v3

class {self.project.name}_base_test extends uvm_test;
    `uvm_component_utils({self.project.name}_base_test)
    
    // Environment instance
    // {self.project.name}_env env;
    
    function new(string name = "{self.project.name}_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // env = {self.project.name}_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_name(), "Starting test", UVM_LOW)
        
        // Run test sequences here
        #1000ns;
        
        `uvm_info(get_name(), "Test complete", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
endclass
"""
        
    def generate_makefile(self):
        """Generate Makefile"""
        return f"""# Makefile for {self.project.name} VIP
# Generated by AMBA AXI4 RTL & VIP Generator v3

# Simulator selection
SIM ?= {self.simulator_var.get().lower()}

# Directories
RTL_DIR = ../rtl
VIP_DIR = .

# Source files
RTL_FILES = -f $(RTL_DIR)/filelist.f
VIP_FILES = $(VIP_DIR)/{self.project.name}_vip_pkg.sv \\
            $(VIP_DIR)/{self.project.name}_base_test.sv

# Compile and run
compile:
	vcs -sverilog -uvm $(RTL_FILES) $(VIP_FILES)

run:
	./simv +UVM_TESTNAME={self.project.name}_base_test

clean:
	rm -rf simv* csrc *.log

.PHONY: compile run clean
"""
        
    def save_project_config(self, output_dir):
        """Save project configuration to YAML"""
        config_file = os.path.join(output_dir, f"{self.project.name}_config.yaml")
        
        # Convert dataclasses to dict
        config_dict = {
            'project_name': self.project.name,
            'bus': asdict(self.project.bus),
            'masters': [asdict(m) for m in self.project.masters],
            'slaves': [asdict(s) for s in self.project.slaves],
            'bridges': [asdict(b) for b in self.project.bridges],
            'domains': [asdict(d) for d in self.project.domains]
        }
        
        with open(config_file, 'w') as f:
            yaml.dump(config_dict, f, default_flow_style=False)
            
        logger.info(f"Saved configuration to {config_file}")

class CLITab(ttk.Frame):
    """CLI command generation and preview tab"""
    
    def __init__(self, parent, project):
        super().__init__(parent)
        self.project = project
        self.create_widgets()
        
    def create_widgets(self):
        """Create CLI tab widgets"""
        # Title
        title = ttk.Label(self, text="Command-Line Interface", font=('Arial', 14, 'bold'))
        title.pack(pady=10)
        
        # Description
        desc = ttk.Label(self, text="Generate and preview CLI commands for your current configuration")
        desc.pack(pady=5)
        
        # Command generation frame
        cmd_frame = ttk.LabelFrame(self, text="Generated CLI Command", padding=10)
        cmd_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Command text area with scrollbar
        text_frame = ttk.Frame(cmd_frame)
        text_frame.pack(fill=tk.BOTH, expand=True)
        
        scrollbar = ttk.Scrollbar(text_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.command_text = tk.Text(text_frame, height=15, wrap=tk.WORD, 
                                   yscrollcommand=scrollbar.set,
                                   font=('Courier', 10))
        self.command_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=self.command_text.yview)
        
        # Button frame
        button_frame = ttk.Frame(self)
        button_frame.pack(pady=10)
        
        ttk.Button(button_frame, text="Generate Command", 
                  command=self.generate_command).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Copy to Clipboard", 
                  command=self.copy_to_clipboard).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Export Script", 
                  command=self.export_script).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Save Config YAML", 
                  command=self.save_config).pack(side=tk.LEFT, padx=5)
        
        # Options frame
        options_frame = ttk.LabelFrame(self, text="CLI Options", padding=10)
        options_frame.pack(fill=tk.X, padx=20, pady=10)
        
        # Output directory option
        ttk.Label(options_frame, text="Output Directory:").grid(row=0, column=0, sticky='w', padx=5, pady=5)
        self.output_dir_var = tk.StringVar(value="./generated")
        ttk.Entry(options_frame, textvariable=self.output_dir_var, width=40).grid(row=0, column=1, padx=5, pady=5)
        
        # Log level option
        ttk.Label(options_frame, text="Log Level:").grid(row=1, column=0, sticky='w', padx=5, pady=5)
        self.log_level_var = tk.StringVar(value="INFO")
        ttk.Combobox(options_frame, textvariable=self.log_level_var,
                    values=["DEBUG", "INFO", "WARNING", "ERROR"]).grid(row=1, column=1, padx=5, pady=5)
        
        # Generation mode
        ttk.Label(options_frame, text="Generation Mode:").grid(row=2, column=0, sticky='w', padx=5, pady=5)
        self.gen_mode_var = tk.StringVar(value="both")
        ttk.Combobox(options_frame, textvariable=self.gen_mode_var,
                    values=["rtl", "vip", "both"]).grid(row=2, column=1, padx=5, pady=5)
        
        # Auto-generate on startup
        self.generate_command()
        
    def generate_command(self):
        """Generate CLI command from current project configuration"""
        self.command_text.delete(1.0, tk.END)
        
        # Generate the main command
        cmd = "#!/bin/bash\n"
        cmd += "# AXI4 Generator CLI Command\n"
        cmd += f"# Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n"
        
        # Save config file command
        cmd += "# Step 1: Create configuration file\n"
        cmd += "cat > config.yaml << 'EOF'\n"
        cmd += self.generate_yaml_config()
        cmd += "EOF\n\n"
        
        # Generate command
        cmd += "# Step 2: Run the generator\n"
        cmd += "axi_generator \\\n"
        cmd += "    --config config.yaml \\\n"
        cmd += f"    --output {self.output_dir_var.get()} \\\n"
        cmd += f"    --log-level {self.log_level_var.get()} \\\n"
        cmd += f"    --mode {self.gen_mode_var.get()}\n\n"
        
        # Add comments about what will be generated
        cmd += "# This will generate:\n"
        if self.gen_mode_var.get() in ["rtl", "both"]:
            cmd += f"#   - RTL in {self.output_dir_var.get()}/rtl/\n"
        if self.gen_mode_var.get() in ["vip", "both"]:
            cmd += f"#   - VIP in {self.output_dir_var.get()}/vip/\n"
        cmd += f"#   - Configuration saved to {self.output_dir_var.get()}/config.yaml\n"
        
        self.command_text.insert(1.0, cmd)
        
    def generate_yaml_config(self):
        """Generate YAML configuration for current project"""
        config = {
            'project_name': self.project.name,
            'bus': asdict(self.project.bus),
            'masters': [asdict(m) for m in self.project.masters],
            'slaves': [asdict(s) for s in self.project.slaves],
            'bridges': [asdict(b) for b in self.project.bridges],
            'domains': [asdict(d) for d in self.project.domains]
        }
        
        import io
        stream = io.StringIO()
        yaml.dump(config, stream, default_flow_style=False)
        return stream.getvalue()
        
    def copy_to_clipboard(self):
        """Copy command to clipboard"""
        command = self.command_text.get(1.0, tk.END).strip()
        self.clipboard_clear()
        self.clipboard_append(command)
        messagebox.showinfo("Success", "Command copied to clipboard!")
        
    def export_script(self):
        """Export as executable script"""
        filename = filedialog.asksaveasfilename(
            title="Export Script",
            defaultextension=".sh",
            filetypes=[("Shell Script", "*.sh"), ("All Files", "*.*")]
        )
        
        if filename:
            command = self.command_text.get(1.0, tk.END).strip()
            with open(filename, 'w') as f:
                f.write(command)
            os.chmod(filename, 0o755)
            messagebox.showinfo("Success", f"Script exported to {filename}")
            
    def save_config(self):
        """Save configuration YAML file"""
        filename = filedialog.asksaveasfilename(
            title="Save Configuration",
            defaultextension=".yaml",
            filetypes=[("YAML Files", "*.yaml"), ("All Files", "*.*")]
        )
        
        if filename:
            config_yaml = self.generate_yaml_config()
            with open(filename, 'w') as f:
                f.write(config_yaml)
            messagebox.showinfo("Success", f"Configuration saved to {filename}")
            
    def refresh(self):
        """Refresh the CLI command with current project state"""
        self.generate_command()

class AXI4GeneratorGUI(tk.Tk):
    """Main GUI Application"""
    
    def __init__(self):
        super().__init__()
        
        self.title("AMBA AXI4 RTL & VIP Generator v3")
        self.geometry("1200x700")
        
        # Initialize project
        self.project = ProjectConfig()
        
        # Create menu bar
        self.create_menu()
        
        # Create main notebook
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(fill=tk.BOTH, expand=True)
        
        # Create Canvas tab
        self.canvas_tab = CanvasTab(self.notebook, self.project)
        self.notebook.add(self.canvas_tab, text="Canvas")
        
        # Create Templates tab
        self.templates_tab = TemplateGallery(self.notebook, self.load_template)
        self.notebook.add(self.templates_tab, text="Templates")
        
        # Create CLI tab
        self.cli_tab = CLITab(self.notebook, self.project)
        self.notebook.add(self.cli_tab, text="CLI")
        
        # Bind tab change event to refresh CLI
        self.notebook.bind("<<NotebookTabChanged>>", self.on_tab_changed)
        
        # Status bar
        self.status_bar = ttk.Label(self, text="Ready", relief=tk.SUNKEN, anchor='w')
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        logger.info("Application started")
        
    def on_tab_changed(self, event):
        """Handle tab change event"""
        selected_tab = self.notebook.select()
        tab_text = self.notebook.tab(selected_tab, "text")
        
        # Refresh CLI tab when it's selected
        if tab_text == "CLI":
            self.cli_tab.refresh()
            self.status_bar.config(text="CLI command generated from current configuration")
        elif tab_text == "Canvas":
            self.status_bar.config(text="Design your bus topology")
        elif tab_text == "Templates":
            self.status_bar.config(text="Select a template to start")
            
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
        file_menu.add_command(label="Exit", command=self.quit)
        
        # Generate menu
        gen_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Generate", menu=gen_menu)
        gen_menu.add_command(label="Generate...", command=self.open_generation_settings)
        gen_menu.add_command(label="Generate RTL Only", command=lambda: self.quick_generate('rtl'))
        gen_menu.add_command(label="Generate VIP Only", command=lambda: self.quick_generate('vip'))
        
        # Help menu
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="About", command=self.show_about)
        
    def new_project(self):
        """Create new project"""
        result = messagebox.askyesno("New Project", 
                                    "This will clear the current design. Continue?")
        if result:
            self.project = ProjectConfig()
            self.canvas_tab.clear_canvas()
            self.status_bar.config(text="New project created")
            
    def open_project(self):
        """Open project from YAML file"""
        file_path = filedialog.askopenfilename(
            title="Open Project",
            filetypes=[("YAML files", "*.yaml"), ("All files", "*.*")]
        )
        
        if file_path:
            try:
                with open(file_path, 'r') as f:
                    config = yaml.safe_load(f)
                    
                # Load configuration
                self.project = self.load_project_from_dict(config)
                self.canvas_tab.clear_canvas()
                self.canvas_tab.redraw_all_nodes()
                
                self.status_bar.config(text=f"Opened: {file_path}")
                logger.info(f"Opened project: {file_path}")
                
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
        file_path = filedialog.asksaveasfilename(
            title="Save Project",
            defaultextension=".yaml",
            filetypes=[("YAML files", "*.yaml"), ("All files", "*.*")]
        )
        
        if file_path:
            self.project_file = file_path
            self.save_project_to_file(file_path)
            
    def save_project_to_file(self, file_path):
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
            
            with open(file_path, 'w') as f:
                yaml.dump(config_dict, f, default_flow_style=False)
                
            self.status_bar.config(text=f"Saved: {file_path}")
            logger.info(f"Saved project: {file_path}")
            
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
        
    def load_template(self, template):
        """Load template from Templates tab"""
        self.canvas_tab.load_template(template)
        # Switch to Canvas tab
        self.notebook.select(0)
        self.status_bar.config(text=f"Loaded template: {template['name']}")
        
    def open_generation_settings(self):
        """Open generation settings dialog"""
        GenerationSettingsDialog(self, self.project)
        
    def quick_generate(self, gen_type):
        """Quick generate RTL or VIP"""
        output_dir = filedialog.askdirectory(title="Select Output Directory")
        if output_dir:
            dialog = GenerationSettingsDialog(self, self.project)
            dialog.output_dir_var.set(output_dir)
            
            if gen_type == 'rtl':
                dialog.generate_rtl(output_dir)
            elif gen_type == 'vip':
                dialog.generate_vip(output_dir)
                
            dialog.save_project_config(output_dir)
            messagebox.showinfo("Success", f"Generated {gen_type.upper()} in {output_dir}")
            dialog.destroy()
            
    def show_about(self):
        """Show about dialog"""
        messagebox.showinfo(
            "About",
            "AMBA AXI4 RTL & VIP Generator v3\n\n"
            "A comprehensive tool for generating AXI4 interconnects\n"
            "and verification environments.\n\n"
            "Features:\n"
            "- Visual topology design\n"
            "- Smart layout & routing\n"
            "- Advanced protocol features\n"
            "- RTL & UVM generation\n"
            "- Template gallery\n"
            "- CLI support"
        )

def main():
    """Main entry point"""
    app = AXI4GeneratorGUI()
    app.mainloop()

if __name__ == "__main__":
    main()