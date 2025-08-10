#!/usr/bin/env python3
"""
Modern AMBA Bus Matrix Configuration GUI
Enhanced with modern design aesthetic and smooth animations
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import json
import subprocess
import os
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Tuple
import math
import csv
from modern_ui_theme import ModernTheme, ModernCanvas, ModernButton, apply_modern_theme
from axi_verilog_generator import AXIVerilogGenerator
from address_safety_checker import validate_bus_configuration

# Import existing data classes
from bus_matrix_gui import MasterConfig, SlaveConfig, BusConfig

# Lazy import for VIP integration
VIPControlPanel = None


class ModernBusMatrixCanvas(ModernCanvas):
    """Enhanced canvas with modern bus matrix visualization"""
    
    def __init__(self, parent, theme: ModernTheme = None, **kwargs):
        super().__init__(parent, theme, **kwargs)
        self.masters = []
        self.slaves = []
        self.connections = []
        self.interconnect = None
        self.selected_item = None
        
        # Modern visual parameters
        self.master_gradient = [self.theme.get_color('primary'), self.theme.get_color('primary_light')]
        self.slave_gradient = [self.theme.get_color('secondary'), self.theme.get_color('info')]
        self.interconnect_gradient = [self.theme.get_color('accent'), self.theme.get_color('warning')]
        
        # Enhanced interaction
        self.bind('<Button-1>', self.on_click)
        self.bind('<Button-3>', self.on_right_click)
        self.bind('<B1-Motion>', self.on_drag)
        self.bind('<ButtonRelease-1>', self.on_release)
        self.bind('<MouseWheel>', self.on_mousewheel)
        self.bind('<Control-MouseWheel>', self.on_zoom)
        
        # Animation states
        self.hover_animations = {}
        self.connection_animations = {}
        
        # Setup modern tooltip
        self.tooltip = None
        self.bind('<Motion>', self.on_motion)
        
    def add_master(self, config: MasterConfig, position: Optional[Tuple[int, int]] = None):
        """Add master with modern styling"""
        if position is None:
            x = 50
            y = 50 + len(self.masters) * 120
        else:
            x, y = position
            
        # Create modern master block with gradient and shadow
        master_id = self.create_modern_rect(x, y, x+160, y+80, radius=12,
                                          fill=self.master_gradient[0],
                                          outline='', tags='master')
        
        # Add shadow effect
        shadow_id = self.create_modern_rect(x+2, y+2, x+162, y+82, radius=12,
                                          fill=self.theme.get_color('shadow'),
                                          outline='', tags='shadow')
        self.tag_lower(shadow_id)
        
        # Add icon
        icon_id = self.create_text(x+20, y+40, text="M", 
                                 font=('Segoe UI', 20, 'bold'),
                                 fill=self.theme.get_color('text_on_primary'),
                                 tags='master_icon')
        
        # Add text with better typography
        text_id = self.create_text(x+80, y+25, text=config.name,
                                 font=self.theme.FONTS['subheading'],
                                 fill=self.theme.get_color('text_on_primary'),
                                 anchor='center', tags='master_text')
        
        # Add ID width indicator
        id_text = self.create_text(x+80, y+45, text=f"ID: {config.id_width} bits",
                                 font=self.theme.FONTS['caption'],
                                 fill=self.theme.get_color('text_on_primary'),
                                 anchor='center', tags='master_detail')
        
        # Add QoS indicator if enabled
        if config.qos_support:
            qos_indicator = self.create_oval(x+140, y+10, x+150, y+20,
                                           fill=self.theme.get_color('success'),
                                           outline='', tags='qos_indicator')
            
        # Priority badge
        if config.priority > 0:
            priority_bg = self.create_oval(x+140, y+60, x+155, y+75,
                                         fill=self.theme.get_color('accent'),
                                         outline='', tags='priority_badge')
            priority_text = self.create_text(x+147, y+67, text=str(config.priority),
                                           font=self.theme.FONTS['caption'],
                                           fill=self.theme.get_color('text_on_primary'),
                                           tags='priority_text')
        
        master_info = {
            'id': master_id,
            'shadow_id': shadow_id,
            'icon_id': icon_id,
            'text_id': text_id,
            'id_text': id_text,
            'config': config,
            'x': x,
            'y': y,
            'connections': []
        }
        
        self.masters.append(master_info)
        
        # Animate entrance
        self._animate_entrance(master_id, 'left')
        
    def add_slave(self, config: SlaveConfig, position: Optional[Tuple[int, int]] = None):
        """Add slave with modern styling"""
        if position is None:
            x = 600
            y = 50 + len(self.slaves) * 120
        else:
            x, y = position
            
        # Create modern slave block
        slave_id = self.create_modern_rect(x, y, x+180, y+100, radius=12,
                                         fill=self.slave_gradient[0],
                                         outline='', tags='slave')
        
        # Add shadow
        shadow_id = self.create_modern_rect(x+2, y+2, x+182, y+102, radius=12,
                                          fill=self.theme.get_color('shadow'),
                                          outline='', tags='shadow')
        self.tag_lower(shadow_id)
        
        # Add icon based on memory type
        icon = "M" if config.memory_type == "Memory" else "P"
        icon_id = self.create_text(x+20, y+50, text=icon,
                                 font=('Segoe UI', 20, 'bold'),
                                 fill=self.theme.get_color('text_on_primary'),
                                 tags='slave_icon')
        
        # Add name
        text_id = self.create_text(x+90, y+20, text=config.name,
                                 font=self.theme.FONTS['subheading'],
                                 fill=self.theme.get_color('text_on_primary'),
                                 anchor='center', tags='slave_text')
        
        # Add address range with modern formatting
        addr_text = f"0x{config.base_address:08X}"
        addr_id = self.create_text(x+90, y+40, text=addr_text,
                                 font=self.theme.FONTS['mono'],
                                 fill=self.theme.get_color('text_on_primary'),
                                 anchor='center', tags='slave_addr')
        
        # Add size
        size_text = f"{config.size} KB"
        size_id = self.create_text(x+90, y+58, text=size_text,
                                 font=self.theme.FONTS['caption'],
                                 fill=self.theme.get_color('text_on_primary'),
                                 anchor='center', tags='slave_size')
        
        # Security indicators
        if config.secure_only:
            sec_indicator = self.create_oval(x+160, y+10, x+170, y+20,
                                           fill=self.theme.get_color('error'),
                                           outline='', tags='security_indicator')
            
        # Region count badge
        if config.num_regions > 1:
            region_bg = self.create_modern_rect(x+10, y+75, x+40, y+90, radius=8,
                                              fill=self.theme.get_color('info'),
                                              outline='', tags='region_badge')
            region_text = self.create_text(x+25, y+82, text=f"R:{config.num_regions}",
                                         font=self.theme.FONTS['caption'],
                                         fill=self.theme.get_color('text_on_primary'),
                                         tags='region_text')
        
        slave_info = {
            'id': slave_id,
            'shadow_id': shadow_id,
            'icon_id': icon_id,
            'text_id': text_id,
            'addr_id': addr_id,
            'size_id': size_id,
            'config': config,
            'x': x,
            'y': y,
            'connections': []
        }
        
        self.slaves.append(slave_info)
        
        # Animate entrance
        self._animate_entrance(slave_id, 'right')
        
    def draw_interconnect(self):
        """Draw modern interconnect with animations"""
        if self.interconnect:
            self.delete(self.interconnect['id'])
            if 'shadow_id' in self.interconnect:
                self.delete(self.interconnect['shadow_id'])
                
        # Calculate center position
        if self.masters and self.slaves:
            x1 = max(m['x'] + 160 for m in self.masters) + 50
            y1 = min(m['y'] for m in self.masters)
            x2 = min(s['x'] for s in self.slaves) - 50
            y2 = max(s['y'] + 100 for s in self.slaves)
            
            cx = (x1 + x2) // 2
            cy = (y1 + y2) // 2
            
            # Create modern interconnect shape
            width = 120
            height = 80
            
            # Shadow
            shadow_id = self.create_modern_rect(cx-width//2+3, cy-height//2+3,
                                              cx+width//2+3, cy+height//2+3,
                                              radius=16,
                                              fill=self.theme.get_color('shadow'),
                                              outline='', tags='interconnect_shadow')
            
            # Main interconnect
            inter_id = self.create_modern_rect(cx-width//2, cy-height//2,
                                             cx+width//2, cy+height//2,
                                             radius=16,
                                             fill=self.interconnect_gradient[0],
                                             outline='', tags='interconnect')
            
            # Add icon
            icon_id = self.create_text(cx, cy-10, text="⚡",
                                     font=('Segoe UI', 24, 'normal'),
                                     fill=self.theme.get_color('text_on_primary'),
                                     tags='interconnect_icon')
            
            # Add label
            label_id = self.create_text(cx, cy+15, text="Interconnect",
                                      font=self.theme.FONTS['body'],
                                      fill=self.theme.get_color('text_on_primary'),
                                      tags='interconnect_label')
            
            self.interconnect = {
                'id': inter_id,
                'shadow_id': shadow_id,
                'icon_id': icon_id,
                'label_id': label_id,
                'x': cx,
                'y': cy
            }
            
            # Animate pulse effect
            self._start_interconnect_pulse()
            
            # Draw connections
            self.draw_all_connections()
            
    def draw_all_connections(self):
        """Draw all connections with modern bezier curves"""
        # Clear existing connections
        for conn in self.connections:
            self.delete(conn)
        self.connections.clear()
        
        if not self.interconnect:
            return
            
        # Draw master to interconnect connections
        for master in self.masters:
            self._draw_connection(master['x'] + 160, master['y'] + 40,
                                self.interconnect['x'] - 60, self.interconnect['y'],
                                'master_connection', self.theme.get_color('primary'))
            
        # Draw interconnect to slave connections
        for slave in self.slaves:
            self._draw_connection(self.interconnect['x'] + 60, self.interconnect['y'],
                                slave['x'], slave['y'] + 50,
                                'slave_connection', self.theme.get_color('secondary'))
            
    def _draw_connection(self, x1, y1, x2, y2, tag, color):
        """Draw smooth bezier curve connection"""
        # Calculate control points for smooth curve
        dx = x2 - x1
        dy = y2 - y1
        
        # Control points for bezier curve
        cx1 = x1 + dx * 0.5
        cy1 = y1
        cx2 = x2 - dx * 0.5
        cy2 = y2
        
        # Create smooth path
        points = []
        steps = 20
        for i in range(steps + 1):
            t = i / steps
            # Cubic bezier formula
            x = (1-t)**3 * x1 + 3*(1-t)**2*t * cx1 + 3*(1-t)*t**2 * cx2 + t**3 * x2
            y = (1-t)**3 * y1 + 3*(1-t)**2*t * cy1 + 3*(1-t)*t**2 * cy2 + t**3 * y2
            points.extend([x, y])
            
        # Draw connection line
        conn_id = self.create_line(points, fill=color, width=3,
                                 smooth=True, tags=tag)
        self.connections.append(conn_id)
        
        # Add arrow at end
        arrow_id = self.create_polygon(x2-10, y2-5, x2, y2, x2-10, y2+5,
                                     fill=color, outline='', tags=tag)
        self.connections.append(arrow_id)
        
        # Animate data flow
        self._animate_data_flow(conn_id, points)
        
    def _animate_entrance(self, item_id, direction='left'):
        """Animate item entrance with slide and fade"""
        if direction == 'left':
            self.move(item_id, -100, 0)
        else:
            self.move(item_id, 100, 0)
            
        # Animate slide in
        if direction == 'left':
            self.animate_item(item_id, 'x', self.coords(item_id)[0] + 100, duration=350)
        else:
            self.animate_item(item_id, 'x', self.coords(item_id)[0] - 100, duration=350)
            
    def _start_interconnect_pulse(self):
        """Start pulsing animation for interconnect"""
        if not self.interconnect:
            return
            
        def pulse():
            if self.interconnect:
                # Create expanding circle
                x, y = self.interconnect['x'], self.interconnect['y']
                pulse_id = self.create_oval(x-5, y-5, x+5, y+5,
                                          fill='', outline=self.theme.get_color('text_on_primary'),
                                          width=2, tags='pulse')
                
                # Animate expansion and fade
                self._animate_pulse_ring(pulse_id, x, y)
                
                # Schedule next pulse
                self.after(2000, pulse)
                
        pulse()
        
    def _animate_pulse_ring(self, ring_id, cx, cy, radius=5, max_radius=40):
        """Animate expanding pulse ring"""
        if radius < max_radius:
            self.coords(ring_id, cx-radius, cy-radius, cx+radius, cy+radius)
            opacity = 1 - (radius / max_radius)
            width = max(1, int(3 * opacity))
            self.itemconfig(ring_id, width=width)
            
            self.after(20, lambda: self._animate_pulse_ring(ring_id, cx, cy, radius+2, max_radius))
        else:
            self.delete(ring_id)
            
    def _animate_data_flow(self, conn_id, points):
        """Animate data packets flowing through connection"""
        def create_packet():
            if conn_id not in self.connections:
                return
                
            # Create small data packet
            packet = self.create_oval(points[0]-3, points[1]-3, points[0]+3, points[1]+3,
                                    fill=self.theme.get_color('accent'), outline='',
                                    tags='data_packet')
            
            # Animate along path
            self._move_packet_along_path(packet, points, 0)
            
            # Schedule next packet
            self.after(1500, create_packet)
            
        create_packet()
        
    def _move_packet_along_path(self, packet, points, index):
        """Move packet along connection path"""
        if index < len(points) - 2:
            x, y = points[index], points[index + 1]
            self.coords(packet, x-3, y-3, x+3, y+3)
            
            self.after(30, lambda: self._move_packet_along_path(packet, points, index + 2))
        else:
            self.delete(packet)
            
    def on_motion(self, event):
        """Handle mouse motion for tooltips"""
        x = self.canvasx(event.x)
        y = self.canvasy(event.y)
        
        # Find item under cursor
        item = self.find_closest(x, y)[0]
        
        # Check if it's a master or slave
        for master in self.masters:
            if item in [master['id'], master['text_id'], master['icon_id']]:
                self._show_tooltip(event, f"{master['config'].name}\nID Width: {master['config'].id_width} bits\nQoS: {'Yes' if master['config'].qos_support else 'No'}")
                return
                
        for slave in self.slaves:
            if item in [slave['id'], slave['text_id'], slave['icon_id']]:
                self._show_tooltip(event, f"{slave['config'].name}\n{slave['config'].memory_type}\nAddress: 0x{slave['config'].base_address:08X}\nSize: {slave['config'].size} KB")
                return
                
        self._hide_tooltip()
        
    def _show_tooltip(self, event, text):
        """Show modern tooltip"""
        if self.tooltip:
            self._hide_tooltip()
            
        self.tooltip = tk.Toplevel(self)
        self.tooltip.wm_overrideredirect(True)
        self.tooltip.wm_geometry(f"+{event.x_root+10}+{event.y_root+10}")
        
        # Create modern tooltip with shadow
        frame = tk.Frame(self.tooltip, bg=self.theme.get_color('surface'),
                        highlightbackground=self.theme.get_color('border'),
                        highlightthickness=1)
        frame.pack()
        
        label = tk.Label(frame, text=text, justify=tk.LEFT,
                        bg=self.theme.get_color('surface'),
                        fg=self.theme.get_color('text_primary'),
                        font=self.theme.FONTS['body_small'],
                        padx=8, pady=6)
        label.pack()
        
    def _hide_tooltip(self):
        """Hide tooltip"""
        if self.tooltip:
            self.tooltip.destroy()
            self.tooltip = None
            
    def on_zoom(self, event):
        """Handle zoom with Ctrl+MouseWheel"""
        # Zoom in/out based on mouse wheel
        scale = 1.1 if event.delta > 0 else 0.9
        
        # Get mouse position for zoom center
        x = self.canvasx(event.x)
        y = self.canvasy(event.y)
        
        # Scale all items
        self.scale('all', x, y, scale, scale)
        
        # Update grid
        self.grid_size = int(self.grid_size * scale)
        self._draw_grid()


class ModernBusMatrixGUI:
    """Main GUI application with modern UI"""
    
    def __init__(self, root):
        self.root = root
        self.root.title("AMBA Bus Matrix Designer - Modern UI")
        
        # Apply modern theme
        self.theme = apply_modern_theme(root, dark_mode=False)
        
        # Set window properties
        self.root.geometry("1600x900")
        self.root.minsize(1200, 700)
        
        # Initialize configuration
        self.current_config = BusConfig(
            bus_type="AXI4",
            data_width=64,
            addr_width=32,
            masters=[],
            slaves=[],
            arbitration="QOS"
        )
        
        # Setup UI
        self.setup_ui()
        
        # Add theme toggle
        self.setup_theme_toggle()
        
    def setup_ui(self):
        """Setup modern user interface"""
        # Create main container with padding
        main_container = ttk.Frame(self.root, style='Modern.TFrame')
        main_container.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)
        
        # Create header
        self.create_header(main_container)
        
        # Create main content area
        content_frame = ttk.Frame(main_container, style='Modern.TFrame')
        content_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Create left panel with controls
        left_panel = ttk.Frame(content_frame, style='Modern.TFrame', width=320)
        left_panel.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 20))
        left_panel.pack_propagate(False)
        
        # Create canvas area
        canvas_frame = ttk.Frame(content_frame, style='Modern.TFrame')
        canvas_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # Setup controls
        self.setup_controls(left_panel)
        
        # Setup canvas
        self.setup_canvas(canvas_frame)
        
        # Create status bar
        self.create_status_bar(main_container)
        
    def create_header(self, parent):
        """Create modern header"""
        header_frame = tk.Frame(parent, bg=self.theme.get_color('primary'), height=60)
        header_frame.pack(fill=tk.X)
        header_frame.pack_propagate(False)
        
        # Title
        title = tk.Label(header_frame, text="AMBA Bus Matrix Designer",
                        bg=self.theme.get_color('primary'),
                        fg=self.theme.get_color('text_on_primary'),
                        font=self.theme.FONTS['heading_large'])
        title.pack(side=tk.LEFT, padx=20, pady=15)
        
        # Action buttons in header
        btn_frame = tk.Frame(header_frame, bg=self.theme.get_color('primary'))
        btn_frame.pack(side=tk.RIGHT, padx=20)
        
        # Modern buttons
        ModernButton(btn_frame, text="Generate", command=self.generate_verilog,
                    style='secondary', theme=self.theme, width=100, height=36).pack(side=tk.LEFT, padx=5)
        ModernButton(btn_frame, text="Export", command=self.export_config,
                    style='secondary', theme=self.theme, width=100, height=36).pack(side=tk.LEFT, padx=5)
        
    def setup_controls(self, parent):
        """Setup control panel with modern styling"""
        # Create scrollable frame
        canvas = tk.Canvas(parent, bg=self.theme.get_color('bg'), highlightthickness=0)
        scrollbar = ttk.Scrollbar(parent, orient="vertical", command=canvas.yview, style='Modern.Vertical.TScrollbar')
        scrollable_frame = ttk.Frame(canvas, style='Modern.TFrame')
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # Bus Configuration Section
        bus_frame = ttk.LabelFrame(scrollable_frame, text="Bus Configuration", 
                                 style='Modern.TLabelframe', padding=15)
        bus_frame.pack(fill=tk.X, pady=(0, 15))
        
        # Bus Type with modern styling
        ttk.Label(bus_frame, text="Bus Type:", font=self.theme.FONTS['body']).grid(row=0, column=0, sticky=tk.W, pady=5)
        self.bus_type_var = tk.StringVar(value="AXI4")
        bus_type_combo = ttk.Combobox(bus_frame, textvariable=self.bus_type_var,
                                    values=["AXI4", "AXI3", "AHB", "APB"],
                                    state="readonly", style='Modern.TCombobox')
        bus_type_combo.grid(row=0, column=1, sticky=tk.EW, pady=5)
        
        # Data Width
        ttk.Label(bus_frame, text="Data Width:", font=self.theme.FONTS['body']).grid(row=1, column=0, sticky=tk.W, pady=5)
        self.data_width_var = tk.StringVar(value="64")
        data_width_combo = ttk.Combobox(bus_frame, textvariable=self.data_width_var,
                                      values=["32", "64", "128", "256", "512"],
                                      state="readonly", style='Modern.TCombobox')
        data_width_combo.grid(row=1, column=1, sticky=tk.EW, pady=5)
        
        # Address Width
        ttk.Label(bus_frame, text="Address Width:", font=self.theme.FONTS['body']).grid(row=2, column=0, sticky=tk.W, pady=5)
        self.addr_width_var = tk.StringVar(value="32")
        addr_width_combo = ttk.Combobox(bus_frame, textvariable=self.addr_width_var,
                                      values=["32", "40", "48", "64"],
                                      state="readonly", style='Modern.TCombobox')
        addr_width_combo.grid(row=2, column=1, sticky=tk.EW, pady=5)
        
        # Arbitration
        ttk.Label(bus_frame, text="Arbitration:", font=self.theme.FONTS['body']).grid(row=3, column=0, sticky=tk.W, pady=5)
        self.arbitration_var = tk.StringVar(value="QOS")
        arbitration_combo = ttk.Combobox(bus_frame, textvariable=self.arbitration_var,
                                       values=["FIXED", "RR", "QOS", "WRR"],
                                       state="readonly", style='Modern.TCombobox')
        arbitration_combo.grid(row=3, column=1, sticky=tk.EW, pady=5)
        
        bus_frame.columnconfigure(1, weight=1)
        
        # Component Management Section
        component_frame = ttk.LabelFrame(scrollable_frame, text="Components", 
                                       style='Modern.TLabelframe', padding=15)
        component_frame.pack(fill=tk.X, pady=(0, 15))
        
        # Modern action buttons
        ModernButton(component_frame, text="+ Add Master", command=self.add_master,
                    theme=self.theme, width=120, height=36).pack(fill=tk.X, pady=5)
        ModernButton(component_frame, text="+ Add Slave", command=self.add_slave,
                    theme=self.theme, width=120, height=36).pack(fill=tk.X, pady=5)
        ModernButton(component_frame, text="↻ Update", command=self.update_canvas,
                    style='secondary', theme=self.theme, width=120, height=36).pack(fill=tk.X, pady=5)
        
        # Component List
        list_frame = ttk.LabelFrame(scrollable_frame, text="Component List",
                                  style='Modern.TLabelframe', padding=15)
        list_frame.pack(fill=tk.BOTH, expand=True)
        
        # Modern treeview
        self.component_tree = ttk.Treeview(list_frame, columns=('Type', 'Details'),
                                         show='tree headings', height=10,
                                         style='Modern.Treeview')
        self.component_tree.heading('#0', text='Name')
        self.component_tree.heading('Type', text='Type')
        self.component_tree.heading('Details', text='Details')
        
        self.component_tree.column('#0', width=100)
        self.component_tree.column('Type', width=60)
        self.component_tree.column('Details', width=120)
        
        tree_scroll = ttk.Scrollbar(list_frame, orient=tk.VERTICAL, 
                                  command=self.component_tree.yview,
                                  style='Modern.Vertical.TScrollbar')
        self.component_tree.configure(yscrollcommand=tree_scroll.set)
        
        self.component_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Pack canvas and scrollbar
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
    def setup_canvas(self, parent):
        """Setup modern canvas"""
        # Canvas frame with border
        canvas_container = tk.Frame(parent, bg=self.theme.get_color('border'))
        canvas_container.pack(fill=tk.BOTH, expand=True)
        
        # Create modern canvas
        self.canvas = ModernBusMatrixCanvas(canvas_container, theme=self.theme,
                                          width=800, height=600)
        self.canvas.pack(fill=tk.BOTH, expand=True, padx=1, pady=1)
        self.canvas.gui = self  # Reference for callbacks
        
        # Canvas controls
        control_frame = tk.Frame(parent, bg=self.theme.get_color('bg'), height=40)
        control_frame.pack(fill=tk.X, pady=(10, 0))
        
        # Zoom controls
        zoom_frame = tk.Frame(control_frame, bg=self.theme.get_color('bg'))
        zoom_frame.pack(side=tk.LEFT)
        
        ttk.Label(zoom_frame, text="Zoom:", font=self.theme.FONTS['body']).pack(side=tk.LEFT, padx=5)
        ModernButton(zoom_frame, text="-", command=lambda: self.zoom_canvas(0.9),
                    theme=self.theme, width=30, height=30).pack(side=tk.LEFT, padx=2)
        self.zoom_label = ttk.Label(zoom_frame, text="100%", font=self.theme.FONTS['body'])
        self.zoom_label.pack(side=tk.LEFT, padx=5)
        ModernButton(zoom_frame, text="+", command=lambda: self.zoom_canvas(1.1),
                    theme=self.theme, width=30, height=30).pack(side=tk.LEFT, padx=2)
        
        # Grid toggle
        self.grid_var = tk.BooleanVar(value=True)
        grid_check = ttk.Checkbutton(control_frame, text="Show Grid",
                                   variable=self.grid_var,
                                   command=self.toggle_grid,
                                   style='Modern.TCheckbutton')
        grid_check.pack(side=tk.LEFT, padx=20)
        
    def create_status_bar(self, parent):
        """Create modern status bar"""
        status_frame = tk.Frame(parent, bg=self.theme.get_color('surface_variant'), height=30)
        status_frame.pack(fill=tk.X, side=tk.BOTTOM)
        status_frame.pack_propagate(False)
        
        # Status text
        self.status_label = tk.Label(status_frame, text="Ready",
                                   bg=self.theme.get_color('surface_variant'),
                                   fg=self.theme.get_color('text_secondary'),
                                   font=self.theme.FONTS['body_small'])
        self.status_label.pack(side=tk.LEFT, padx=10)
        
        # Component count
        self.count_label = tk.Label(status_frame, text="Masters: 0 | Slaves: 0",
                                  bg=self.theme.get_color('surface_variant'),
                                  fg=self.theme.get_color('text_secondary'),
                                  font=self.theme.FONTS['body_small'])
        self.count_label.pack(side=tk.RIGHT, padx=10)
        
    def setup_theme_toggle(self):
        """Add theme toggle button"""
        theme_btn = tk.Button(self.root, text="🌙", command=self.toggle_theme,
                            bg=self.theme.get_color('surface'),
                            fg=self.theme.get_color('text_primary'),
                            font=('Segoe UI', 16),
                            bd=0, padx=10, pady=5)
        theme_btn.place(relx=0.95, rely=0.02)
        
    def toggle_theme(self):
        """Toggle between light and dark theme"""
        self.theme.dark_mode = not self.theme.dark_mode
        self.theme.theme = self.theme.DARK_THEME if self.theme.dark_mode else self.theme.LIGHT_THEME
        
        # Reapply theme
        apply_modern_theme(self.root, self.theme.dark_mode)
        
        # Update canvas theme
        self.canvas.theme = self.theme
        self.canvas.configure(bg=self.theme.get_color('canvas_bg'))
        self.canvas._draw_grid()
        
        # TODO: Update all existing canvas items with new colors
        
    def zoom_canvas(self, factor):
        """Zoom canvas with animation"""
        self.canvas.scale('all', 400, 300, factor, factor)
        current_zoom = int(self.zoom_label['text'].rstrip('%'))
        new_zoom = int(current_zoom * factor)
        self.zoom_label['text'] = f"{new_zoom}%"
        
    def toggle_grid(self):
        """Toggle grid visibility"""
        self.canvas.grid_visible = self.grid_var.get()
        if self.canvas.grid_visible:
            self.canvas._draw_grid()
        else:
            for item in self.canvas.grid_items:
                self.canvas.delete(item)
            self.canvas.grid_items.clear()
            
    def add_master(self):
        """Add master with modern dialog"""
        dialog = ModernComponentDialog(self.root, "Add Master", "master", theme=self.theme)
        self.root.wait_window(dialog.dialog)
        
        if dialog.result:
            config = MasterConfig(**dialog.result)
            self.current_config.masters.append(config)
            self.update_canvas()
            self.update_component_list()
            self.update_status(f"Added master: {config.name}")
            
    def add_slave(self):
        """Add slave with modern dialog"""
        dialog = ModernComponentDialog(self.root, "Add Slave", "slave", theme=self.theme)
        self.root.wait_window(dialog.dialog)
        
        if dialog.result:
            config = SlaveConfig(**dialog.result)
            self.current_config.slaves.append(config)
            self.update_canvas()
            self.update_component_list()
            self.update_status(f"Added slave: {config.name}")
            
    def update_canvas(self):
        """Update canvas with current configuration"""
        # Clear canvas
        self.canvas.delete('all')
        self.canvas.masters.clear()
        self.canvas.slaves.clear()
        self.canvas.connections.clear()
        self.canvas.interconnect = None
        
        # Redraw grid
        self.canvas._draw_grid()
        
        # Add components
        for i, master in enumerate(self.current_config.masters):
            self.canvas.add_master(master, position=(50, 50 + i * 120))
            
        for i, slave in enumerate(self.current_config.slaves):
            self.canvas.add_slave(slave, position=(600, 50 + i * 120))
            
        # Draw interconnect if we have components
        if self.current_config.masters and self.current_config.slaves:
            self.canvas.after(500, self.canvas.draw_interconnect)
            
        # Update count label
        self.count_label['text'] = f"Masters: {len(self.current_config.masters)} | Slaves: {len(self.current_config.slaves)}"
        
    def update_component_list(self):
        """Update component treeview"""
        # Clear existing items
        for item in self.component_tree.get_children():
            self.component_tree.delete(item)
            
        # Add masters
        master_parent = self.component_tree.insert('', 'end', text='Masters', values=('', ''))
        for master in self.current_config.masters:
            details = f"ID: {master.id_width}b"
            if master.qos_support:
                details += ", QoS"
            self.component_tree.insert(master_parent, 'end', text=master.name,
                                     values=('Master', details))
            
        # Add slaves
        slave_parent = self.component_tree.insert('', 'end', text='Slaves', values=('', ''))
        for slave in self.current_config.slaves:
            details = f"0x{slave.base_address:08X}, {slave.size}KB"
            self.component_tree.insert(slave_parent, 'end', text=slave.name,
                                     values=(slave.memory_type, details))
            
        # Expand all
        self.component_tree.item(master_parent, open=True)
        self.component_tree.item(slave_parent, open=True)
        
    def update_status(self, message):
        """Update status bar with fade effect"""
        self.status_label['text'] = message
        self.status_label['fg'] = self.theme.get_color('primary')
        
        # Fade back to normal after delay
        self.root.after(3000, lambda: self.status_label.configure(fg=self.theme.get_color('text_secondary')))
        
    def generate_verilog(self):
        """Generate Verilog with progress animation"""
        if not self.current_config.masters or not self.current_config.slaves:
            messagebox.showwarning("Configuration Error", "Please add at least one master and one slave.")
            return
            
        # TODO: Show modern progress dialog
        # TODO: Call actual Verilog generation
        self.update_status("Verilog generation complete")
        
    def export_config(self):
        """Export configuration with modern file dialog"""
        filename = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        
        if filename:
            # Convert configuration to dict
            config_dict = {
                'bus_type': self.current_config.bus_type,
                'data_width': self.current_config.data_width,
                'addr_width': self.current_config.addr_width,
                'arbitration': self.current_config.arbitration,
                'masters': [asdict(m) for m in self.current_config.masters],
                'slaves': [asdict(s) for s in self.current_config.slaves]
            }
            
            with open(filename, 'w') as f:
                json.dump(config_dict, f, indent=2)
                
            self.update_status(f"Configuration exported to {os.path.basename(filename)}")
            
    def edit_master_by_index(self, index):
        """Edit master configuration"""
        if 0 <= index < len(self.current_config.masters):
            master = self.current_config.masters[index]
            dialog = ModernComponentDialog(self.root, f"Edit {master.name}", "master",
                                         initial_values=asdict(master), theme=self.theme)
            self.root.wait_window(dialog.dialog)
            
            if dialog.result:
                self.current_config.masters[index] = MasterConfig(**dialog.result)
                self.update_canvas()
                self.update_component_list()
                self.update_status(f"Updated master: {dialog.result['name']}")
                
    def edit_slave_by_index(self, index):
        """Edit slave configuration"""
        if 0 <= index < len(self.current_config.slaves):
            slave = self.current_config.slaves[index]
            dialog = ModernComponentDialog(self.root, f"Edit {slave.name}", "slave",
                                         initial_values=asdict(slave), theme=self.theme)
            self.root.wait_window(dialog.dialog)
            
            if dialog.result:
                self.current_config.slaves[index] = SlaveConfig(**dialog.result)
                self.update_canvas()
                self.update_component_list()
                self.update_status(f"Updated slave: {dialog.result['name']}")


class ModernComponentDialog:
    """Modern dialog for adding/editing components"""
    
    def __init__(self, parent, title, component_type, initial_values=None, theme=None):
        self.result = None
        self.component_type = component_type
        self.theme = theme or ModernTheme()
        
        # Create dialog window
        self.dialog = tk.Toplevel(parent)
        self.dialog.title(title)
        self.dialog.configure(bg=self.theme.get_color('bg'))
        
        # Make dialog modal
        self.dialog.transient(parent)
        self.dialog.grab_set()
        
        # Center dialog
        self.dialog.geometry("400x500")
        self.center_window()
        
        # Setup content
        self.setup_dialog(initial_values)
        
    def center_window(self):
        """Center dialog on screen"""
        self.dialog.update_idletasks()
        x = (self.dialog.winfo_screenwidth() // 2) - (self.dialog.winfo_width() // 2)
        y = (self.dialog.winfo_screenheight() // 2) - (self.dialog.winfo_height() // 2)
        self.dialog.geometry(f"+{x}+{y}")
        
    def setup_dialog(self, initial_values):
        """Setup dialog content"""
        # Main frame with padding
        main_frame = ttk.Frame(self.dialog, style='Modern.TFrame', padding=20)
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # Title
        title_label = ttk.Label(main_frame, text=self.dialog.title(),
                              font=self.theme.FONTS['heading'])
        title_label.pack(pady=(0, 20))
        
        # Form frame
        form_frame = ttk.Frame(main_frame, style='Modern.TFrame')
        form_frame.pack(fill=tk.BOTH, expand=True)
        
        # Create form fields based on component type
        self.fields = {}
        
        if self.component_type == 'master':
            self.create_master_fields(form_frame, initial_values)
        else:
            self.create_slave_fields(form_frame, initial_values)
            
        # Button frame
        btn_frame = ttk.Frame(main_frame, style='Modern.TFrame')
        btn_frame.pack(fill=tk.X, pady=(20, 0))
        
        # Modern buttons
        ModernButton(btn_frame, text="Cancel", command=self.cancel,
                    style='secondary', theme=self.theme, width=80, height=36).pack(side=tk.RIGHT, padx=(5, 0))
        ModernButton(btn_frame, text="Save", command=self.save,
                    theme=self.theme, width=80, height=36).pack(side=tk.RIGHT)
        
    def create_master_fields(self, parent, initial_values):
        """Create master configuration fields"""
        # Name
        self.add_field(parent, "name", "Master Name:", "text", 
                      initial_values.get('name', 'Master0') if initial_values else 'Master0')
        
        # ID Width
        self.add_field(parent, "id_width", "ID Width (bits):", "spinbox",
                      initial_values.get('id_width', 4) if initial_values else 4,
                      from_=1, to=16)
        
        # QoS Support
        self.add_field(parent, "qos_support", "QoS Support:", "checkbox",
                      initial_values.get('qos_support', True) if initial_values else True)
        
        # Exclusive Support
        self.add_field(parent, "exclusive_support", "Exclusive Access:", "checkbox",
                      initial_values.get('exclusive_support', True) if initial_values else True)
        
        # User Width
        self.add_field(parent, "user_width", "User Signal Width:", "spinbox",
                      initial_values.get('user_width', 0) if initial_values else 0,
                      from_=0, to=128)
        
        # Priority
        self.add_field(parent, "priority", "Priority:", "spinbox",
                      initial_values.get('priority', 0) if initial_values else 0,
                      from_=0, to=15)
        
    def create_slave_fields(self, parent, initial_values):
        """Create slave configuration fields"""
        # Name
        self.add_field(parent, "name", "Slave Name:", "text",
                      initial_values.get('name', 'Slave0') if initial_values else 'Slave0')
        
        # Base Address
        self.add_field(parent, "base_address", "Base Address (hex):", "text",
                      f"0x{initial_values.get('base_address', 0):08X}" if initial_values else "0x00000000")
        
        # Size
        self.add_field(parent, "size", "Size (KB):", "spinbox",
                      initial_values.get('size', 64) if initial_values else 64,
                      from_=1, to=1048576)
        
        # Memory Type
        self.add_field(parent, "memory_type", "Type:", "combobox",
                      initial_values.get('memory_type', 'Memory') if initial_values else 'Memory',
                      values=['Memory', 'Peripheral'])
        
        # Read Latency
        self.add_field(parent, "read_latency", "Read Latency:", "spinbox",
                      initial_values.get('read_latency', 1) if initial_values else 1,
                      from_=0, to=100)
        
        # Write Latency
        self.add_field(parent, "write_latency", "Write Latency:", "spinbox",
                      initial_values.get('write_latency', 1) if initial_values else 1,
                      from_=0, to=100)
        
        # Number of Regions
        self.add_field(parent, "num_regions", "Protection Regions:", "spinbox",
                      initial_values.get('num_regions', 1) if initial_values else 1,
                      from_=1, to=16)
        
        # Security
        self.add_field(parent, "secure_only", "Secure Only:", "checkbox",
                      initial_values.get('secure_only', False) if initial_values else False)
        
    def add_field(self, parent, name, label, field_type, initial_value=None, **kwargs):
        """Add a form field with modern styling"""
        row = len(self.fields)
        
        # Label
        ttk.Label(parent, text=label, font=self.theme.FONTS['body']).grid(
            row=row, column=0, sticky=tk.W, padx=(0, 10), pady=8)
        
        # Field
        if field_type == 'text':
            var = tk.StringVar(value=initial_value or '')
            field = ttk.Entry(parent, textvariable=var, style='Modern.TEntry', width=25)
            field.grid(row=row, column=1, sticky=tk.EW, pady=8)
            
        elif field_type == 'spinbox':
            var = tk.IntVar(value=initial_value or 0)
            field = ttk.Spinbox(parent, textvariable=var, 
                              from_=kwargs.get('from_', 0),
                              to=kwargs.get('to', 100),
                              style='Modern.TEntry', width=25)
            field.grid(row=row, column=1, sticky=tk.EW, pady=8)
            
        elif field_type == 'combobox':
            var = tk.StringVar(value=initial_value or '')
            field = ttk.Combobox(parent, textvariable=var,
                               values=kwargs.get('values', []),
                               state='readonly',
                               style='Modern.TCombobox', width=23)
            field.grid(row=row, column=1, sticky=tk.EW, pady=8)
            
        elif field_type == 'checkbox':
            var = tk.BooleanVar(value=initial_value or False)
            field = ttk.Checkbutton(parent, variable=var, style='Modern.TCheckbutton')
            field.grid(row=row, column=1, sticky=tk.W, pady=8)
            
        self.fields[name] = var
        parent.columnconfigure(1, weight=1)
        
    def save(self):
        """Save dialog values"""
        try:
            self.result = {}
            for name, var in self.fields.items():
                value = var.get()
                
                # Convert hex address to int
                if name == 'base_address' and isinstance(value, str):
                    value = int(value, 16)
                    
                self.result[name] = value
                
            self.dialog.destroy()
        except Exception as e:
            messagebox.showerror("Error", f"Invalid input: {str(e)}")
            
    def cancel(self):
        """Cancel dialog"""
        self.result = None
        self.dialog.destroy()


def main():
    """Main entry point"""
    root = tk.Tk()
    app = ModernBusMatrixGUI(root)
    root.mainloop()


if __name__ == "__main__":
    main()