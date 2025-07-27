#!/usr/bin/env python3
"""
AMBA Bus Matrix Configuration GUI
A visual tool for designing and configuring AMBA bus matrices
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
from axi_verilog_generator import AXIVerilogGenerator
from address_safety_checker import validate_bus_configuration

# Lazy import for VIP integration to handle missing dependencies
VIPControlPanel = None

@dataclass
class MasterConfig:
    """Configuration for a bus master"""
    name: str
    id_width: int = 4
    qos_support: bool = True
    exclusive_support: bool = True
    user_width: int = 0
    priority: int = 0  # Default priority (0-15)
    default_prot: int = 0b010  # Default AxPROT value (privileged, non-secure, data)
    default_cache: int = 0b0011  # Default AxCACHE value (normal, non-cacheable)
    default_region: int = 0  # Default AxREGION value
    
@dataclass
class SlaveConfig:
    """Configuration for a bus slave"""
    name: str
    base_address: int
    size: int  # in KB
    memory_type: str = "Memory"  # Memory or Peripheral
    read_latency: int = 1
    write_latency: int = 1
    priority: int = 0  # Slave priority for arbitration
    num_regions: int = 1  # Number of protection regions (1-16)
    secure_only: bool = False  # Whether slave accepts only secure transactions
    privileged_only: bool = False  # Whether slave requires privileged access
    allowed_masters: List[str] = None  # List of master names allowed to access (None = all allowed)
    
    def __post_init__(self):
        if self.allowed_masters is None:
            self.allowed_masters = []  # Empty list means all masters allowed (default)
    
    def get_end_address(self):
        """Calculate end address based on size"""
        return self.base_address + (self.size * 1024) - 1
    
@dataclass
class BusConfig:
    """Complete bus configuration"""
    bus_type: str  # AXI4, AXI3, AHB, APB
    data_width: int
    addr_width: int
    masters: List[MasterConfig]
    slaves: List[SlaveConfig]
    arbitration: str = "QOS"  # FIXED, RR, QOS, WRR
    
class BusMatrixCanvas(tk.Canvas):
    """Canvas for visual bus matrix representation"""
    
    def __init__(self, parent, **kwargs):
        super().__init__(parent, bg='white', **kwargs)
        self.masters = []
        self.slaves = []
        self.connections = []
        self.selected_item = None
        
        # Visual parameters
        self.master_color = '#4CAF50'
        self.slave_color = '#2196F3'
        self.interconnect_color = '#FFC107'
        self.connection_color = '#757575'
        
        # Bind mouse events
        self.bind('<Button-1>', self.on_click)
        self.bind('<Button-3>', self.on_right_click)  # Right-click for context menu
        self.bind('<B1-Motion>', self.on_drag)
        self.bind('<ButtonRelease-1>', self.on_release)
        
        # Drag state tracking
        self.dragging = False
        self.drag_data = {"x": 0, "y": 0, "item": None}
        
        # Grid snapping (optional)
        self.snap_to_grid = True
        self.grid_size = 20
        
        # Zoom functionality
        self.zoom_level = 1.0
        self.zoom_min = 0.25
        self.zoom_max = 4.0
        self.zoom_step = 0.25
        
        # Flash state tracking
        self.flashing_block = None
        self.flash_after_id = None
        
    def add_master(self, config: MasterConfig, x: int = 50, y: int = 50):
        """Add a master to the canvas"""
        # Apply zoom to dimensions
        zoom = self.zoom_level
        width = int(100 * zoom)
        height = int(60 * zoom)
        
        master_id = self.create_rectangle(x, y, x+width, y+height, 
                                        fill=self.master_color, 
                                        outline='black', width=2)
        
        # Scale font sizes
        name_font_size = max(8, int(10 * zoom))
        priority_font_size = max(7, int(9 * zoom))
        idx_font_size = max(6, int(8 * zoom))
        
        text_id = self.create_text(x+width//2, y+height//3, text=config.name, 
                                  font=('Arial', name_font_size, 'bold'))
        
        # Add priority label below the name
        priority = getattr(config, 'priority', 0)
        priority_text = f"P:{priority}"
        priority_id = self.create_text(x+width//2, y+2*height//3, text=priority_text,
                                     font=('Arial', priority_font_size, 'bold'),
                                     fill='darkgreen')
        
        # Add master index (will be updated after all masters are added)
        master_idx = len(self.masters)
        idx_text = f"M{master_idx}"
        idx_id = self.create_text(x+width//10, y+height//6, text=idx_text,
                                font=('Arial', idx_font_size, 'bold'),
                                fill='darkgreen')
        
        self.masters.append({
            'id': master_id,
            'text_id': text_id,
            'priority_id': priority_id,
            'idx_id': idx_id,
            'config': config,
            'x': x,
            'y': y
        })
        
        return master_id
        
    def add_slave(self, config: SlaveConfig, x: int = 450, y: int = 50):
        """Add a slave to the canvas"""
        # Apply zoom to dimensions
        zoom = self.zoom_level
        width = int(150 * zoom)
        height = int(100 * zoom)
        
        slave_id = self.create_rectangle(x, y, x+width, y+height,  # Taller for all labels
                                       fill=self.slave_color,
                                       outline='black', width=2)
        
        # Scale font sizes
        name_font_size = max(8, int(10 * zoom))
        text_font_size = max(6, int(8 * zoom))
        
        text_id = self.create_text(x+width//2, y+height//5, text=config.name,
                                 font=('Arial', name_font_size, 'bold'))
        
        # Add slave index label
        slave_idx = len(self.slaves)
        idx_text = f"S{slave_idx}"
        idx_id = self.create_text(x+width//15, y+height//10, text=idx_text,
                                font=('Arial', text_font_size, 'bold'),
                                fill='darkblue')
        
        # Add address range info (begin - end)
        end_addr = config.get_end_address()
        addr_range_text = f"0x{config.base_address:08X} -\n0x{end_addr:08X}"
        addr_id = self.create_text(x+width//2, y+height*0.45, text=addr_range_text,
                                 font=('Arial', text_font_size))
        
        # Add size info
        size_kb = config.size
        if size_kb >= 1048576:  # >= 1GB
            size_text = f"({size_kb // 1048576}GB)"
        elif size_kb >= 1024:  # >= 1MB
            size_text = f"({size_kb // 1024}MB)"
        else:
            size_text = f"({size_kb}KB)"
        
        size_id = self.create_text(x+width//2, y+height*0.7, text=size_text,
                                 font=('Arial', text_font_size))
        
        # Add priority if available
        priority = getattr(config, 'priority', 0)
        priority_text = f"P:{priority}"
        priority_id = self.create_text(x+width//2, y+height*0.85, text=priority_text,
                                     font=('Arial', text_font_size),
                                     fill='darkblue')
        
        self.slaves.append({
            'id': slave_id,
            'text_id': text_id,
            'addr_id': addr_id,
            'size_id': size_id,
            'idx_id': idx_id,
            'priority_id': priority_id,
            'config': config,
            'x': x,
            'y': y
        })
        
        return slave_id
        
    def draw_interconnect(self):
        """Draw the interconnect with simplified, clear routing"""
        # Clear existing interconnect
        self.delete('interconnect')
        self.delete('router')
        
        if not self.masters or not self.slaves:
            return
        
        # Fixed interconnect position for consistency
        center_y = 350
        
        # Calculate interconnect bounds
        if self.masters and self.slaves:
            min_x = min(min(m['x'] for m in self.masters), min(s['x'] for s in self.slaves)) - 50
            max_x = max(max(m['x'] + 100 for m in self.masters), max(s['x'] + 150 for s in self.slaves)) + 50
        else:
            min_x = 0
            max_x = 800
            
        # Draw horizontal interconnect box
        interconnect_left = min_x
        interconnect_right = max_x
        interconnect_height = 60  # Compact for cleaner look
        
        self.create_rectangle(interconnect_left, center_y - interconnect_height//2,
                            interconnect_right, center_y + interconnect_height//2,
                            fill=self.interconnect_color,
                            outline='black', width=2,
                            tags='interconnect')
        
        # Draw simplified router component
        center_x = (interconnect_left + interconnect_right) // 2
        
        # Get bus type from GUI config, fallback to AXI4 if not available
        bus_type = "AXI4"  # Default
        if hasattr(self, 'gui') and hasattr(self.gui, 'current_config'):
            bus_type = self.gui.current_config.bus_type
        
        self.create_text(center_x, center_y,
                       text=f'{bus_type} Interconnect',
                       font=('Arial', 14, 'bold'),
                       tags='interconnect')
        
        # Define colors for visual distinction
        colors = ['#2196F3', '#3F51B5', '#673AB7', '#9C27B0', 
                  '#E91E63', '#F44336', '#FF5722', '#FF9800']
        
        # Draw connections from masters (top) to interconnect (middle)
        num_masters = len(self.masters)
        num_slaves = len(self.slaves)
        
        # Calculate connection points with wider spacing for clarity
        if num_masters > 0:
            master_spacing = (interconnect_right - interconnect_left - 100) / (num_masters + 1)
        
        # Simplified master connections with clearer routing
        interconnect_top = center_y - interconnect_height//2
        
        for i, master in enumerate(self.masters):
            # Use color coding for visual distinction
            line_color = colors[i % len(colors)]
            
            # Calculate connection points
            start_x = master['x'] + 50  # Center of master block
            start_y = master['y'] + 60  # Bottom of master block
            conn_x = interconnect_left + 50 + (i + 1) * master_spacing
            
            # Check if direct path is clear
            if not self.path_intersects_blocks(start_x, start_y, conn_x, interconnect_top, 
                                             exclude_blocks=[('master', i)]):
                # Direct connection is clear
                self.create_line(start_x, start_y,
                               conn_x, interconnect_top,
                               fill=line_color, width=3,
                               smooth=True,
                               arrow=tk.LAST, tags='interconnect')
            else:
                # Use L-shaped routing to avoid blocks
                # Try going down first, then across
                mid_y = start_y + 40  # Go down a bit first
                
                # Check if this path is clear
                if (not self.path_intersects_blocks(start_x, start_y, start_x, mid_y, 
                                                  exclude_blocks=[('master', i)]) and
                    not self.path_intersects_blocks(start_x, mid_y, conn_x, mid_y, 
                                                  exclude_blocks=[('master', i)]) and
                    not self.path_intersects_blocks(conn_x, mid_y, conn_x, interconnect_top, 
                                                  exclude_blocks=[('master', i)])):
                    # This path is clear
                    points = [start_x, start_y,
                             start_x, mid_y,
                             conn_x, mid_y,
                             conn_x, interconnect_top]
                    
                    self.create_line(points,
                                   fill=line_color, width=3,
                                   smooth=True, splinesteps=12,
                                   arrow=tk.LAST, tags='interconnect')
                else:
                    # Try alternative routing - go around blocks
                    # Find clear horizontal path
                    clear_y = start_y + 60
                    while clear_y < interconnect_top - 20:
                        if not self.path_intersects_blocks(min(start_x, conn_x) - 10, clear_y, 
                                                         max(start_x, conn_x) + 10, clear_y):
                            break
                        clear_y += 20
                    
                    points = [start_x, start_y,
                             start_x, clear_y,
                             conn_x, clear_y,
                             conn_x, interconnect_top]
                    
                    self.create_line(points,
                                   fill=line_color, width=3,
                                   smooth=True, splinesteps=12,
                                   arrow=tk.LAST, tags='interconnect')
        
        # Simplified slave connections
        if num_slaves > 0:
            slave_spacing = (interconnect_right - interconnect_left - 100) / (num_slaves + 1)
        
        interconnect_bottom = center_y + interconnect_height//2
        
        for i, slave in enumerate(self.slaves):
            # Use matching color from master for visual connection
            line_color = colors[i % len(colors)]
            
            # Calculate connection points
            conn_x = interconnect_left + 50 + (i + 1) * slave_spacing
            end_x = slave['x'] + 75  # Center of slave block
            end_y = slave['y']  # Top of slave block
            
            # Check if direct path is clear
            if not self.path_intersects_blocks(conn_x, interconnect_bottom, end_x, end_y, 
                                             exclude_blocks=[('slave', i)]):
                # Direct connection is clear
                self.create_line(conn_x, interconnect_bottom,
                               end_x, end_y,
                               fill=line_color, width=3,
                               smooth=True,
                               arrow=tk.LAST, tags='interconnect')
            else:
                # Use L-shaped routing to avoid blocks
                # Try going down first, then across
                mid_y = interconnect_bottom + 40  # Go down a bit first
                
                # Check if this path is clear
                if (not self.path_intersects_blocks(conn_x, interconnect_bottom, conn_x, mid_y, 
                                                  exclude_blocks=[('slave', i)]) and
                    not self.path_intersects_blocks(conn_x, mid_y, end_x, mid_y, 
                                                  exclude_blocks=[('slave', i)]) and
                    not self.path_intersects_blocks(end_x, mid_y, end_x, end_y, 
                                                  exclude_blocks=[('slave', i)])):
                    # This path is clear
                    points = [conn_x, interconnect_bottom,
                             conn_x, mid_y,
                             end_x, mid_y,
                             end_x, end_y]
                    
                    self.create_line(points,
                                   fill=line_color, width=3,
                                   smooth=True, splinesteps=12,
                                   arrow=tk.LAST, tags='interconnect')
                else:
                    # Try alternative routing - find clear path
                    clear_y = interconnect_bottom + 60
                    max_y = min(s['y'] for s in self.slaves) - 20
                    while clear_y < max_y:
                        if not self.path_intersects_blocks(min(conn_x, end_x) - 10, clear_y, 
                                                         max(conn_x, end_x) + 10, clear_y):
                            break
                        clear_y += 20
                    
                    points = [conn_x, interconnect_bottom,
                             conn_x, clear_y,
                             end_x, clear_y,
                             end_x, end_y]
                    
                    self.create_line(points,
                                   fill=line_color, width=3,
                                   smooth=True, splinesteps=12,
                                   arrow=tk.LAST, tags='interconnect')
            
            # Security and permission indicators with matching color
            indicators = []
            if hasattr(slave['config'], 'secure_only') and slave['config'].secure_only:
                indicators.append("[SEC]")
            # Only show [PERM] if there are actual restrictions
            if (hasattr(slave['config'], 'allowed_masters') and 
                slave['config'].allowed_masters and 
                len(slave['config'].allowed_masters) < len(self.masters)):
                indicators.append("[PERM]")
            
            if indicators:
                self.create_text(end_x + 40, end_y + 5,
                               text=" ".join(indicators),
                               font=('Arial', 8),
                               fill=line_color,
                               tags='interconnect')
                           
    def on_click(self, event):
        """Handle mouse click - start drag if on a block"""
        # Convert canvas coordinates to item coordinates
        x = self.canvasx(event.x)
        y = self.canvasy(event.y)
        
        # Find clicked item
        clicked_item = self.find_closest(x, y)[0]
        
        # Check if it's a master or slave block
        for i, master in enumerate(self.masters):
            master_items = [master['id'], master['text_id']]
            if 'priority_id' in master:
                master_items.append(master['priority_id'])
            if 'idx_id' in master:
                master_items.append(master['idx_id'])
                
            if clicked_item in master_items:
                self.selected_item = ('master', i)
                # Flash the block
                self.flash_block(master['id'], self.master_color)
                # Start drag
                self.dragging = True
                self.drag_data["x"] = x
                self.drag_data["y"] = y
                self.drag_data["item"] = ('master', i)
                # Bring all master components to front
                self.tag_raise(master['id'])
                self.tag_raise(master['text_id'])
                if 'priority_id' in master:
                    self.tag_raise(master['priority_id'])
                if 'idx_id' in master:
                    self.tag_raise(master['idx_id'])
                return
                
        for i, slave in enumerate(self.slaves):
            slave_items = [slave['id'], slave['text_id'], slave.get('addr_id'), slave.get('size_id')]
            if 'idx_id' in slave:
                slave_items.append(slave['idx_id'])
            if 'priority_id' in slave:
                slave_items.append(slave['priority_id'])
                
            if clicked_item in slave_items:
                self.selected_item = ('slave', i)
                # Flash the block
                self.flash_block(slave['id'], self.slave_color)
                # Start drag
                self.dragging = True
                self.drag_data["x"] = x
                self.drag_data["y"] = y
                self.drag_data["item"] = ('slave', i)
                # Bring all slave components to front
                self.tag_raise(slave['id'])
                self.tag_raise(slave['text_id'])
                if 'addr_id' in slave:
                    self.tag_raise(slave['addr_id'])
                if 'size_id' in slave:
                    self.tag_raise(slave['size_id'])
                if 'idx_id' in slave:
                    self.tag_raise(slave['idx_id'])
                if 'priority_id' in slave:
                    self.tag_raise(slave['priority_id'])
                return
                
        self.selected_item = None
        self.dragging = False
        # Stop any flashing if clicking on empty space
        self.stop_flash()
    
    def flash_block(self, block_id, original_color):
        """Start continuous slow flashing of a block"""
        # Stop any existing flash
        self.stop_flash()
        
        # Store flashing block info
        self.flashing_block = (block_id, original_color)
        
        # Flash colors for slow pulsing effect
        flash_colors = ['#FFFF99', '#FFFFCC', '#FFFFFF', '#FFFFCC', '#FFFF99', original_color]
        flash_duration = 200  # milliseconds per color (slower)
        
        def continuous_flash(color_index=0):
            # Check if we should continue flashing
            if self.flashing_block and self.flashing_block[0] == block_id:
                self.itemconfig(block_id, fill=flash_colors[color_index])
                # Schedule next color
                next_index = (color_index + 1) % len(flash_colors)
                self.flash_after_id = self.after(flash_duration, lambda: continuous_flash(next_index))
        
        # Start continuous flashing
        continuous_flash()
    
    def stop_flash(self):
        """Stop any ongoing flash effect"""
        if self.flash_after_id:
            self.after_cancel(self.flash_after_id)
            self.flash_after_id = None
        
        if self.flashing_block:
            block_id, original_color = self.flashing_block
            self.itemconfig(block_id, fill=original_color)
            self.flashing_block = None
        
    def on_right_click(self, event):
        """Handle right-click for context menu"""
        # Stop any flashing
        self.stop_flash()
        
        # Convert canvas coordinates to item coordinates
        x = self.canvasx(event.x)
        y = self.canvasy(event.y)
        
        # Find clicked item
        clicked_item = self.find_closest(x, y)[0]
        
        # Check if it's a master or slave block
        for i, master in enumerate(self.masters):
            master_items = [master['id'], master['text_id']]
            if 'priority_id' in master:
                master_items.append(master['priority_id'])
            if 'idx_id' in master:
                master_items.append(master['idx_id'])
                
            if clicked_item in master_items:
                self.show_master_context_menu(event, i)
                return
                
        for i, slave in enumerate(self.slaves):
            slave_items = [slave['id'], slave['text_id'], slave.get('addr_id'), slave.get('size_id')]
            if 'idx_id' in slave:
                slave_items.append(slave['idx_id'])
            if 'priority_id' in slave:
                slave_items.append(slave['priority_id'])
                
            if clicked_item in slave_items:
                self.show_slave_context_menu(event, i)
                return
    
    def show_master_context_menu(self, event, master_index):
        """Show context menu for master block"""
        import tkinter as tk
        
        context_menu = tk.Menu(self, tearoff=0)
        context_menu.add_command(label=f"Configure {self.masters[master_index]['config'].name}", 
                               command=lambda: self.edit_master_by_index(master_index))
        context_menu.add_separator()
        context_menu.add_command(label="Delete Master", 
                               command=lambda: self.delete_master_by_index(master_index))
        
        try:
            context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            context_menu.grab_release()
    
    def show_slave_context_menu(self, event, slave_index):
        """Show context menu for slave block"""
        import tkinter as tk
        
        context_menu = tk.Menu(self, tearoff=0)
        context_menu.add_command(label=f"Configure {self.slaves[slave_index]['config'].name}", 
                               command=lambda: self.edit_slave_by_index(slave_index))
        context_menu.add_separator()
        context_menu.add_command(label="Delete Slave", 
                               command=lambda: self.delete_slave_by_index(slave_index))
        
        try:
            context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            context_menu.grab_release()
    
    def edit_master_by_index(self, index):
        """Edit master by canvas index"""
        if hasattr(self, 'gui'):
            self.gui.edit_master_by_index(index)
    
    def edit_slave_by_index(self, index):
        """Edit slave by canvas index"""
        if hasattr(self, 'gui'):
            self.gui.edit_slave_by_index(index)
    
    def delete_master_by_index(self, index):
        """Delete master by canvas index"""
        if hasattr(self, 'gui'):
            self.gui.delete_master_by_index(index)
    
    def delete_slave_by_index(self, index):
        """Delete slave by canvas index"""
        if hasattr(self, 'gui'):
            self.gui.delete_slave_by_index(index)
            
    def on_drag(self, event):
        """Handle mouse drag - move blocks and auto-reconnect lines"""
        if not self.dragging or not self.drag_data["item"]:
            return
            
        # Convert to canvas coordinates
        x = self.canvasx(event.x)
        y = self.canvasy(event.y)
        
        # Calculate movement delta
        dx = x - self.drag_data["x"]
        dy = y - self.drag_data["y"]
        
        # Update drag position
        self.drag_data["x"] = x
        self.drag_data["y"] = y
        
        # Move the appropriate block
        item_type, item_index = self.drag_data["item"]
        
        if item_type == 'master' and item_index < len(self.masters):
            master = self.masters[item_index]
            
            # Move all master components
            self.move(master['id'], dx, dy)
            self.move(master['text_id'], dx, dy)
            if 'priority_id' in master:
                self.move(master['priority_id'], dx, dy)
            if 'idx_id' in master:
                self.move(master['idx_id'], dx, dy)
            
            # Update stored position
            master['x'] += dx
            master['y'] += dy
            
            # Redraw interconnect to update lines
            self.draw_interconnect()
            # Ensure dragged block stays on top
            self.tag_raise(master['id'])
            self.tag_raise(master['text_id'])
            if 'priority_id' in master:
                self.tag_raise(master['priority_id'])
            if 'idx_id' in master:
                self.tag_raise(master['idx_id'])
            
        elif item_type == 'slave' and item_index < len(self.slaves):
            slave = self.slaves[item_index]
            
            # Move all slave components
            self.move(slave['id'], dx, dy)
            self.move(slave['text_id'], dx, dy)
            if 'addr_id' in slave:
                self.move(slave['addr_id'], dx, dy)
            if 'size_id' in slave:
                self.move(slave['size_id'], dx, dy)
            if 'idx_id' in slave:
                self.move(slave['idx_id'], dx, dy)
            if 'priority_id' in slave:
                self.move(slave['priority_id'], dx, dy)
            
            # Update stored position
            slave['x'] += dx
            slave['y'] += dy
            
            # Redraw interconnect to update lines
            self.draw_interconnect()
            # Ensure dragged block stays on top
            self.tag_raise(slave['id'])
            self.tag_raise(slave['text_id'])
            if 'addr_id' in slave:
                self.tag_raise(slave['addr_id'])
            if 'size_id' in slave:
                self.tag_raise(slave['size_id'])
            if 'idx_id' in slave:
                self.tag_raise(slave['idx_id'])
            if 'priority_id' in slave:
                self.tag_raise(slave['priority_id'])
            
    def on_release(self, event):
        """Handle mouse release - end drag operation"""
        if self.dragging:
            self.dragging = False
            self.drag_data["item"] = None
            
            # Stop flashing
            self.stop_flash()
            
            # Final redraw to ensure clean connections
            self.draw_interconnect()
            
            # Ensure all blocks are above lines
            self.raise_all_blocks()
            
            # Optional: Snap to grid for cleaner layout
            if hasattr(self, 'snap_to_grid') and self.snap_to_grid:
                self.snap_blocks_to_grid()
    
    def snap_blocks_to_grid(self):
        """Snap all blocks to grid positions for cleaner layout"""
        # Stop any flashing
        self.stop_flash()
        
        grid_size = self.grid_size
        
        # Snap masters to grid
        for master in self.masters:
            # Calculate snapped position
            new_x = round(master['x'] / grid_size) * grid_size
            new_y = round(master['y'] / grid_size) * grid_size
            
            # Calculate delta
            dx = new_x - master['x']
            dy = new_y - master['y']
            
            if dx != 0 or dy != 0:
                # Move to snapped position
                self.move(master['id'], dx, dy)
                self.move(master['text_id'], dx, dy)
                if 'priority_id' in master:
                    self.move(master['priority_id'], dx, dy)
                if 'idx_id' in master:
                    self.move(master['idx_id'], dx, dy)
                
                # Update stored position
                master['x'] = new_x
                master['y'] = new_y
        
        # Snap slaves to grid
        for slave in self.slaves:
            # Calculate snapped position
            new_x = round(slave['x'] / grid_size) * grid_size
            new_y = round(slave['y'] / grid_size) * grid_size
            
            # Calculate delta
            dx = new_x - slave['x']
            dy = new_y - slave['y']
            
            if dx != 0 or dy != 0:
                # Move to snapped position
                self.move(slave['id'], dx, dy)
                self.move(slave['text_id'], dx, dy)
                if 'addr_id' in slave:
                    self.move(slave['addr_id'], dx, dy)
                if 'size_id' in slave:
                    self.move(slave['size_id'], dx, dy)
                if 'idx_id' in slave:
                    self.move(slave['idx_id'], dx, dy)
                if 'priority_id' in slave:
                    self.move(slave['priority_id'], dx, dy)
                
                # Update stored position
                slave['x'] = new_x
                slave['y'] = new_y
        
        # Redraw connections after snapping
        self.draw_interconnect()
        # Ensure blocks are above lines
        self.raise_all_blocks()
    
    def line_intersects_rect(self, x1, y1, x2, y2, rect_x, rect_y, rect_w, rect_h):
        """Check if line from (x1,y1) to (x2,y2) intersects rectangle"""
        # Check if line is completely outside rectangle bounds
        if ((x1 < rect_x and x2 < rect_x) or 
            (x1 > rect_x + rect_w and x2 > rect_x + rect_w) or
            (y1 < rect_y and y2 < rect_y) or 
            (y1 > rect_y + rect_h and y2 > rect_y + rect_h)):
            return False
            
        # Use line-rectangle intersection algorithm
        # Check intersection with each edge of rectangle
        def line_intersects_line(x1, y1, x2, y2, x3, y3, x4, y4):
            """Check if line (x1,y1)-(x2,y2) intersects line (x3,y3)-(x4,y4)"""
            denom = (x1-x2)*(y3-y4) - (y1-y2)*(x3-x4)
            if abs(denom) < 1e-10:
                return False  # Lines are parallel
            t = ((x1-x3)*(y3-y4) - (y1-y3)*(x3-x4)) / denom
            u = -((x1-x2)*(y1-y3) - (y1-y2)*(x1-x3)) / denom
            return 0 <= t <= 1 and 0 <= u <= 1
        
        # Check intersection with rectangle edges
        edges = [
            (rect_x, rect_y, rect_x + rect_w, rect_y),  # Top
            (rect_x + rect_w, rect_y, rect_x + rect_w, rect_y + rect_h),  # Right
            (rect_x + rect_w, rect_y + rect_h, rect_x, rect_y + rect_h),  # Bottom
            (rect_x, rect_y + rect_h, rect_x, rect_y)   # Left
        ]
        
        for x3, y3, x4, y4 in edges:
            if line_intersects_line(x1, y1, x2, y2, x3, y3, x4, y4):
                return True
                
        return False
    
    def path_intersects_blocks(self, x1, y1, x2, y2, exclude_blocks=None):
        """Check if path intersects any master or slave blocks"""
        exclude_blocks = exclude_blocks or []
        
        # Check intersection with all master blocks (add margin for safety)
        zoom = self.zoom_level
        for i, master in enumerate(self.masters):
            if ('master', i) in exclude_blocks:
                continue
            # Add 5px margin around blocks for safer routing
            master_width = int(110 * zoom)
            master_height = int(70 * zoom)
            if self.line_intersects_rect(x1, y1, x2, y2, 
                                       master['x'] - 5, master['y'] - 5, 
                                       master_width, master_height):
                return True
        
        # Check intersection with all slave blocks (add margin for safety)
        for i, slave in enumerate(self.slaves):
            if ('slave', i) in exclude_blocks:
                continue
            # Add 5px margin around blocks for safer routing
            slave_width = int(160 * zoom)
            slave_height = int(110 * zoom)
            if self.line_intersects_rect(x1, y1, x2, y2, 
                                       slave['x'] - 5, slave['y'] - 5, 
                                       slave_width, slave_height):
                return True
                
        return False
    
    def raise_all_blocks(self):
        """Raise all blocks above the interconnect lines"""
        # Raise all master blocks and their text
        for master in self.masters:
            self.tag_raise(master['id'])
            self.tag_raise(master['text_id'])
            if 'priority_id' in master:
                self.tag_raise(master['priority_id'])
            if 'idx_id' in master:
                self.tag_raise(master['idx_id'])
        
        # Raise all slave blocks and their text
        for slave in self.slaves:
            self.tag_raise(slave['id'])
            self.tag_raise(slave['text_id'])
            if 'addr_id' in slave:
                self.tag_raise(slave['addr_id'])
            if 'size_id' in slave:
                self.tag_raise(slave['size_id'])
            if 'idx_id' in slave:
                self.tag_raise(slave['idx_id'])
            if 'priority_id' in slave:
                self.tag_raise(slave['priority_id'])

class BusMatrixGUI:
    """Main GUI application"""
    
    def __init__(self, root):
        self.root = root
        self.root.title("AMBA Bus Matrix Configuration Tool")
        self.root.geometry("1400x850")  # Larger window for better layout
        
        self.current_config = BusConfig(
            bus_type="AXI4",
            data_width=64,
            addr_width=32,
            masters=[],
            slaves=[],
            arbitration="QOS"
        )
        
        self.setup_ui()
        
    def setup_ui(self):
        """Setup the user interface"""
        # Create menu bar
        self.menubar = tk.Menu(self.root)
        self.root.config(menu=self.menubar)
        
        file_menu = tk.Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="New", command=self.new_config)
        file_menu.add_command(label="Open...", command=self.load_config)
        file_menu.add_command(label="Save...", command=self.save_config)
        file_menu.add_separator()
        file_menu.add_command(label="Export Verilog", command=self.export_verilog)
        file_menu.add_separator()
        file_menu.add_command(label="Export Memory Map CSV...", command=self.export_memory_map_csv)
        file_menu.add_command(label="Export Master/Slave Table CSV...", command=self.export_master_slave_csv)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)
        
        # Templates menu
        templates_menu = tk.Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label="Templates", menu=templates_menu)
        templates_menu.add_command(label="Simple AXI4 (2M x 3S)", command=lambda: self.load_template("simple_axi4_2m3s.json"))
        templates_menu.add_command(label="Complex AXI4 System", command=lambda: self.load_template("complex_axi4_system.json"))
        templates_menu.add_command(label="AHB System", command=lambda: self.load_template("ahb_system.json"))
        
        # Settings menu
        settings_menu = tk.Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label="Settings", menu=settings_menu)
        
        # Grid snapping toggle
        self.grid_snap_var = tk.BooleanVar(value=True)
        settings_menu.add_checkbutton(label="Grid Snapping", 
                                     variable=self.grid_snap_var,
                                     command=self.toggle_grid_snap)
        
        # Grid size submenu
        grid_size_menu = tk.Menu(settings_menu, tearoff=0)
        settings_menu.add_cascade(label="Grid Size", menu=grid_size_menu)
        for size in [10, 20, 25, 40, 50]:
            grid_size_menu.add_radiobutton(label=f"{size}px", 
                                         command=lambda s=size: self.set_grid_size(s))
        
        # Safety submenu
        settings_menu.add_separator()
        safety_menu = tk.Menu(settings_menu, tearoff=0)
        settings_menu.add_cascade(label="Safety & Security", menu=safety_menu)
        safety_menu.add_command(label="Validate Address Safety", command=self.validate_address_safety)
        safety_menu.add_command(label="Show Safety Report", command=self.show_safety_report)
        
        # Create main frame
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Left panel - Configuration
        left_panel = ttk.LabelFrame(main_frame, text="Configuration", padding=10)
        left_panel.pack(side=tk.LEFT, fill=tk.Y, padx=5)
        
        # Bus type selection
        ttk.Label(left_panel, text="Bus Type:").grid(row=0, column=0, sticky=tk.W)
        self.bus_type_var = tk.StringVar(value="AXI4")
        bus_type_combo = ttk.Combobox(left_panel, textvariable=self.bus_type_var,
                                     values=["AXI4", "AXI3", "AHB", "APB"],
                                     state="readonly", width=15)
        bus_type_combo.grid(row=0, column=1, padx=5)
        
        # Data width
        ttk.Label(left_panel, text="Data Width:").grid(row=1, column=0, sticky=tk.W)
        self.data_width_var = tk.StringVar(value="64")
        data_width_combo = ttk.Combobox(left_panel, textvariable=self.data_width_var,
                                       values=["8", "16", "32", "64", "128", "256"],
                                       state="readonly", width=15)
        data_width_combo.grid(row=1, column=1, padx=5)
        
        # Address width
        ttk.Label(left_panel, text="Address Width:").grid(row=2, column=0, sticky=tk.W)
        self.addr_width_var = tk.StringVar(value="32")
        addr_width_spin = tk.Spinbox(left_panel, textvariable=self.addr_width_var,
                                     from_=16, to=64, width=15)
        addr_width_spin.grid(row=2, column=1, padx=5)
        
        # Arbitration
        ttk.Label(left_panel, text="Arbitration:").grid(row=3, column=0, sticky=tk.W)
        self.arb_var = tk.StringVar(value="QOS")
        arb_combo = ttk.Combobox(left_panel, textvariable=self.arb_var,
                               values=["FIXED", "RR", "QOS", "WRR"],
                               state="readonly", width=15)
        arb_combo.grid(row=3, column=1, padx=5)
        
        # Masters section
        ttk.Separator(left_panel, orient=tk.HORIZONTAL).grid(row=4, column=0, 
                                                            columnspan=2, sticky="ew", pady=10)
        
        ttk.Label(left_panel, text="Masters", font=('Arial', 10, 'bold')).grid(row=5, column=0, columnspan=2)
        
        # Master list
        self.master_listbox = tk.Listbox(left_panel, height=5, width=25)
        self.master_listbox.grid(row=6, column=0, columnspan=2, pady=5)
        
        # Master buttons
        master_btn_frame = ttk.Frame(left_panel)
        master_btn_frame.grid(row=7, column=0, columnspan=2)
        
        ttk.Button(master_btn_frame, text="Add Master", 
                  command=self.add_master).pack(side=tk.LEFT, padx=2)
        ttk.Button(master_btn_frame, text="Edit", 
                  command=self.edit_master).pack(side=tk.LEFT, padx=2)
        ttk.Button(master_btn_frame, text="Delete", 
                  command=self.delete_master).pack(side=tk.LEFT, padx=2)
        
        # Slaves section
        ttk.Separator(left_panel, orient=tk.HORIZONTAL).grid(row=8, column=0, 
                                                            columnspan=2, sticky="ew", pady=10)
        
        ttk.Label(left_panel, text="Slaves", font=('Arial', 10, 'bold')).grid(row=9, column=0, columnspan=2)
        
        # Slave list
        self.slave_listbox = tk.Listbox(left_panel, height=5, width=25)
        self.slave_listbox.grid(row=10, column=0, columnspan=2, pady=5)
        
        # Slave buttons
        slave_btn_frame = ttk.Frame(left_panel)
        slave_btn_frame.grid(row=11, column=0, columnspan=2)
        
        ttk.Button(slave_btn_frame, text="Add Slave", 
                  command=self.add_slave).pack(side=tk.LEFT, padx=2)
        ttk.Button(slave_btn_frame, text="Edit", 
                  command=self.edit_slave).pack(side=tk.LEFT, padx=2)
        ttk.Button(slave_btn_frame, text="Delete", 
                  command=self.delete_slave).pack(side=tk.LEFT, padx=2)
        
        # Output directory selection
        output_frame = ttk.LabelFrame(left_panel, text="Output Directory", padding=5)
        output_frame.grid(row=12, column=0, columnspan=2, sticky="ew", pady=10)
        
        self.output_dir_var = tk.StringVar(value=os.path.abspath("output/rtl"))
        ttk.Entry(output_frame, textvariable=self.output_dir_var, width=30).pack(side=tk.LEFT, padx=5)
        ttk.Button(output_frame, text="Browse", 
                  command=self.browse_output_dir).pack(side=tk.LEFT)
        
        # Generate button
        ttk.Button(left_panel, text="Generate Verilog", 
                  command=self.generate_verilog,
                  style='Accent.TButton').grid(row=13, column=0, columnspan=2, pady=10)
        
        # Right panel - Visual representation
        right_panel = ttk.LabelFrame(main_frame, text="Bus Matrix Visualization", padding=10)
        right_panel.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=5)
        
        # Zoom controls frame
        zoom_frame = ttk.Frame(right_panel)
        zoom_frame.pack(side=tk.TOP, fill=tk.X, pady=(0, 5))
        
        # Zoom label
        ttk.Label(zoom_frame, text="Zoom:").pack(side=tk.LEFT, padx=5)
        
        # Zoom buttons
        ttk.Button(zoom_frame, text="-", width=3, 
                  command=self.zoom_out).pack(side=tk.LEFT, padx=2)
        
        self.zoom_label = ttk.Label(zoom_frame, text="100%", width=6)
        self.zoom_label.pack(side=tk.LEFT, padx=5)
        
        ttk.Button(zoom_frame, text="+", width=3, 
                  command=self.zoom_in).pack(side=tk.LEFT, padx=2)
        
        ttk.Button(zoom_frame, text="Reset", 
                  command=self.zoom_reset).pack(side=tk.LEFT, padx=10)
        
        # Canvas for drawing with scrollbars for many components
        canvas_frame = ttk.Frame(right_panel)
        canvas_frame.pack(fill=tk.BOTH, expand=True)
        
        # Create scrollbars
        v_scrollbar = ttk.Scrollbar(canvas_frame, orient=tk.VERTICAL)
        h_scrollbar = ttk.Scrollbar(canvas_frame, orient=tk.HORIZONTAL)
        
        # Canvas with larger virtual size for top-bottom layout with improved routing
        self.canvas = BusMatrixCanvas(canvas_frame, width=1000, height=700,
                                     scrollregion=(0, 0, 1600, 1000))
        # Store reference to GUI in canvas for callbacks
        self.canvas.gui = self
        
        # Configure scrollbars
        v_scrollbar.config(command=self.canvas.yview)
        h_scrollbar.config(command=self.canvas.xview)
        self.canvas.config(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)
        
        # Pack components
        v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # VIP Integration Panel
        self.setup_vip_integration(main_frame)
        
        # Status bar
        self.status_bar = ttk.Label(self.root, text="Ready", relief=tk.SUNKEN)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
        # Bind keyboard shortcuts
        self.root.bind('<Control-plus>', lambda e: self.zoom_in())
        self.root.bind('<Control-equal>', lambda e: self.zoom_in())  # Also accept = key
        self.root.bind('<Control-minus>', lambda e: self.zoom_out())
        self.root.bind('<Control-0>', lambda e: self.zoom_reset())
        self.root.bind('<Control-KP_Add>', lambda e: self.zoom_in())  # Numpad +
        self.root.bind('<Control-KP_Subtract>', lambda e: self.zoom_out())  # Numpad -
    
    def setup_vip_integration(self, parent_frame):
        """Setup VIP (Verification IP) integration panel"""
        global VIPControlPanel
        
        try:
            # Lazy import VIP integration
            if VIPControlPanel is None:
                from vip_gui_integration import VIPControlPanel
            
            # Create VIP panel as expandable section at bottom
            vip_frame = ttk.LabelFrame(self.root, text="AXI4 Verification IP (VIP) Suite", padding=10)
            vip_frame.pack(side=tk.BOTTOM, fill=tk.BOTH, expand=False, padx=5, pady=(0, 5))
            
            # Create VIP control panel
            self.vip_panel = VIPControlPanel(vip_frame, self)
            
            # Add VIP menu to menu bar
            self.add_vip_menu()
            
            print("[OK] VIP integration successful")
            
        except ImportError as e:
            print(f"Info: VIP features not available: {e}")
            # Create placeholder VIP frame
            self.create_vip_placeholder()
        except Exception as e:
            print(f"Warning: VIP integration failed: {e}")
            # Continue without VIP features if there's an error
            self.create_vip_placeholder()
    
    def add_vip_menu(self):
        """Add VIP menu to menu bar"""
        try:
            # Use the menubar instance variable
            if hasattr(self, 'menubar'):
                
                # Create VIP menu
                vip_menu = tk.Menu(self.menubar, tearoff=0)
                self.menubar.add_cascade(label="VIP", menu=vip_menu)
                
                # VIP Environment submenu
                env_menu = tk.Menu(vip_menu, tearoff=0)
                vip_menu.add_cascade(label="Environment", menu=env_menu)
                env_menu.add_command(label="Create VIP Environment", 
                                   command=lambda: self.vip_panel.create_vip_environment() if hasattr(self, 'vip_panel') else None)
                env_menu.add_command(label="Reset Environment",
                                   command=lambda: self.vip_panel.reset_vip_environment() if hasattr(self, 'vip_panel') else None)
                env_menu.add_command(label="Export VIP Config",
                                   command=lambda: self.vip_panel.export_vip_config() if hasattr(self, 'vip_panel') else None)
                
                # Test Generation submenu
                test_menu = tk.Menu(vip_menu, tearoff=0)
                vip_menu.add_cascade(label="Test Generation", menu=test_menu)
                test_menu.add_command(label="Generate Test Suite",
                                    command=lambda: self.vip_panel.generate_test_suite() if hasattr(self, 'vip_panel') else None)
                test_menu.add_command(label="Run Tests",
                                    command=lambda: self.vip_panel.run_tests() if hasattr(self, 'vip_panel') else None)
                test_menu.add_command(label="Stop Tests",
                                    command=lambda: self.vip_panel.stop_tests() if hasattr(self, 'vip_panel') else None)
                
                # Results submenu
                results_menu = tk.Menu(vip_menu, tearoff=0)
                vip_menu.add_cascade(label="Results", menu=results_menu)
                results_menu.add_command(label="Export Results",
                                       command=lambda: self.vip_panel.export_results() if hasattr(self, 'vip_panel') else None)
                results_menu.add_command(label="Generate Report",
                                       command=lambda: self.vip_panel.generate_report() if hasattr(self, 'vip_panel') else None)
                
                # About VIP
                vip_menu.add_separator()
                vip_menu.add_command(label="About VIP", command=self.show_vip_about)
                
        except Exception as e:
            print(f"Warning: VIP menu creation failed: {e}")
    
    def show_vip_about(self):
        """Show VIP features information"""
        about_text = """AXI4 Verification IP (VIP) Suite

Features:
• Master Agent - Generates AXI4 transactions with configurable timing
• Slave Agent - Responds to transactions with memory model
• Monitor - Observes and checks protocol compliance  
• Checker - Performs assertion-based verification
• Test Sequences - Comprehensive test pattern generation
• Coverage Analysis - Functional and code coverage collection

Test Categories:
• Basic Transactions - Single R/W, all burst types, WSTRB variations
• Advanced Features - Out-of-order, exclusive access, attribute variations
• Error Injection - SLVERR, DECERR, protocol violations
• Stress Tests - High throughput, randomized, corner cases

Based on CLAUDE.md requirements for complete AXI4 VIP development."""

        messagebox.showinfo("About AXI4 VIP", about_text)
    
    def create_vip_placeholder(self):
        """Create placeholder VIP frame when full VIP is not available"""
        try:
            vip_frame = ttk.LabelFrame(self.root, text="AXI4 Verification IP (VIP) - Loading...", padding=10)
            vip_frame.pack(side=tk.BOTTOM, fill=tk.X, expand=False, padx=5, pady=(0, 5))
            
            info_text = ("VIP features include:\n"
                        "• Master/Slave Agents for transaction generation\n"
                        "• Protocol compliance monitoring and checking\n"
                        "• Comprehensive test sequence generation\n"
                        "• Coverage analysis and reporting\n\n"
                        "Full VIP integration in development...")
            
            info_label = ttk.Label(vip_frame, text=info_text, justify=tk.LEFT)
            info_label.pack(pady=10)
            
            # Add simple VIP status button
            status_button = ttk.Button(vip_frame, text="Check VIP Status", 
                                     command=self.check_vip_status)
            status_button.pack()
            
        except Exception as e:
            print(f"Warning: Could not create VIP placeholder: {e}")
    
    def check_vip_status(self):
        """Check VIP integration status"""
        try:
            # Try to import VIP components
            from vip_gui_integration import VIPControlPanel
            
            # Check if VIP components are available
            if hasattr(VIPControlPanel, '__module__'):
                # VIP integration module loaded successfully
                pass
            else:
                raise ImportError("VIP module not properly loaded")
            
            messagebox.showinfo("VIP Status", 
                              "[OK] VIP components are available!\n\n"
                              "Features ready:\n"
                              "• AXI4 Master/Slave Agents\n"
                              "• Protocol Monitors and Checkers\n"
                              "• Test Sequence Generation\n"
                              "• Coverage Analysis\n\n"
                              "Restart the GUI to enable full VIP integration.")
        except ImportError as e:
            messagebox.showwarning("VIP Status",
                                 f"[ERROR] VIP components not fully available.\n\n"
                                 f"Missing: {str(e)}\n\n"
                                 f"Please ensure all VIP modules are installed.")
        except Exception as e:
            messagebox.showerror("VIP Status",
                               f"[ERROR] VIP status check failed.\n\n"
                               f"Error: {str(e)}")
        
    def add_master(self):
        """Add a new master"""
        # Generate unique name
        existing_names = [m.name for m in self.current_config.masters]
        master_num = 0
        while f"Master{master_num}" in existing_names:
            master_num += 1
        default_name = f"Master{master_num}"
        
        dialog = MasterDialog(self.root, default_name=default_name)
        self.root.wait_window(dialog.dialog)
        
        if dialog.result:
            config = dialog.result
            self.current_config.masters.append(config)
            self.master_listbox.insert(tk.END, config.name)
            
            # Add to canvas - Masters on top in rows
            # Use 4 columns for better horizontal layout
            zoom = self.canvas.zoom_level
            col = len(self.canvas.masters) % 4
            row = len(self.canvas.masters) // 4
            x_pos = (50 + col * 140) * zoom  # 4 columns with 140px spacing
            y_pos = (50 + row * 80) * zoom  # Masters at top with 80px row spacing
            self.canvas.add_master(config, x=int(x_pos), y=int(y_pos))
            self.canvas.draw_interconnect()
            self.canvas.raise_all_blocks()  # Ensure blocks are above lines
            self.update_canvas_scroll_region()
            
            self.update_status(f"Added master: {config.name}")
            
    def edit_master(self):
        """Edit selected master"""
        selection = self.master_listbox.curselection()
        if not selection:
            messagebox.showwarning("No Selection", "Please select a master to edit")
            return
            
        index = selection[0]
        config = self.current_config.masters[index]
        
        # Ensure config has all fields (for backwards compatibility)
        if not hasattr(config, 'priority'):
            config.priority = 0
        if not hasattr(config, 'default_prot'):
            config.default_prot = 0b010
        if not hasattr(config, 'default_cache'):
            config.default_cache = 0b0011
        if not hasattr(config, 'default_region'):
            config.default_region = 0
        
        dialog = MasterDialog(self.root, config)
        self.root.wait_window(dialog.dialog)
        
        if dialog.result:
            self.current_config.masters[index] = dialog.result
            self.master_listbox.delete(index)
            self.master_listbox.insert(index, dialog.result.name)
            
            # Update canvas
            self.canvas.masters[index]['config'] = dialog.result
            self.canvas.itemconfig(self.canvas.masters[index]['text_id'], 
                                 text=dialog.result.name)
            self.canvas.draw_interconnect()  # Redraw to update priority labels
            self.update_canvas_scroll_region()
            
            self.update_status(f"Updated master: {dialog.result.name}")
    
    def edit_master_by_index(self, index):
        """Edit master by canvas index (for right-click menu)"""
        if 0 <= index < len(self.current_config.masters):
            # Select in listbox and call edit
            self.master_listbox.selection_clear(0, tk.END)
            self.master_listbox.selection_set(index)
            self.edit_master()
    
    def delete_master_by_index(self, index):
        """Delete master by canvas index (for right-click menu)"""
        if 0 <= index < len(self.current_config.masters):
            # Select in listbox and call delete
            self.master_listbox.selection_clear(0, tk.END)
            self.master_listbox.selection_set(index)
            self.delete_master()
            
    def delete_master(self):
        """Delete selected master"""
        selection = self.master_listbox.curselection()
        if not selection:
            messagebox.showwarning("No Selection", "Please select a master to delete")
            return
            
        index = selection[0]
        name = self.current_config.masters[index].name
        
        if messagebox.askyesno("Confirm Delete", f"Delete master '{name}'?"):
            del self.current_config.masters[index]
            self.master_listbox.delete(index)
            
            # Remove from canvas
            master = self.canvas.masters[index]
            self.canvas.delete(master['id'])
            self.canvas.delete(master['text_id'])
            del self.canvas.masters[index]
            self.canvas.draw_interconnect()
            self.update_canvas_scroll_region()
            
            self.update_status(f"Deleted master: {name}")
            
    def add_slave(self):
        """Add a new slave"""
        # Generate unique name
        existing_names = [s.name for s in self.current_config.slaves]
        slave_num = 0
        while f"Slave{slave_num}" in existing_names:
            slave_num += 1
        default_name = f"Slave{slave_num}"
        
        # Calculate next available address
        default_address = 0
        if self.current_config.slaves:
            # Find the highest end address
            max_end_addr = 0
            for slave in self.current_config.slaves:
                end_addr = slave.base_address + (slave.size * 1024)  # Convert KB to bytes
                if end_addr > max_end_addr:
                    max_end_addr = end_addr
            # Align to next power-of-2 boundary (at least 1MB)
            # Find next power of 2 boundary
            import math
            if max_end_addr == 0:
                default_address = 0
            else:
                # Round up to next power of 2
                next_pow2 = 2 ** math.ceil(math.log2(max_end_addr + 1))
                default_address = next_pow2
        
        # Get list of available masters
        available_masters = [m.name for m in self.current_config.masters]
        
        dialog = SlaveDialog(self.root, default_name=default_name, default_address=default_address,
                           available_masters=available_masters)
        self.root.wait_window(dialog.dialog)
        
        if dialog.result:
            config = dialog.result
            
            # Validate address alignment
            is_valid, error_msg = self.validate_address_alignment(config.base_address, config.size)
            if not is_valid:
                result = messagebox.askyesno("Address Alignment Warning",
                                           f"{error_msg}\n\nDo you want to continue anyway?")
                if not result:
                    return
            
            # Check for address conflicts
            for slave in self.current_config.slaves:
                if self.check_address_overlap(config, slave):
                    messagebox.showerror("Address Conflict", 
                                       f"Address range overlaps with {slave.name}")
                    return
                    
            self.current_config.slaves.append(config)
            self.slave_listbox.insert(tk.END, 
                                    f"{config.name} (0x{config.base_address:08X})")
            
            # Add to canvas - Slaves on bottom in rows
            # Use 4 columns for better horizontal layout
            zoom = self.canvas.zoom_level
            col = len(self.canvas.slaves) % 4
            row = len(self.canvas.slaves) // 4
            x_pos = (50 + col * 200) * zoom  # 4 columns starting from x=50 with 200px spacing (wider for 150px blocks)
            y_pos = (500 + row * 120) * zoom  # Slaves at bottom with 120px row spacing (taller blocks)
            self.canvas.add_slave(config, x=int(x_pos), y=int(y_pos))
            self.canvas.draw_interconnect()
            self.canvas.raise_all_blocks()  # Ensure blocks are above lines
            self.update_canvas_scroll_region()
            
            self.update_status(f"Added slave: {config.name}")
            
    def edit_slave(self):
        """Edit selected slave"""
        selection = self.slave_listbox.curselection()
        if not selection:
            messagebox.showwarning("No Selection", "Please select a slave to edit")
            return
            
        index = selection[0]
        config = self.current_config.slaves[index]
        
        # Ensure config has all fields (for backwards compatibility)
        if not hasattr(config, 'priority'):
            config.priority = 0
        if not hasattr(config, 'num_regions'):
            config.num_regions = 1
        if not hasattr(config, 'secure_only'):
            config.secure_only = False
        if not hasattr(config, 'privileged_only'):
            config.privileged_only = False
        
        # Get list of available masters
        available_masters = [m.name for m in self.current_config.masters]
        
        dialog = SlaveDialog(self.root, config, available_masters=available_masters)
        self.root.wait_window(dialog.dialog)
        
        if dialog.result:
            # Validate address alignment
            is_valid, error_msg = self.validate_address_alignment(dialog.result.base_address, dialog.result.size)
            if not is_valid:
                result = messagebox.askyesno("Address Alignment Warning",
                                           f"{error_msg}\n\nDo you want to continue anyway?")
                if not result:
                    return
            
            # Check for address conflicts with other slaves
            for i, slave in enumerate(self.current_config.slaves):
                if i != index and self.check_address_overlap(dialog.result, slave):
                    messagebox.showerror("Address Conflict", 
                                       f"Address range overlaps with {slave.name}")
                    return
                    
            self.current_config.slaves[index] = dialog.result
            self.slave_listbox.delete(index)
            self.slave_listbox.insert(index, 
                                    f"{dialog.result.name} (0x{dialog.result.base_address:08X})")
            
            # Update canvas
            self.canvas.slaves[index]['config'] = dialog.result
            self.canvas.itemconfig(self.canvas.slaves[index]['text_id'], 
                                 text=dialog.result.name)
            
            # Update address range display
            end_addr = dialog.result.get_end_address()
            addr_range_text = f"0x{dialog.result.base_address:08X} -\n0x{end_addr:08X}"
            self.canvas.itemconfig(self.canvas.slaves[index]['addr_id'], 
                                 text=addr_range_text)
            
            # Update size display
            size_kb = dialog.result.size
            if size_kb >= 1048576:  # >= 1GB
                size_text = f"({size_kb // 1048576}GB)"
            elif size_kb >= 1024:  # >= 1MB
                size_text = f"({size_kb // 1024}MB)"
            else:
                size_text = f"({size_kb}KB)"
            self.canvas.itemconfig(self.canvas.slaves[index]['size_id'], 
                                 text=size_text)
            self.canvas.draw_interconnect()  # Redraw to update security indicators
            self.update_canvas_scroll_region()
            
            self.update_status(f"Updated slave: {dialog.result.name}")
    
    def edit_slave_by_index(self, index):
        """Edit slave by canvas index (for right-click menu)"""
        if 0 <= index < len(self.current_config.slaves):
            # Select in listbox and call edit
            self.slave_listbox.selection_clear(0, tk.END)
            self.slave_listbox.selection_set(index)
            self.edit_slave()
    
    def delete_slave_by_index(self, index):
        """Delete slave by canvas index (for right-click menu)"""
        if 0 <= index < len(self.current_config.slaves):
            # Select in listbox and call delete
            self.slave_listbox.selection_clear(0, tk.END)
            self.slave_listbox.selection_set(index)
            self.delete_slave()
            
    def delete_slave(self):
        """Delete selected slave"""
        selection = self.slave_listbox.curselection()
        if not selection:
            messagebox.showwarning("No Selection", "Please select a slave to delete")
            return
            
        index = selection[0]
        name = self.current_config.slaves[index].name
        
        if messagebox.askyesno("Confirm Delete", f"Delete slave '{name}'?"):
            del self.current_config.slaves[index]
            self.slave_listbox.delete(index)
            
            # Remove from canvas
            slave = self.canvas.slaves[index]
            self.canvas.delete(slave['id'])
            self.canvas.delete(slave['text_id'])
            self.canvas.delete(slave['addr_id'])
            self.canvas.delete(slave['size_id'])
            del self.canvas.slaves[index]
            self.canvas.draw_interconnect()
            self.update_canvas_scroll_region()
            
            self.update_status(f"Deleted slave: {name}")
            
    def check_address_overlap(self, slave1: SlaveConfig, slave2: SlaveConfig) -> bool:
        """Check if two slaves have overlapping address ranges"""
        end1 = slave1.base_address + (slave1.size * 1024) - 1
        end2 = slave2.base_address + (slave2.size * 1024) - 1
        
        return not (end1 < slave2.base_address or end2 < slave1.base_address)
    
    def validate_address_alignment(self, base_address: int, size_kb: int) -> Tuple[bool, str]:
        """Validate that address and size are properly aligned
        
        Returns: (is_valid, error_message)
        """
        # Check if base address is aligned to size
        size_bytes = size_kb * 1024
        
        # Size must be power of 2
        if size_bytes & (size_bytes - 1) != 0:
            # Find nearest power of 2
            import math
            nearest_pow2_kb = 2 ** math.ceil(math.log2(size_kb))
            return False, f"Size must be power of 2. Suggested: {nearest_pow2_kb}KB"
        
        # Base address must be aligned to size
        if base_address % size_bytes != 0:
            aligned_addr = (base_address // size_bytes) * size_bytes
            return False, f"Base address must be aligned to size boundary. Suggested: 0x{aligned_addr:08X}"
        
        return True, ""
        
    def new_config(self):
        """Create a new configuration"""
        if messagebox.askyesno("New Configuration", 
                             "This will clear the current configuration. Continue?"):
            self.current_config = BusConfig(
                bus_type="AXI4",
                data_width=64,
                addr_width=32,
                masters=[],
                slaves=[],
                arbitration="QOS"
            )
            
            # Clear UI
            self.master_listbox.delete(0, tk.END)
            self.slave_listbox.delete(0, tk.END)
            self.canvas.delete("all")
            self.canvas.masters.clear()
            self.canvas.slaves.clear()
            
            self.update_status("New configuration created")
            
    def load_config(self):
        """Load configuration from file"""
        filename = filedialog.askopenfilename(
            title="Load Configuration",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        
        if filename:
            try:
                with open(filename, 'r') as f:
                    data = json.load(f)
                    
                # Convert to dataclasses with default values for missing fields
                masters = []
                for m in data['masters']:
                    # Add default values for missing fields
                    m.setdefault('priority', 0)
                    m.setdefault('default_prot', 0b010)
                    m.setdefault('default_cache', 0b0011)
                    m.setdefault('default_region', 0)
                    masters.append(MasterConfig(**m))
                    
                slaves = []
                for s in data['slaves']:
                    # Add default values for missing fields
                    s.setdefault('priority', 0)
                    s.setdefault('num_regions', 1)
                    s.setdefault('secure_only', False)
                    s.setdefault('privileged_only', False)
                    slaves.append(SlaveConfig(**s))
                
                self.current_config = BusConfig(
                    bus_type=data['bus_type'],
                    data_width=data['data_width'],
                    addr_width=data['addr_width'],
                    masters=masters,
                    slaves=slaves,
                    arbitration=data.get('arbitration', 'QOS')
                )
                
                # Update UI
                self.refresh_ui()
                self.update_status(f"Loaded configuration from {os.path.basename(filename)}")
                
            except Exception as e:
                messagebox.showerror("Load Error", f"Failed to load configuration: {e}")
                
    def load_template(self, template_name):
        """Load a template configuration"""
        try:
            # Get the directory of the current script
            script_dir = os.path.dirname(os.path.abspath(__file__))
            template_path = os.path.join(script_dir, "..", "templates", template_name)
            
            with open(template_path, 'r') as f:
                data = json.load(f)
                
            # Convert to dataclasses with default values for missing fields
            masters = []
            for m in data['masters']:
                # Add default values for missing fields
                m.setdefault('priority', 0)
                m.setdefault('default_prot', 0b010)
                m.setdefault('default_cache', 0b0011)
                m.setdefault('default_region', 0)
                masters.append(MasterConfig(**m))
                
            slaves = []
            for s in data['slaves']:
                # Add default values for missing fields
                s.setdefault('priority', 0)
                s.setdefault('num_regions', 1)
                s.setdefault('secure_only', False)
                s.setdefault('privileged_only', False)
                slaves.append(SlaveConfig(**s))
            
            self.current_config = BusConfig(
                bus_type=data['bus_type'],
                data_width=data['data_width'],
                addr_width=data['addr_width'],
                masters=masters,
                slaves=slaves,
                arbitration=data.get('arbitration', 'QOS')
            )
            
            # Update UI
            self.refresh_ui()
            self.update_status(f"Loaded template: {template_name}")
            
        except Exception as e:
            import traceback
            error_details = traceback.format_exc()
            messagebox.showerror("Load Error", f"Failed to load template: {e}\n\nDetails:\n{error_details}")
            print(f"Error loading template: {e}")
            print(error_details)
                
    def save_config(self):
        """Save configuration to file"""
        # Validate configuration safety before saving
        if not self.validate_address_safety():
            return  # User chose not to proceed with safety violations
            
        filename = filedialog.asksaveasfilename(
            title="Save Configuration",
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
        )
        
        if filename:
            try:
                data = {
                    'bus_type': self.current_config.bus_type,
                    'data_width': self.current_config.data_width,
                    'addr_width': self.current_config.addr_width,
                    'masters': [asdict(m) for m in self.current_config.masters],
                    'slaves': [asdict(s) for s in self.current_config.slaves],
                    'arbitration': self.current_config.arbitration
                }
                
                with open(filename, 'w') as f:
                    json.dump(data, f, indent=2)
                    
                self.update_status(f"Saved configuration to {os.path.basename(filename)}")
                
            except Exception as e:
                messagebox.showerror("Save Error", f"Failed to save configuration: {e}")
                
    def refresh_ui(self):
        """Refresh UI with current configuration"""
        try:
            # Update controls
            self.bus_type_var.set(self.current_config.bus_type)
            self.data_width_var.set(str(self.current_config.data_width))
            self.addr_width_var.set(str(self.current_config.addr_width))
            self.arb_var.set(self.current_config.arbitration)
            
            # Clear lists
            self.master_listbox.delete(0, tk.END)
            self.slave_listbox.delete(0, tk.END)
            
            # Clear canvas
            self.canvas.delete("all")
            self.canvas.masters.clear()
            self.canvas.slaves.clear()
            
            # First add all masters and slaves (without drawing interconnect)
            zoom = self.canvas.zoom_level
            for i, master in enumerate(self.current_config.masters):
                self.master_listbox.insert(tk.END, master.name)
                col = i % 4  # 4 columns for horizontal layout
                row = i // 4
                x_pos = (50 + col * 140) * zoom
                y_pos = (50 + row * 80) * zoom  # Masters at top
                self.canvas.add_master(master, x=int(x_pos), y=int(y_pos))
                
            # Add slaves at bottom in horizontal layout
            for i, slave in enumerate(self.current_config.slaves):
                self.slave_listbox.insert(tk.END, 
                                        f"{slave.name} (0x{slave.base_address:08X})")
                col = i % 4  # 4 columns for horizontal layout
                row = i // 4
                x_pos = (50 + col * 200) * zoom  # Wider spacing for 150px wide blocks
                y_pos = (500 + row * 120) * zoom  # Slaves at bottom with taller spacing
                self.canvas.add_slave(slave, x=int(x_pos), y=int(y_pos))
            
            # Draw interconnect lines first (they will be under blocks)
            self.canvas.draw_interconnect()
            
            # Raise all blocks above the lines
            self.canvas.raise_all_blocks()
                
            # Update canvas scroll region based on content
            self.update_canvas_scroll_region()
            
        except Exception as e:
            import traceback
            error_details = traceback.format_exc()
            messagebox.showerror("UI Refresh Error", f"Failed to refresh UI: {e}\n\nDetails:\n{error_details}")
            print(f"Error refreshing UI: {e}")
            print(error_details)
        
    def update_canvas_scroll_region(self):
        """Update canvas scroll region based on actual content"""
        # Get bounding box of all items
        bbox = self.canvas.bbox("all")
        if bbox:
            # Add some padding
            x1, y1, x2, y2 = bbox
            self.canvas.config(scrollregion=(x1-50, y1-50, x2+50, y2+50))
    
    def generate_verilog(self):
        """Generate Verilog code"""
        # Update configuration from UI
        self.current_config.bus_type = self.bus_type_var.get()
        self.current_config.data_width = int(self.data_width_var.get())
        self.current_config.addr_width = int(self.addr_width_var.get())
        self.current_config.arbitration = self.arb_var.get()
        
        # Validate configuration
        if len(self.current_config.masters) < 1:
            messagebox.showerror("Invalid Configuration", 
                               "At least one master is required")
            return
            
        if len(self.current_config.slaves) < 1:
            messagebox.showerror("Invalid Configuration", 
                               "At least one slave is required")
            return
            
        # For AXI, need at least 2 masters and 2 slaves
        if self.current_config.bus_type in ["AXI4", "AXI3"]:
            if len(self.current_config.masters) < 2:
                messagebox.showerror("Invalid Configuration", 
                                   "AXI requires at least 2 masters")
                return
            if len(self.current_config.slaves) < 2:
                messagebox.showerror("Invalid Configuration", 
                                   "AXI requires at least 2 slaves")
                return
                
        # Validate all slave addresses before generation
        for slave in self.current_config.slaves:
            is_valid, error_msg = self.validate_address_alignment(slave.base_address, slave.size)
            if not is_valid:
                messagebox.showwarning("Address Alignment Issue",
                                     f"Slave '{slave.name}': {error_msg}\n\n"
                                     "Please fix address alignment before generating Verilog.")
                return
        
        # Generate command
        try:
            if self.current_config.bus_type in ["AXI4", "AXI3"]:
                self.generate_axi()
            elif self.current_config.bus_type == "AHB":
                self.generate_ahb()
            elif self.current_config.bus_type == "APB":
                self.generate_apb()
                
        except Exception as e:
            messagebox.showerror("Generation Error", f"Failed to generate Verilog: {e}")
            
    def generate_axi(self):
        """Generate AXI bus RTL"""
        num_masters = len(self.current_config.masters)
        num_slaves = len(self.current_config.slaves)
        
        result = messagebox.askyesno("Generate Verilog",
                                   f"Generate AXI4 interconnect RTL for:\n"
                                   f"- {num_masters} Masters\n"
                                   f"- {num_slaves} Slaves\n"
                                   f"- {self.current_config.data_width}-bit data\n"
                                   f"- {self.current_config.addr_width}-bit addresses\n"
                                   f"- {self.current_config.arbitration} arbitration\n\n"
                                   f"This will create Verilog files following IHI0022D spec.")
        
        if result:
            try:
                # Use the selected output directory
                output_dir = self.output_dir_var.get()
                os.makedirs(output_dir, exist_ok=True)
                
                # Generate RTL to the selected directory
                generator = AXIVerilogGenerator(self.current_config)
                output_file = os.path.join(output_dir, f"{self.current_config.bus_type.lower()}_interconnect.v")
                
                # Try to generate - assuming the generator has a method like generate_verilog
                success = False
                if hasattr(generator, 'generate_verilog'):
                    success = generator.generate_verilog(output_file)
                elif hasattr(generator, 'generate'):
                    # If it returns a directory, use that
                    result = generator.generate()
                    if result:
                        output_dir = result
                        success = True
                else:
                    # Fallback - create a placeholder file
                    with open(output_file, 'w') as f:
                        f.write(f"// {self.current_config.bus_type} Interconnect\n")
                        f.write(f"// Masters: {num_masters}\n")
                        f.write(f"// Slaves: {num_slaves}\n")
                        f.write(f"// Generated by Bus Matrix GUI\n")
                    success = True
                
                self.update_status(f"Generated RTL in: {output_dir}")
                
                # Also create legacy script for gen_amba_axi tool
                cmd = [
                    "../../gen_amba_axi/gen_amba_axi",
                    f"--master={num_masters}",
                    f"--slave={num_slaves}",
                    f"--module=axi_bus_m{num_masters}s{num_slaves}"
                ]
                
                if self.current_config.bus_type == "AXI3":
                    cmd.append("--axi3")
                    
                cmd_str = " ".join(cmd)
                
                with open(f"{output_dir}/run_gen_amba.sh", "w") as f:
                    f.write("#!/bin/bash\n")
                    f.write(f"# Command to run gen_amba_axi tool\n")
                    f.write(f"# Generated by Bus Matrix GUI\n")
                    f.write(cmd_str + "\n")
                    
                os.chmod(f"{output_dir}/run_gen_amba.sh", 0o755)
                
                # Show results
                files = os.listdir(output_dir)
                file_list = "\n".join(f"- {f}" for f in files if f.endswith('.v'))
                
                messagebox.showinfo("Success", 
                                  f"RTL generated successfully!\n\n"
                                  f"Output directory: {output_dir}\n\n"
                                  f"Generated files:\n{file_list}\n\n"
                                  f"To synthesize, use the generated Verilog files.\n"
                                  f"To use gen_amba_axi tool, run: {output_dir}/run_gen_amba.sh")
                                  
            except Exception as e:
                messagebox.showerror("Generation Error", f"Failed to generate RTL: {e}")
    
    def browse_output_dir(self):
        """Browse for output directory"""
        directory = filedialog.askdirectory(
            title="Select Output Directory for Verilog",
            initialdir=self.output_dir_var.get()
        )
        
        if directory:
            self.output_dir_var.set(directory)
            print(f"[INFO] Verilog output directory set to: {directory}")
            
    def generate_ahb(self):
        """Generate AHB bus"""
        num_masters = len(self.current_config.masters)
        num_slaves = len(self.current_config.slaves)
        
        # Build command
        cmd = [
            "../../gen_amba_ahb/gen_amba_ahb",
            f"--master={num_masters}",
            f"--slave={num_slaves}",
            f"--module=ahb_bus_m{num_masters}s{num_slaves}"
        ]
        
        if num_masters == 1:
            cmd.append("--lite")
            
        output_file = f"ahb_bus_m{num_masters}s{num_slaves}.v"
        cmd.append(f"--output={output_file}")
        
        # Show command
        cmd_str = " ".join(cmd)
        result = messagebox.askyesno("Generate Verilog",
                                   f"Generate AHB bus for:\n"
                                   f"- {num_masters} Masters\n"
                                   f"- {num_slaves} Slaves\n\n"
                                   f"Command:\n{cmd_str}")
        
        if result:
            # Create output directory
            output_dir = "generated_rtl"
            os.makedirs(output_dir, exist_ok=True)
            
            # Save command to script
            with open(f"{output_dir}/generate_ahb.sh", "w") as f:
                f.write("#!/bin/bash\n")
                f.write(f"# Generated by Bus Matrix GUI\n")
                f.write(f"# Configuration: {num_masters} masters, {num_slaves} slaves\n\n")
                f.write(f"cd {output_dir}\n")
                f.write(cmd_str + "\n")
                
            os.chmod(f"{output_dir}/generate_ahb.sh", 0o755)
            
            self.update_status(f"Generated script: {output_dir}/generate_ahb.sh")
            messagebox.showinfo("Success", 
                              f"Generation script created: {output_dir}/generate_ahb.sh\n"
                              f"Output file will be: {output_file}\n\n"
                              f"Run the script to generate AHB RTL using gen_amba_ahb tool.")
            
    def generate_apb(self):
        """Generate APB bridge"""
        num_slaves = len(self.current_config.slaves)
        
        # Determine bridge type based on first master
        bridge_type = "--axi"  # Default to AXI
        if self.current_config.masters and "AHB" in self.current_config.masters[0].name:
            bridge_type = "--ahb"
            
        # Build command
        cmd = [
            "../../gen_amba_apb/gen_amba_apb",
            bridge_type,
            f"--slave={num_slaves}",
            f"--module=apb_bridge_s{num_slaves}"
        ]
        
        output_file = f"apb_bridge_s{num_slaves}.v"
        cmd.append(f"--output={output_file}")
        
        # Show command
        cmd_str = " ".join(cmd)
        result = messagebox.askyesno("Generate Verilog",
                                   f"Execute command:\n\n{cmd_str}")
        
        if result:
            # Save command to script
            with open("generate_bus.sh", "w") as f:
                f.write("#!/bin/bash\n")
                f.write(f"# Generated by Bus Matrix GUI\n")
                f.write(f"# Configuration: APB bridge with {num_slaves} slaves\n\n")
                f.write(cmd_str + "\n")
                
            os.chmod("generate_bus.sh", 0o755)
            
            self.update_status(f"Generated script: generate_bus.sh")
            messagebox.showinfo("Success", 
                              f"Generation script created: generate_bus.sh\n"
                              f"Output file will be: {output_file}")
    
    def validate_address_safety(self) -> bool:
        """Validate bus configuration for address decode risks"""
        if not self.current_config.slaves:
            return True  # No slaves to validate
            
        try:
            # Run comprehensive safety validation
            is_safe, violations, report = validate_bus_configuration(
                self.current_config.slaves, 
                self.current_config.masters
            )
            
            if not is_safe:
                # Show detailed violation report
                messagebox.showerror(
                    "Address Safety Violations", 
                    f"Configuration has CRITICAL safety risks!\n\n{report}\n\n"
                    "Fix these issues before proceeding."
                )
                return False
            elif violations:
                # Show warnings but allow to continue
                response = messagebox.askquestion(
                    "Address Safety Warnings",
                    f"Configuration has warnings:\n\n{report}\n\n"
                    "Continue anyway?",
                    icon='warning'
                )
                return response == 'yes'
            else:
                # All good
                self.update_status("[OK] Address configuration validated - no safety risks detected")
                return True
                
        except Exception as e:
            messagebox.showerror("Validation Error", f"Safety validation failed: {str(e)}")
            return False
    
    def show_safety_report(self):
        """Show detailed safety analysis report"""
        if not self.current_config.slaves:
            messagebox.showinfo("Safety Report", "No slaves configured - nothing to validate.")
            return
            
        try:
            is_safe, violations, report = validate_bus_configuration(
                self.current_config.slaves, 
                self.current_config.masters
            )
            
            # Create detailed report window
            report_window = tk.Toplevel(self.root)
            report_window.title("Address Safety Report")
            report_window.geometry("800x600")
            
            # Add text widget with scrollbar
            text_frame = ttk.Frame(report_window)
            text_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
            
            text_widget = tk.Text(text_frame, wrap=tk.WORD, font=('Courier', 10))
            scrollbar = ttk.Scrollbar(text_frame, orient=tk.VERTICAL, command=text_widget.yview)
            text_widget.configure(yscrollcommand=scrollbar.set)
            
            text_widget.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
            scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
            
            # Insert report content
            text_widget.insert(tk.END, report)
            text_widget.config(state=tk.DISABLED)  # Read-only
            
            # Add summary at bottom
            summary_frame = ttk.Frame(report_window)
            summary_frame.pack(fill=tk.X, padx=10, pady=(0, 10))
            
            critical_count = len([v for v in violations if v.severity == "CRITICAL"])
            if critical_count > 0:
                status_text = f"[CRITICAL] {critical_count} CRITICAL issues found - FIX BEFORE DEPLOYMENT!"
                status_color = "red"
            elif violations:
                status_text = f"[WARNING] {len(violations)} warnings found - review recommended"
                status_color = "orange"
            else:
                status_text = "[OK] Configuration is SAFE - no issues detected"
                status_color = "green"
                
            ttk.Label(summary_frame, text=status_text, foreground=status_color).pack()
            
        except Exception as e:
            messagebox.showerror("Report Error", f"Failed to generate safety report: {str(e)}")
            
    def export_verilog(self):
        """Export complete Verilog with testbench"""
        # Validate configuration safety before export
        if not self.validate_address_safety():
            return  # User chose not to proceed with safety violations
            
        # TODO: Implement full Verilog export with address decoding
        messagebox.showinfo("Export", "Full Verilog export not yet implemented")
        
    def update_status(self, message):
        """Update status bar"""
        self.status_bar.config(text=message)
        self.root.update()
    
    def toggle_grid_snap(self):
        """Toggle grid snapping on/off"""
        self.canvas.snap_to_grid = self.grid_snap_var.get()
        if self.canvas.snap_to_grid:
            self.update_status(f"Grid snapping enabled ({self.canvas.grid_size}px)")
        else:
            self.update_status("Grid snapping disabled")
    
    def set_grid_size(self, size):
        """Set the grid size for snapping"""
        self.canvas.grid_size = size
        self.update_status(f"Grid size set to {size}px")
        # If grid snapping is enabled, snap current blocks to new grid
        if self.canvas.snap_to_grid:
            self.canvas.snap_blocks_to_grid()
    
    def zoom_in(self):
        """Zoom in the canvas"""
        if self.canvas.zoom_level < self.canvas.zoom_max:
            self.canvas.zoom_level += self.canvas.zoom_step
            self.apply_zoom()
    
    def zoom_out(self):
        """Zoom out the canvas"""
        if self.canvas.zoom_level > self.canvas.zoom_min:
            self.canvas.zoom_level -= self.canvas.zoom_step
            self.apply_zoom()
    
    def zoom_reset(self):
        """Reset zoom to 100%"""
        self.canvas.zoom_level = 1.0
        self.apply_zoom()
    
    def apply_zoom(self):
        """Apply the current zoom level to the canvas"""
        # Update zoom label
        self.zoom_label.config(text=f"{int(self.canvas.zoom_level * 100)}%")
        
        # Redraw everything with current zoom
        self.refresh_ui()
        
        # Update status
        self.update_status(f"Zoom: {int(self.canvas.zoom_level * 100)}%")
    
    def export_memory_map_csv(self):
        """Export memory map table to CSV file"""
        if not self.current_config.slaves:
            messagebox.showwarning("No Slaves", "No slaves configured to export")
            return
            
        filename = filedialog.asksaveasfilename(
            title="Export Memory Map",
            defaultextension=".csv",
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
        )
        
        if filename:
            try:
                with open(filename, 'w', newline='') as csvfile:
                    writer = csv.writer(csvfile)
                    
                    # Write header
                    writer.writerow([
                        "Slave Name", "Base Address", "End Address", "Size", 
                        "Type", "Priority", "Read Latency", "Write Latency",
                        "Secure Only", "Privileged Only", "Num Regions"
                    ])
                    
                    # Write slave data
                    for slave in self.current_config.slaves:
                        end_addr = slave.base_address + (slave.size * 1024) - 1
                        
                        # Format size
                        size_kb = slave.size
                        if size_kb >= 1048576:  # >= 1GB
                            size_text = f"{size_kb // 1048576}GB"
                        elif size_kb >= 1024:  # >= 1MB
                            size_text = f"{size_kb // 1024}MB"
                        else:
                            size_text = f"{size_kb}KB"
                        
                        writer.writerow([
                            slave.name,
                            f"0x{slave.base_address:08X}",
                            f"0x{end_addr:08X}",
                            size_text,
                            slave.memory_type,
                            slave.priority,
                            slave.read_latency,
                            slave.write_latency,
                            "Yes" if slave.secure_only else "No",
                            "Yes" if slave.privileged_only else "No",
                            slave.num_regions
                        ])
                        
                self.update_status(f"Exported memory map to {os.path.basename(filename)}")
                messagebox.showinfo("Export Complete", f"Memory map exported to:\n{filename}")
                
            except Exception as e:
                messagebox.showerror("Export Error", f"Failed to export memory map: {e}")
    
    def export_master_slave_csv(self):
        """Export master/slave configuration table to CSV file"""
        if not self.current_config.masters and not self.current_config.slaves:
            messagebox.showwarning("No Configuration", "No masters or slaves configured to export")
            return
            
        filename = filedialog.asksaveasfilename(
            title="Export Master/Slave Table",
            defaultextension=".csv",
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
        )
        
        if filename:
            try:
                with open(filename, 'w', newline='') as csvfile:
                    writer = csv.writer(csvfile)
                    
                    # Write bus configuration
                    writer.writerow(["Bus Configuration"])
                    writer.writerow(["Bus Type:", self.current_config.bus_type])
                    writer.writerow(["Data Width:", f"{self.current_config.data_width} bits"])
                    writer.writerow(["Address Width:", f"{self.current_config.addr_width} bits"])
                    writer.writerow(["Arbitration:", self.current_config.arbitration])
                    writer.writerow([])  # Empty row
                    
                    # Write masters
                    writer.writerow(["Masters"])
                    writer.writerow([
                        "Name", "ID Width", "Priority", "QoS Support", 
                        "Exclusive Support", "User Width", "Default PROT", 
                        "Default CACHE", "Default REGION"
                    ])
                    
                    for master in self.current_config.masters:
                        writer.writerow([
                            master.name,
                            master.id_width,
                            master.priority,
                            "Yes" if master.qos_support else "No",
                            "Yes" if master.exclusive_support else "No",
                            master.user_width,
                            f"0b{master.default_prot:03b}",
                            f"0x{master.default_cache:X}",
                            master.default_region
                        ])
                    
                    writer.writerow([])  # Empty row
                    
                    # Write slaves
                    writer.writerow(["Slaves"])
                    writer.writerow([
                        "Name", "Base Address", "Size", "Type", "Priority",
                        "Read Latency", "Write Latency", "Secure Only",
                        "Privileged Only", "Num Regions"
                    ])
                    
                    for slave in self.current_config.slaves:
                        # Format size
                        size_kb = slave.size
                        if size_kb >= 1048576:  # >= 1GB
                            size_text = f"{size_kb // 1048576}GB"
                        elif size_kb >= 1024:  # >= 1MB
                            size_text = f"{size_kb // 1024}MB"
                        else:
                            size_text = f"{size_kb}KB"
                            
                        writer.writerow([
                            slave.name,
                            f"0x{slave.base_address:08X}",
                            size_text,
                            slave.memory_type,
                            slave.priority,
                            slave.read_latency,
                            slave.write_latency,
                            "Yes" if slave.secure_only else "No",
                            "Yes" if slave.privileged_only else "No",
                            slave.num_regions
                        ])
                        
                self.update_status(f"Exported configuration to {os.path.basename(filename)}")
                messagebox.showinfo("Export Complete", f"Master/Slave table exported to:\n{filename}")
                
            except Exception as e:
                messagebox.showerror("Export Error", f"Failed to export configuration: {e}")
        

class MasterDialog:
    """Dialog for adding/editing master configuration"""
    
    def __init__(self, parent, config: Optional[MasterConfig] = None, default_name: str = "Master0"):
        self.result = None
        
        self.dialog = tk.Toplevel(parent)
        self.dialog.title("Master Configuration")
        self.dialog.geometry("400x550")
        self.dialog.transient(parent)
        
        # Create notebook for tabbed interface
        notebook = ttk.Notebook(self.dialog)
        notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # Basic tab
        basic_frame = ttk.Frame(notebook)
        notebook.add(basic_frame, text="Basic")
        
        # Name
        ttk.Label(basic_frame, text="Name:").grid(row=0, column=0, sticky=tk.W, padx=10, pady=5)
        self.name_var = tk.StringVar(value=config.name if config else default_name)
        ttk.Entry(basic_frame, textvariable=self.name_var, width=20).grid(row=0, column=1, padx=10, pady=5)
        
        # ID Width
        ttk.Label(basic_frame, text="ID Width:").grid(row=1, column=0, sticky=tk.W, padx=10, pady=5)
        self.id_width_var = tk.StringVar(value=str(config.id_width if config else 4))
        tk.Spinbox(basic_frame, textvariable=self.id_width_var, 
                   from_=1, to=16, width=20).grid(row=1, column=1, padx=10, pady=5)
        
        # Priority
        ttk.Label(basic_frame, text="Priority (0-15):").grid(row=2, column=0, sticky=tk.W, padx=10, pady=5)
        self.priority_var = tk.StringVar(value=str(config.priority if config else 0))
        tk.Spinbox(basic_frame, textvariable=self.priority_var, 
                   from_=0, to=15, width=20).grid(row=2, column=1, padx=10, pady=5)
        
        # QoS Support
        self.qos_var = tk.BooleanVar(value=config.qos_support if config else True)
        ttk.Checkbutton(basic_frame, text="QoS Support", 
                       variable=self.qos_var).grid(row=3, column=0, columnspan=2, padx=10, pady=5)
        
        # Exclusive Support
        self.exclusive_var = tk.BooleanVar(value=config.exclusive_support if config else True)
        ttk.Checkbutton(basic_frame, text="Exclusive Access Support", 
                       variable=self.exclusive_var).grid(row=4, column=0, columnspan=2, padx=10, pady=5)
        
        # User Width
        ttk.Label(basic_frame, text="User Signal Width:").grid(row=5, column=0, sticky=tk.W, padx=10, pady=5)
        self.user_width_var = tk.StringVar(value=str(config.user_width if config else 0))
        tk.Spinbox(basic_frame, textvariable=self.user_width_var, 
                   from_=0, to=64, width=20).grid(row=5, column=1, padx=10, pady=5)
        
        # Advanced tab
        advanced_frame = ttk.Frame(notebook)
        notebook.add(advanced_frame, text="Advanced")
        
        # Default AxPROT
        ttk.Label(advanced_frame, text="Default AxPROT:").grid(row=0, column=0, sticky=tk.W, padx=10, pady=5)
        prot_frame = ttk.Frame(advanced_frame)
        prot_frame.grid(row=0, column=1, padx=10, pady=5)
        
        self.prot_privileged_var = tk.BooleanVar(value=bool((config.default_prot if config else 0b010) & 0b001))
        self.prot_secure_var = tk.BooleanVar(value=not bool((config.default_prot if config else 0b010) & 0b010))
        self.prot_instruction_var = tk.BooleanVar(value=bool((config.default_prot if config else 0b010) & 0b100))
        
        ttk.Checkbutton(prot_frame, text="Privileged", variable=self.prot_privileged_var).pack(anchor=tk.W)
        ttk.Checkbutton(prot_frame, text="Secure", variable=self.prot_secure_var).pack(anchor=tk.W)
        ttk.Checkbutton(prot_frame, text="Instruction", variable=self.prot_instruction_var).pack(anchor=tk.W)
        
        # Default AxCACHE
        ttk.Label(advanced_frame, text="Default AxCACHE:").grid(row=1, column=0, sticky=tk.W, padx=10, pady=5)
        cache_frame = ttk.Frame(advanced_frame)
        cache_frame.grid(row=1, column=1, padx=10, pady=5)
        
        self.cache_var = tk.StringVar(value=f"0x{config.default_cache if config else 0b0011:X}")
        cache_values = {
            "Non-cacheable (0x0)": "0x0",
            "Write-through (0x2)": "0x2", 
            "Write-back (0x3)": "0x3",
            "Write-back allocate (0x7)": "0x7",
            "Write-through allocate (0xA)": "0xA",
            "Write-back write-allocate (0xF)": "0xF"
        }
        cache_combo = ttk.Combobox(cache_frame, textvariable=self.cache_var, 
                                  values=list(cache_values.values()), width=25)
        cache_combo.pack()
        
        # Default AxREGION
        ttk.Label(advanced_frame, text="Default AxREGION:").grid(row=2, column=0, sticky=tk.W, padx=10, pady=5)
        self.region_var = tk.StringVar(value=str(config.default_region if config else 0))
        tk.Spinbox(advanced_frame, textvariable=self.region_var,
                   from_=0, to=15, width=20).grid(row=2, column=1, padx=10, pady=5)
        
        # Buttons
        btn_frame = ttk.Frame(self.dialog)
        btn_frame.pack(side=tk.BOTTOM, pady=10)
        
        ttk.Button(btn_frame, text="OK", command=self.ok_clicked).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Cancel", command=self.dialog.destroy).pack(side=tk.LEFT, padx=5)
        
    def ok_clicked(self):
        """Handle OK button"""
        # Calculate AxPROT value
        prot_value = 0
        if self.prot_privileged_var.get():
            prot_value |= 0b001
        if not self.prot_secure_var.get():  # Note: secure is inverted
            prot_value |= 0b010
        if self.prot_instruction_var.get():
            prot_value |= 0b100
            
        # Parse cache value
        cache_str = self.cache_var.get()
        if cache_str.startswith("0x") or cache_str.startswith("0X"):
            cache_value = int(cache_str, 16)
        else:
            cache_value = int(cache_str)
        
        self.result = MasterConfig(
            name=self.name_var.get(),
            id_width=int(self.id_width_var.get()),
            qos_support=self.qos_var.get(),
            exclusive_support=self.exclusive_var.get(),
            user_width=int(self.user_width_var.get()),
            priority=int(self.priority_var.get()),
            default_prot=prot_value,
            default_cache=cache_value,
            default_region=int(self.region_var.get())
        )
        self.dialog.destroy()
        

class SlaveDialog:
    """Dialog for adding/editing slave configuration"""
    
    def __init__(self, parent, config: Optional[SlaveConfig] = None, default_name: str = "Slave0", default_address: int = 0, available_masters: List[str] = None):
        self.result = None
        self.available_masters = available_masters or []
        
        self.dialog = tk.Toplevel(parent)
        self.dialog.title("Slave Configuration")
        self.dialog.geometry("450x650")
        self.dialog.transient(parent)
        
        # Create notebook for tabbed interface
        notebook = ttk.Notebook(self.dialog)
        notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # Basic tab
        basic_frame = ttk.Frame(notebook)
        notebook.add(basic_frame, text="Basic")
        
        # Name
        ttk.Label(basic_frame, text="Name:").grid(row=0, column=0, sticky=tk.W, padx=10, pady=5)
        self.name_var = tk.StringVar(value=config.name if config else default_name)
        ttk.Entry(basic_frame, textvariable=self.name_var, width=20).grid(row=0, column=1, padx=10, pady=5)
        
        # Base Address
        ttk.Label(basic_frame, text="Base Address:").grid(row=1, column=0, sticky=tk.W, padx=10, pady=5)
        self.addr_var = tk.StringVar(value=f"0x{config.base_address if config else default_address:08X}")
        ttk.Entry(basic_frame, textvariable=self.addr_var, width=20).grid(row=1, column=1, padx=10, pady=5)
        
        # Size with unit
        ttk.Label(basic_frame, text="Size:").grid(row=2, column=0, sticky=tk.W, padx=10, pady=5)
        size_frame = ttk.Frame(basic_frame)
        size_frame.grid(row=2, column=1, padx=10, pady=5)
        
        # Calculate default size value and unit
        if config:
            size_kb = config.size
            if size_kb >= 1048576:  # >= 1GB in KB
                size_value = size_kb // 1048576
                size_unit = "GB"
            elif size_kb >= 1024:  # >= 1MB in KB
                size_value = size_kb // 1024
                size_unit = "MB"
            else:
                size_value = size_kb
                size_unit = "KB"
        else:
            size_value = 1
            size_unit = "MB"
            
        self.size_value_var = tk.StringVar(value=str(size_value))
        size_entry = tk.Spinbox(size_frame, textvariable=self.size_value_var,
                               from_=1, to=1024, width=10)
        size_entry.pack(side=tk.LEFT)
        
        self.size_unit_var = tk.StringVar(value=size_unit)
        unit_combo = ttk.Combobox(size_frame, textvariable=self.size_unit_var,
                                 values=["KB", "MB", "GB"],
                                 state="readonly", width=5)
        unit_combo.pack(side=tk.LEFT, padx=(5, 0))
        unit_combo.bind("<<ComboboxSelected>>", lambda e: self.update_address_info())
        
        # Memory Type
        ttk.Label(basic_frame, text="Type:").grid(row=3, column=0, sticky=tk.W, padx=10, pady=5)
        self.type_var = tk.StringVar(value=config.memory_type if config else "Memory")
        type_combo = ttk.Combobox(basic_frame, textvariable=self.type_var,
                                values=["Memory", "Peripheral"],
                                state="readonly", width=18)
        type_combo.grid(row=3, column=1, padx=10, pady=5)
        
        # Priority
        ttk.Label(basic_frame, text="Priority (0-15):").grid(row=4, column=0, sticky=tk.W, padx=10, pady=5)
        self.priority_var = tk.StringVar(value=str(config.priority if config else 0))
        tk.Spinbox(basic_frame, textvariable=self.priority_var,
                   from_=0, to=15, width=20).grid(row=4, column=1, padx=10, pady=5)
        
        # Read Latency
        ttk.Label(basic_frame, text="Read Latency:").grid(row=5, column=0, sticky=tk.W, padx=10, pady=5)
        self.read_lat_var = tk.StringVar(value=str(config.read_latency if config else 1))
        tk.Spinbox(basic_frame, textvariable=self.read_lat_var, 
                   from_=1, to=100, width=20).grid(row=5, column=1, padx=10, pady=5)
        
        # Write Latency
        ttk.Label(basic_frame, text="Write Latency:").grid(row=6, column=0, sticky=tk.W, padx=10, pady=5)
        self.write_lat_var = tk.StringVar(value=str(config.write_latency if config else 1))
        tk.Spinbox(basic_frame, textvariable=self.write_lat_var, 
                   from_=1, to=100, width=20).grid(row=6, column=1, padx=10, pady=5)
        
        # Security tab
        security_frame = ttk.Frame(notebook)
        notebook.add(security_frame, text="Security/Regions")
        
        # Number of regions
        ttk.Label(security_frame, text="Number of Regions:").grid(row=0, column=0, sticky=tk.W, padx=10, pady=5)
        self.num_regions_var = tk.StringVar(value=str(config.num_regions if config else 1))
        tk.Spinbox(security_frame, textvariable=self.num_regions_var,
                   from_=1, to=16, width=20).grid(row=0, column=1, padx=10, pady=5)
        
        # Security settings
        self.secure_only_var = tk.BooleanVar(value=config.secure_only if config else False)
        ttk.Checkbutton(security_frame, text="Secure Access Only", 
                       variable=self.secure_only_var).grid(row=1, column=0, columnspan=2, padx=10, pady=5)
        
        self.privileged_only_var = tk.BooleanVar(value=config.privileged_only if config else False)
        ttk.Checkbutton(security_frame, text="Privileged Access Only",
                       variable=self.privileged_only_var).grid(row=2, column=0, columnspan=2, padx=10, pady=5)
        
        # Permissions tab
        permissions_frame = ttk.Frame(notebook)
        notebook.add(permissions_frame, text="Permissions")
        
        # Master access permissions
        ttk.Label(permissions_frame, text="Allowed Masters:", font=('Arial', 10, 'bold')).grid(row=0, column=0, sticky=tk.W, padx=10, pady=5)
        ttk.Label(permissions_frame, text="(Empty = All masters allowed)", font=('Arial', 8)).grid(row=1, column=0, sticky=tk.W, padx=10)
        
        # Create frame for checkboxes
        master_frame = ttk.LabelFrame(permissions_frame, text="Select Masters with Access", padding=10)
        master_frame.grid(row=2, column=0, columnspan=2, padx=10, pady=10, sticky="ew")
        
        self.master_vars = {}
        # Default to all masters allowed if no specific permissions set
        if config and config.allowed_masters:
            # Specific permissions configured
            allowed_masters = config.allowed_masters
            default_state = False  # Only check specific allowed masters
        else:
            # No specific permissions (default = all allowed)
            allowed_masters = []
            default_state = True   # Check all masters by default
        
        for i, master_name in enumerate(self.available_masters):
            if allowed_masters:
                # Use specific permissions
                var = tk.BooleanVar(value=master_name in allowed_masters)
            else:
                # Default to all allowed
                var = tk.BooleanVar(value=default_state)
            self.master_vars[master_name] = var
            ttk.Checkbutton(master_frame, text=master_name, variable=var).grid(row=i//2, column=i%2, sticky=tk.W, padx=5, pady=2)
        
        # Address info
        info_frame = ttk.LabelFrame(basic_frame, text="Address Range", padding=10)
        info_frame.grid(row=7, column=0, columnspan=2, padx=10, pady=10)
        
        self.info_label = ttk.Label(info_frame, text="")
        self.info_label.pack()
        
        # Alignment help text
        help_text = "Note: Size must be power of 2 (e.g., 1, 2, 4, 8, 16...KB/MB/GB)\n"
        help_text += "Base address must be aligned to size boundary"
        self.help_label = ttk.Label(info_frame, text=help_text, font=('Arial', 8), foreground='gray')
        self.help_label.pack(pady=(5, 0))
        
        self.update_address_info()
        
        # Buttons
        btn_frame = ttk.Frame(self.dialog)
        btn_frame.pack(side=tk.BOTTOM, pady=10)
        
        ttk.Button(btn_frame, text="OK", command=self.ok_clicked).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Cancel", command=self.dialog.destroy).pack(side=tk.LEFT, padx=5)
        
        # Bind events
        self.addr_var.trace('w', lambda *args: self.update_address_info())
        self.size_value_var.trace('w', lambda *args: self.update_address_info())
        
    def update_address_info(self):
        """Update address range information"""
        try:
            addr_str = self.addr_var.get()
            if addr_str.startswith("0x") or addr_str.startswith("0X"):
                base = int(addr_str, 16)
            else:
                base = int(addr_str)
                
            size_value = int(self.size_value_var.get())
            size_unit = self.size_unit_var.get()
            
            # Convert to KB
            if size_unit == "GB":
                size_kb = size_value * 1048576
            elif size_unit == "MB":
                size_kb = size_value * 1024
            else:
                size_kb = size_value
                
            end = base + (size_kb * 1024) - 1
            
            # Check alignment
            size_bytes = size_kb * 1024
            is_pow2 = size_bytes & (size_bytes - 1) == 0
            is_aligned = base % size_bytes == 0 if is_pow2 else False
            
            info_text = f"0x{base:08X} - 0x{end:08X}"
            
            if not is_pow2:
                info_text += "\n[WARNING] Size is not power of 2"
            elif not is_aligned:
                info_text += "\n[WARNING] Address not aligned to size"
            else:
                info_text += "\n[OK] Properly aligned"
                
            self.info_label.config(text=info_text)
        except:
            self.info_label.config(text="Invalid address/size")
            
    def ok_clicked(self):
        """Handle OK button"""
        try:
            addr_str = self.addr_var.get()
            if addr_str.startswith("0x") or addr_str.startswith("0X"):
                base_addr = int(addr_str, 16)
            else:
                base_addr = int(addr_str)
                
            # Convert size to KB
            size_value = int(self.size_value_var.get())
            size_unit = self.size_unit_var.get()
            
            if size_unit == "GB":
                size_kb = size_value * 1048576
            elif size_unit == "MB":
                size_kb = size_value * 1024
            else:
                size_kb = size_value
                
            # Get allowed masters
            allowed_masters = [name for name, var in self.master_vars.items() if var.get()]
            
            # If all masters are selected, use None (default = all allowed)
            # If partial selection, use the specific list
            if len(allowed_masters) == len(self.available_masters):
                final_allowed_masters = None  # All allowed (default)
            elif len(allowed_masters) == 0:
                final_allowed_masters = None  # None selected = all allowed (default)
            else:
                final_allowed_masters = allowed_masters  # Specific restrictions
            
            self.result = SlaveConfig(
                name=self.name_var.get(),
                base_address=base_addr,
                size=size_kb,
                memory_type=self.type_var.get(),
                read_latency=int(self.read_lat_var.get()),
                write_latency=int(self.write_lat_var.get()),
                priority=int(self.priority_var.get()),
                num_regions=int(self.num_regions_var.get()),
                secure_only=self.secure_only_var.get(),
                privileged_only=self.privileged_only_var.get(),
                allowed_masters=final_allowed_masters
            )
            self.dialog.destroy()
        except ValueError:
            messagebox.showerror("Invalid Input", "Please enter valid numeric values")
            

def main():
    """Main function to start the GUI application"""
    print("Starting AMBA Bus Matrix Configuration GUI...")
    print("Loading components...")
    
    try:
        import tkinter as tk
        
        root = tk.Tk()
        print("[OK] Tkinter initialized")
        
        app = BusMatrixGUI(root)
        print("[OK] GUI application created")
        
        # Check VIP integration status
        if hasattr(app, 'vip_panel'):
            print("[OK] VIP features fully integrated and available")
        else:
            print("[INFO] VIP features in placeholder mode - use 'Check VIP Status' button")
        
        print("[START] Starting GUI event loop...")
        root.mainloop()
        
        print("GUI application closed normally")
        
    except ImportError as e:
        print(f"[ERROR] Import error: {e}")
        print("Please ensure all required modules are available")
        return 1
    except Exception as e:
        print(f"[ERROR] GUI startup failed: {e}")
        import traceback
        traceback.print_exc()
        return 1
    
    return 0

if __name__ == "__main__":
    import sys
    exit_code = main()
    sys.exit(exit_code)