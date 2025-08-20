#!/usr/bin/env python3
"""
Visual Bus Layout Canvas
Draggable nodes for Masters/Slaves with interconnect
Based on gui_build.md specification
"""

import tkinter as tk
from tkinter import ttk
import math
from typing import Optional, Tuple, List
from bus_config import Project, MasterNode, SlaveNode, EdgeConfig, QoSConfig

class BusCanvas(tk.Canvas):
    """Visual bus layout with draggable nodes"""
    
    def __init__(self, parent, project: Project, **kwargs):
        super().__init__(parent, bg='white', **kwargs)
        self.project = project
        
        # Visual settings
        self.master_color = '#4CAF50'
        self.slave_color = '#2196F3'
        self.interconnect_color = '#FFC107'
        self.edge_color = '#757575'
        self.selected_color = '#FF5722'
        
        # Node dimensions
        self.node_width = 120
        self.node_height = 80
        self.interconnect_width = 200
        self.interconnect_height = 150
        
        # Drag state
        self.dragging = False
        self.drag_data = {"x": 0, "y": 0, "item": None, "node": None}
        self.selected_node = None
        
        # Grid snap
        self.grid_snap = True
        self.grid_size = 20
        
        # Node visuals
        self.node_items = {}  # node -> canvas item mapping
        self.edge_items = []  # edge line items
        
        # Callbacks
        self.on_node_selected = None
        self.on_edge_selected = None
        
        # Bind events
        self.bind('<Button-1>', self.on_click)
        self.bind('<B1-Motion>', self.on_drag)
        self.bind('<ButtonRelease-1>', self.on_release)
        self.bind('<Button-3>', self.on_right_click)
        self.bind('<Double-Button-1>', self.on_double_click)
        
        # Initial layout
        self.refresh()
    
    def refresh(self):
        """Refresh the entire canvas"""
        self.delete("all")
        self.node_items.clear()
        self.edge_items.clear()
        
        # Draw grid if enabled
        if self.grid_snap:
            self.draw_grid()
        
        # Draw interconnect
        self.draw_interconnect()
        
        # Draw nodes
        for master in self.project.masters:
            self.draw_master(master)
        
        for slave in self.project.slaves:
            self.draw_slave(slave)
        
        # Draw edges
        self.draw_edges()
    
    def draw_grid(self):
        """Draw background grid"""
        width = int(self.cget('width'))
        height = int(self.cget('height'))
        
        for x in range(0, width, self.grid_size):
            self.create_line(x, 0, x, height, fill='#f0f0f0', tags='grid')
        
        for y in range(0, height, self.grid_size):
            self.create_line(0, y, width, y, fill='#f0f0f0', tags='grid')
    
    def draw_interconnect(self):
        """Draw the central interconnect"""
        cx = int(self.cget('width')) // 2
        cy = int(self.cget('height')) // 2
        
        # Calculate interconnect size based on number of masters and slaves
        num_masters = len(self.project.masters)
        num_slaves = len(self.project.slaves)
        max_nodes = max(num_masters, num_slaves)
        
        # Expand width based on node count (minimum 200px, +100px per additional node beyond 2)
        dynamic_width = max(200, 200 + (max_nodes - 2) * 100)
        
        x1 = cx - dynamic_width // 2
        y1 = cy - self.interconnect_height // 2
        x2 = cx + dynamic_width // 2
        y2 = cy + self.interconnect_height // 2
        
        # Draw interconnect box
        self.create_rectangle(x1, y1, x2, y2,
                             fill=self.interconnect_color,
                             outline='black', width=2,
                             tags=('interconnect', 'node'))
        
        # Draw label
        self.create_text(cx, cy - 30,
                        text="AXI Interconnect",
                        font=('Arial', 12, 'bold'),
                        tags='interconnect')
        
        # Draw configuration info
        config_text = f"{len(self.project.masters)}×{len(self.project.slaves)}"
        if self.project.bus.qos:
            config_text += " QoS"
        if self.project.bus.arbitration == "fixed":
            config_text += " Fixed"
        elif self.project.bus.arbitration == "rr":
            config_text += " RR"
        
        self.create_text(cx, cy,
                        text=config_text,
                        font=('Arial', 10),
                        tags='interconnect')
        
        # Store interconnect position
        self.interconnect_bbox = (x1, y1, x2, y2)
    
    def draw_master(self, master: MasterNode):
        """Draw a master node"""
        # Use stored position or auto-layout
        if master.x == 0 and master.y == 0:
            # Auto position horizontally above interconnect
            canvas_width = int(self.cget('width'))
            num_masters = len(self.project.masters)
            
            # Calculate spacing to distribute masters evenly across the top
            if num_masters == 1:
                master.x = canvas_width // 2 - self.node_width // 2
            else:
                spacing = (canvas_width - 200) // (num_masters + 1)  # Leave margins
                master.x = 100 + spacing * (master.m_index + 1) - self.node_width // 2
            
            master.y = 50  # Fixed Y position above interconnect
        
        x, y = master.x, master.y
        
        # Draw rectangle
        rect = self.create_rectangle(x, y,
                                    x + self.node_width,
                                    y + self.node_height,
                                    fill=self.master_color,
                                    outline='black', width=2,
                                    tags=('master', f'M{master.m_index}', 'node'))
        
        # Draw index only (cleaner display)
        self.create_text(x + self.node_width // 2, y + 20,
                        text=f"M{master.m_index}",
                        font=('Arial', 10, 'bold'),
                        tags=('master', f'M{master.m_index}'))
        
        # Draw QoS if enabled
        if self.project.bus.qos and self.project.preferences.show_qos:
            qos_text = f"AWQ:{master.qos_default.aw} ARQ:{master.qos_default.ar}"
            self.create_text(x + self.node_width // 2, y + 40,
                           text=qos_text,
                           font=('Arial', 8),
                           fill='darkgreen',
                           tags=('master', f'M{master.m_index}'))
        
        # Draw outstanding transactions
        out_text = f"R:{master.outstanding['read']} W:{master.outstanding['write']}"
        self.create_text(x + self.node_width // 2, y + 60,
                        text=out_text,
                        font=('Arial', 8),
                        fill='darkgreen',
                        tags=('master', f'M{master.m_index}'))
        
        # Store item
        self.node_items[f'M{master.m_index}'] = rect
    
    def draw_slave(self, slave: SlaveNode):
        """Draw a slave node"""
        # Use stored position or auto-layout
        if slave.x == 0 and slave.y == 0:
            # Auto position horizontally below interconnect
            canvas_width = int(self.cget('width'))
            canvas_height = int(self.cget('height'))
            num_slaves = len(self.project.slaves)
            
            # Calculate spacing to distribute slaves evenly across the bottom
            if num_slaves == 1:
                slave.x = canvas_width // 2 - self.node_width // 2
            else:
                spacing = (canvas_width - 200) // (num_slaves + 1)  # Leave margins
                slave.x = 100 + spacing * (slave.s_index + 1) - self.node_width // 2
            
            slave.y = canvas_height - 150  # Fixed Y position below interconnect
        
        x, y = slave.x, slave.y
        
        # Draw rectangle
        rect = self.create_rectangle(x, y,
                                    x + self.node_width,
                                    y + self.node_height,
                                    fill=self.slave_color,
                                    outline='black', width=2,
                                    tags=('slave', f'S{slave.s_index}', 'node'))
        
        # Draw index only (cleaner display)
        self.create_text(x + self.node_width // 2, y + 20,
                        text=f"S{slave.s_index}",
                        font=('Arial', 10, 'bold'),
                        tags=('slave', f'S{slave.s_index}'))
        
        # Draw address range
        addr_text = f"0x{slave.base:08X}"
        size_text = f"{slave.size // 1024}KB"
        self.create_text(x + self.node_width // 2, y + 40,
                        text=f"{addr_text}",
                        font=('Arial', 8),
                        fill='darkblue',
                        tags=('slave', f'S{slave.s_index}'))
        self.create_text(x + self.node_width // 2, y + 55,
                        text=f"{size_text}",
                        font=('Arial', 8),
                        fill='darkblue',
                        tags=('slave', f'S{slave.s_index}'))
        
        # Draw priority if enabled
        if self.project.preferences.show_priority and slave.priority:
            if self.project.bus.arbitration == "fixed" and "order" in slave.priority:
                # Show top 3 masters in priority order
                order = slave.priority.get("order", [])[:3]
                if order:
                    prio_text = "P: " + ">".join(order)
                    self.create_text(x + self.node_width // 2, y + 70,
                                   text=prio_text,
                                   font=('Arial', 7),
                                   fill='purple',
                                   tags=('slave', f'S{slave.s_index}'))
            elif self.project.bus.arbitration == "rr":
                self.create_text(x + self.node_width // 2, y + 70,
                               text="P: RR",
                               font=('Arial', 7),
                               fill='purple',
                               tags=('slave', f'S{slave.s_index}'))
            elif self.project.bus.arbitration == "qos":
                self.create_text(x + self.node_width // 2, y + 70,
                               text="P: QoS",
                               font=('Arial', 7),
                               fill='purple',
                               tags=('slave', f'S{slave.s_index}'))
        
        # Store item
        self.node_items[f'S{slave.s_index}'] = rect
    
    def draw_edges(self):
        """Draw connection edges"""
        # Draw master to interconnect edges
        for master in self.project.masters:
            self.draw_edge_line(f'M{master.m_index}', 'interconnect')
        
        # Draw interconnect to slave edges
        for slave in self.project.slaves:
            self.draw_edge_line('interconnect', f'S{slave.s_index}')
    
    def draw_edge_line(self, from_node: str, to_node: str):
        """Draw a single edge line"""
        # Get node positions
        from_pos = self.get_node_center(from_node)
        to_pos = self.get_node_center(to_node)
        
        if not from_pos or not to_pos:
            return
        
        # Check if edge has overrides
        has_override = False
        for edge in self.project.edges:
            if edge.from_node == from_node and edge.to_node == to_node:
                if edge.qos or edge.cache or edge.prot or edge.region:
                    has_override = True
                    break
        
        # Draw line
        line_width = 3 if has_override else 2
        line = self.create_line(from_pos[0], from_pos[1],
                               to_pos[0], to_pos[1],
                               fill=self.edge_color,
                               width=line_width,
                               arrow=tk.LAST,
                               tags=('edge', f'{from_node}->{to_node}'))
        
        # Draw override indicator if needed
        if has_override:
            # Draw small circle at midpoint
            mid_x = (from_pos[0] + to_pos[0]) // 2
            mid_y = (from_pos[1] + to_pos[1]) // 2
            self.create_oval(mid_x - 4, mid_y - 4,
                           mid_x + 4, mid_y + 4,
                           fill='red', outline='darkred',
                           tags=('edge-override', f'{from_node}->{to_node}'))
        
        self.edge_items.append(line)
    
    def get_node_center(self, node_id: str) -> Optional[Tuple[int, int]]:
        """Get the center position of a node"""
        if node_id == 'interconnect':
            if hasattr(self, 'interconnect_bbox'):
                x1, y1, x2, y2 = self.interconnect_bbox
                return ((x1 + x2) // 2, (y1 + y2) // 2)
        elif node_id in self.node_items:
            bbox = self.bbox(self.node_items[node_id])
            if bbox:
                x1, y1, x2, y2 = bbox
                return ((x1 + x2) // 2, (y1 + y2) // 2)
        return None
    
    def on_click(self, event):
        """Handle mouse click"""
        # Find clicked item
        item = self.find_closest(event.x, event.y)[0]
        tags = self.gettags(item)
        
        if 'node' in tags:
            # Start dragging
            self.dragging = True
            self.drag_data["x"] = event.x
            self.drag_data["y"] = event.y
            self.drag_data["item"] = item
            
            # Find which node
            for tag in tags:
                if tag.startswith('M') or tag.startswith('S'):
                    self.drag_data["node"] = tag
                    self.select_node(tag)
                    break
        elif 'edge' in tags:
            # Select edge
            for tag in tags:
                if '->' in tag:
                    self.select_edge(tag)
                    break
    
    def on_drag(self, event):
        """Handle mouse drag"""
        if self.dragging and self.drag_data["item"]:
            # Calculate delta
            dx = event.x - self.drag_data["x"]
            dy = event.y - self.drag_data["y"]
            
            # Move the node
            node_tag = self.drag_data["node"]
            if node_tag and node_tag != 'interconnect':
                # Move all items with this tag
                for item in self.find_withtag(node_tag):
                    self.move(item, dx, dy)
                
                # Update stored position
                if node_tag.startswith('M'):
                    idx = int(node_tag[1:])
                    if 0 <= idx < len(self.project.masters):
                        self.project.masters[idx].x += dx
                        self.project.masters[idx].y += dy
                elif node_tag.startswith('S'):
                    idx = int(node_tag[1:])
                    if 0 <= idx < len(self.project.slaves):
                        self.project.slaves[idx].x += dx
                        self.project.slaves[idx].y += dy
                
                # Redraw edges
                self.delete('edge')
                self.delete('edge-override')
                self.draw_edges()
            
            # Update drag position
            self.drag_data["x"] = event.x
            self.drag_data["y"] = event.y
    
    def on_release(self, event):
        """Handle mouse release"""
        if self.dragging:
            # Snap to grid if enabled
            if self.grid_snap and self.drag_data["node"]:
                node_tag = self.drag_data["node"]
                if node_tag.startswith('M'):
                    idx = int(node_tag[1:])
                    if 0 <= idx < len(self.project.masters):
                        master = self.project.masters[idx]
                        master.x = round(master.x / self.grid_size) * self.grid_size
                        master.y = round(master.y / self.grid_size) * self.grid_size
                elif node_tag.startswith('S'):
                    idx = int(node_tag[1:])
                    if 0 <= idx < len(self.project.slaves):
                        slave = self.project.slaves[idx]
                        slave.x = round(slave.x / self.grid_size) * self.grid_size
                        slave.y = round(slave.y / self.grid_size) * self.grid_size
                
                # Refresh to apply snap
                self.refresh()
        
        self.dragging = False
        self.drag_data = {"x": 0, "y": 0, "item": None, "node": None}
    
    def on_right_click(self, event):
        """Handle right click for context menu"""
        # Find clicked item
        item = self.find_closest(event.x, event.y)[0]
        tags = self.gettags(item)
        
        if 'node' in tags:
            # Show node context menu
            for tag in tags:
                if tag.startswith('M') or tag.startswith('S'):
                    self.show_node_menu(event, tag)
                    break
    
    def on_double_click(self, event):
        """Handle double click"""
        # Find clicked item
        item = self.find_closest(event.x, event.y)[0]
        tags = self.gettags(item)
        
        if 'node' in tags:
            # Edit node properties
            for tag in tags:
                if tag.startswith('M') or tag.startswith('S'):
                    self.edit_node(tag)
                    break
    
    def select_node(self, node_id: str):
        """Select a node"""
        self.selected_node = node_id
        
        # Highlight selected node
        if node_id in self.node_items:
            self.itemconfig(self.node_items[node_id], outline=self.selected_color, width=3)
        
        # Unhighlight others
        for nid, item in self.node_items.items():
            if nid != node_id:
                self.itemconfig(item, outline='black', width=2)
        
        # Callback
        if self.on_node_selected:
            self.on_node_selected(node_id)
    
    def select_edge(self, edge_id: str):
        """Select an edge"""
        # Highlight edge
        for item in self.find_withtag(edge_id):
            if 'edge' in self.gettags(item):
                self.itemconfig(item, fill=self.selected_color, width=4)
        
        # Unhighlight other edges
        for item in self.edge_items:
            tags = self.gettags(item)
            if edge_id not in tags:
                self.itemconfig(item, fill=self.edge_color, width=2)
        
        # Callback
        if self.on_edge_selected:
            parts = edge_id.split('->')
            if len(parts) == 2:
                self.on_edge_selected(parts[0], parts[1])
    
    def show_node_menu(self, event, node_id: str):
        """Show context menu for a node"""
        menu = tk.Menu(self, tearoff=0)
        menu.add_command(label=f"Edit {node_id}", command=lambda: self.edit_node(node_id))
        menu.add_command(label=f"Delete {node_id}", command=lambda: self.delete_node(node_id))
        menu.add_separator()
        menu.add_command(label="Cancel")
        menu.post(event.x_root, event.y_root)
    
    def edit_node(self, node_id: str):
        """Edit node properties (placeholder for dialog)"""
        print(f"Edit node: {node_id}")
        # This will be connected to the property editor
    
    def delete_node(self, node_id: str):
        """Delete a node"""
        if node_id.startswith('M'):
            idx = int(node_id[1:])
            self.project.delete_master(idx)
        elif node_id.startswith('S'):
            idx = int(node_id[1:])
            self.project.delete_slave(idx)
        
        self.refresh()
    
    def auto_layout(self):
        """Auto-arrange all nodes"""
        canvas_width = int(self.cget('width'))
        canvas_height = int(self.cget('height'))
        
        # Position masters horizontally at the top
        num_masters = len(self.project.masters)
        for i, master in enumerate(self.project.masters):
            if num_masters == 1:
                master.x = canvas_width // 2 - self.node_width // 2
            else:
                spacing = (canvas_width - 200) // (num_masters + 1)
                master.x = 100 + spacing * (i + 1) - self.node_width // 2
            master.y = 50
        
        # Position slaves horizontally at the bottom
        num_slaves = len(self.project.slaves)
        for i, slave in enumerate(self.project.slaves):
            if num_slaves == 1:
                slave.x = canvas_width // 2 - self.node_width // 2
            else:
                spacing = (canvas_width - 200) // (num_slaves + 1)
                slave.x = 100 + spacing * (i + 1) - self.node_width // 2
            slave.y = canvas_height - 150
        
        self.refresh()