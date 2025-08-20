#!/usr/bin/env python3
"""
AMBA AXI4 RTL & VIP Generator - Main GUI Application
Based on gui_build.md v3 specification
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import os
import sys
import time
from pathlib import Path

# Add current directory to path
sys.path.insert(0, str(Path(__file__).parent))

from bus_config import Project, BusConfig, MasterNode, SlaveNode, QoSConfig
from bus_canvas import BusCanvas
from template_gallery import TemplateGallery
from priority_editor import PriorityEditor
from generator import Generator
from logger import get_logger, AppLogger
from log_viewer import LogViewer, BatchManager
from batch_processor import get_batch_processor, BatchTask

class AXI4GeneratorGUI:
    """Main GUI application for AXI4 RTL & VIP Generator"""
    
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("AMBA AXI4 RTL & VIP Generator v3")
        self.root.geometry("1400x900")
        
        # Initialize logging
        self.logger = get_logger("main_gui")
        self.logger.info("Starting AXI4 Generator GUI v3")
        
        # Initialize batch processor
        self.batch_processor = get_batch_processor(max_workers=2)
        
        # Initialize project
        self.project = Project(name="untitled")
        
        # Setup UI
        self.setup_menu()
        self.setup_toolbar()
        self.setup_main_layout()
        self.setup_status_bar()
        
        # Check for template on startup
        self.root.after(100, self.show_template_gallery)
        
        # Setup cleanup on exit
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        
    def setup_menu(self):
        """Setup menu bar"""
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)
        
        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="New Project", command=self.new_project, accelerator="Ctrl+N")
        file_menu.add_command(label="Open Project...", command=self.open_project, accelerator="Ctrl+O")
        file_menu.add_command(label="Save Project", command=self.save_project, accelerator="Ctrl+S")
        file_menu.add_command(label="Save Project As...", command=self.save_project_as)
        file_menu.add_separator()
        file_menu.add_command(label="Template Gallery...", command=self.show_template_gallery)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)
        
        # Edit menu
        edit_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Edit", menu=edit_menu)
        edit_menu.add_command(label="Add Master", command=self.add_master, accelerator="Ctrl+M")
        edit_menu.add_command(label="Add Slave", command=self.add_slave, accelerator="Ctrl+L")
        edit_menu.add_separator()
        edit_menu.add_command(label="Bus Configuration...", command=self.edit_bus_config)
        edit_menu.add_command(label="Preferences...", command=self.edit_preferences)
        
        # Batch menu
        batch_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Batch", menu=batch_menu)
        batch_menu.add_command(label="Start Batch Processor", command=self.start_batch_processor)
        batch_menu.add_command(label="Stop Batch Processor", command=self.stop_batch_processor)
        batch_menu.add_separator()
        batch_menu.add_command(label="Add Current Project to Batch", command=self.add_to_batch)
        batch_menu.add_command(label="Create Template Batch...", command=self.create_template_batch)
        batch_menu.add_separator()
        batch_menu.add_command(label="Show Batch Manager", command=self.show_batch_manager)
        
        # View menu
        view_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="View", menu=view_menu)
        view_menu.add_command(label="Show Logs", command=self.show_log_viewer)
        view_menu.add_command(label="Show Batch Manager", command=self.show_batch_manager)
        view_menu.add_separator()
        
        self.show_qos_var = tk.BooleanVar(value=True)
        self.show_priority_var = tk.BooleanVar(value=True)
        self.show_cache_var = tk.BooleanVar(value=False)
        self.show_prot_var = tk.BooleanVar(value=False)
        self.show_region_var = tk.BooleanVar(value=False)
        
        view_menu.add_checkbutton(label="Show QoS", variable=self.show_qos_var, 
                                 command=self.update_view_preferences)
        view_menu.add_checkbutton(label="Show Priority", variable=self.show_priority_var,
                                 command=self.update_view_preferences)
        view_menu.add_checkbutton(label="Show Cache", variable=self.show_cache_var,
                                 command=self.update_view_preferences)
        view_menu.add_checkbutton(label="Show Prot", variable=self.show_prot_var,
                                 command=self.update_view_preferences)
        view_menu.add_checkbutton(label="Show Region", variable=self.show_region_var,
                                 command=self.update_view_preferences)
        view_menu.add_separator()
        view_menu.add_command(label="Auto Layout", command=self.auto_layout)
        view_menu.add_command(label="Zoom In", command=self.zoom_in, accelerator="Ctrl++")
        view_menu.add_command(label="Zoom Out", command=self.zoom_out, accelerator="Ctrl+-")
        view_menu.add_command(label="Zoom Reset", command=self.zoom_reset, accelerator="Ctrl+0")
        
        # Generate menu
        generate_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Generate", menu=generate_menu)
        generate_menu.add_command(label="Generate RTL...", command=self.generate_rtl, accelerator="F5")
        generate_menu.add_command(label="Generate VIP...", command=self.generate_vip, accelerator="F6")
        generate_menu.add_separator()
        generate_menu.add_command(label="Validate Configuration", command=self.validate_config)
        
        # Help menu
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="User Guide", command=self.show_help)
        help_menu.add_command(label="About", command=self.show_about)
        
        # Bind accelerators
        self.root.bind('<Control-n>', lambda e: self.new_project())
        self.root.bind('<Control-o>', lambda e: self.open_project())
        self.root.bind('<Control-s>', lambda e: self.save_project())
        self.root.bind('<Control-m>', lambda e: self.add_master())
        self.root.bind('<Control-l>', lambda e: self.add_slave())
        self.root.bind('<F5>', lambda e: self.generate_rtl())
        self.root.bind('<F6>', lambda e: self.generate_vip())
    
    def setup_toolbar(self):
        """Setup toolbar"""
        toolbar = ttk.Frame(self.root, relief=tk.RAISED, borderwidth=1)
        toolbar.pack(side=tk.TOP, fill=tk.X)
        
        # Toolbar buttons
        ttk.Button(toolbar, text="New", command=self.new_project).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Open", command=self.open_project).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Save", command=self.save_project).pack(side=tk.LEFT, padx=2)
        
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)
        
        ttk.Button(toolbar, text="+ Master", command=self.add_master).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="+ Slave", command=self.add_slave).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Delete", command=self.delete_selected).pack(side=tk.LEFT, padx=2)
        
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)
        
        ttk.Button(toolbar, text="Zoom In", command=self.zoom_in).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Zoom Out", command=self.zoom_out).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Auto Layout", command=self.auto_layout).pack(side=tk.LEFT, padx=2)
        
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)
        
        ttk.Button(toolbar, text="Generate RTL", command=self.generate_rtl).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="Generate VIP", command=self.generate_vip).pack(side=tk.LEFT, padx=2)
    
    def setup_main_layout(self):
        """Setup main layout with canvas and property panels"""
        # Main paned window
        main_paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Left panel - Properties
        left_frame = ttk.Frame(main_paned, width=300)
        main_paned.add(left_frame, weight=0)
        
        # Property notebook
        self.prop_notebook = ttk.Notebook(left_frame)
        self.prop_notebook.pack(fill=tk.BOTH, expand=True)
        
        # Bus properties tab
        self.setup_bus_properties_tab()
        
        # Node properties tab
        self.setup_node_properties_tab()
        
        # Edge properties tab
        self.setup_edge_properties_tab()
        
        # Log viewer tab
        self.setup_log_viewer_tab()
        
        # Batch manager tab
        self.setup_batch_manager_tab()
        
        # Center - Canvas
        canvas_frame = ttk.LabelFrame(main_paned, text="Bus Matrix Layout")
        main_paned.add(canvas_frame, weight=3)
        
        # Create canvas
        self.canvas = BusCanvas(canvas_frame, self.project, width=800, height=600)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        
        # Set callbacks
        self.canvas.on_node_selected = self.on_node_selected
        self.canvas.on_edge_selected = self.on_edge_selected
        
        # Right panel - Info
        right_frame = ttk.Frame(main_paned, width=250)
        main_paned.add(right_frame, weight=0)
        
        # Info notebook
        info_notebook = ttk.Notebook(right_frame)
        info_notebook.pack(fill=tk.BOTH, expand=True)
        
        # Summary tab
        summary_frame = ttk.Frame(info_notebook)
        info_notebook.add(summary_frame, text="Summary")
        
        self.summary_text = tk.Text(summary_frame, width=30, height=20, wrap=tk.WORD)
        self.summary_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.update_summary()
        
        # Messages tab
        messages_frame = ttk.Frame(info_notebook)
        info_notebook.add(messages_frame, text="Messages")
        
        self.messages_text = tk.Text(messages_frame, width=30, height=20, wrap=tk.WORD)
        self.messages_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
    
    def setup_bus_properties_tab(self):
        """Setup bus properties tab"""
        bus_frame = ttk.Frame(self.prop_notebook)
        self.prop_notebook.add(bus_frame, text="Bus")
        
        # Bus configuration
        config_frame = ttk.LabelFrame(bus_frame, text="Bus Configuration", padding=10)
        config_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # Address width
        ttk.Label(config_frame, text="Address Width:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
        self.addr_width_var = tk.IntVar(value=self.project.bus.addr_width)
        # Use tk.Spinbox instead of ttk.Spinbox for compatibility
        addr_spin = tk.Spinbox(config_frame, from_=8, to=64, textvariable=self.addr_width_var, width=10)
        addr_spin.grid(row=0, column=1, padx=5, pady=2)
        addr_spin.bind('<FocusOut>', lambda e: self.update_bus_config())
        
        # Data width
        ttk.Label(config_frame, text="Data Width:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
        self.data_width_var = tk.StringVar(value=str(self.project.bus.data_width))
        data_combo = ttk.Combobox(config_frame, textvariable=self.data_width_var,
                                 values=["8", "16", "32", "64", "128", "256", "512", "1024"],
                                 state="readonly", width=10)
        data_combo.grid(row=1, column=1, padx=5, pady=2)
        data_combo.bind('<<ComboboxSelected>>', lambda e: self.update_bus_config())
        
        # ID width
        ttk.Label(config_frame, text="ID Width:").grid(row=2, column=0, sticky=tk.W, padx=5, pady=2)
        self.id_width_var = tk.IntVar(value=self.project.bus.id_width)
        # Use tk.Spinbox instead of ttk.Spinbox for compatibility
        id_spin = tk.Spinbox(config_frame, from_=1, to=16, textvariable=self.id_width_var, width=10)
        id_spin.grid(row=2, column=1, padx=5, pady=2)
        id_spin.bind('<FocusOut>', lambda e: self.update_bus_config())
        
        # Arbitration
        ttk.Label(config_frame, text="Arbitration:").grid(row=3, column=0, sticky=tk.W, padx=5, pady=2)
        self.arbitration_var = tk.StringVar(value=self.project.bus.arbitration)
        arb_combo = ttk.Combobox(config_frame, textvariable=self.arbitration_var,
                                values=["fixed", "rr", "qos"],
                                state="readonly", width=10)
        arb_combo.grid(row=3, column=1, padx=5, pady=2)
        arb_combo.bind('<<ComboboxSelected>>', lambda e: self.update_bus_config())
        
        # Features
        features_frame = ttk.LabelFrame(bus_frame, text="Features", padding=10)
        features_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.qos_var = tk.BooleanVar(value=self.project.bus.qos)
        ttk.Checkbutton(features_frame, text="QoS Support", variable=self.qos_var,
                       command=self.update_bus_config).pack(anchor=tk.W)
        
        self.cache_var = tk.BooleanVar(value=self.project.bus.cache)
        ttk.Checkbutton(features_frame, text="Cache Support", variable=self.cache_var,
                       command=self.update_bus_config).pack(anchor=tk.W)
        
        self.prot_var = tk.BooleanVar(value=self.project.bus.prot)
        ttk.Checkbutton(features_frame, text="Protection Support", variable=self.prot_var,
                       command=self.update_bus_config).pack(anchor=tk.W)
        
        self.region_var = tk.BooleanVar(value=self.project.bus.region)
        ttk.Checkbutton(features_frame, text="Region Support", variable=self.region_var,
                       command=self.update_bus_config).pack(anchor=tk.W)
        
        # Default QoS
        qos_frame = ttk.LabelFrame(bus_frame, text="Default QoS", padding=10)
        qos_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(qos_frame, text="Default AWQoS:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
        self.default_awqos_var = tk.IntVar(value=self.project.bus.qos_default.aw)
        # Use tk.Spinbox instead of ttk.Spinbox for compatibility
        awqos_spin = tk.Spinbox(qos_frame, from_=0, to=15, textvariable=self.default_awqos_var, width=10)
        awqos_spin.grid(row=0, column=1, padx=5, pady=2)
        awqos_spin.bind('<FocusOut>', lambda e: self.update_bus_config())
        
        ttk.Label(qos_frame, text="Default ARQoS:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
        self.default_arqos_var = tk.IntVar(value=self.project.bus.qos_default.ar)
        # Use tk.Spinbox instead of ttk.Spinbox for compatibility
        arqos_spin = tk.Spinbox(qos_frame, from_=0, to=15, textvariable=self.default_arqos_var, width=10)
        arqos_spin.grid(row=1, column=1, padx=5, pady=2)
        arqos_spin.bind('<FocusOut>', lambda e: self.update_bus_config())
    
    def setup_node_properties_tab(self):
        """Setup node properties tab"""
        node_frame = ttk.Frame(self.prop_notebook)
        self.prop_notebook.add(node_frame, text="Node")
        
        # Selected node info
        info_frame = ttk.LabelFrame(node_frame, text="Selected Node", padding=10)
        info_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.node_info_label = ttk.Label(info_frame, text="No node selected")
        self.node_info_label.pack(anchor=tk.W)
        
        # Node properties will be dynamically created based on selection
        self.node_props_frame = ttk.Frame(node_frame)
        self.node_props_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
    
    def setup_edge_properties_tab(self):
        """Setup edge properties tab"""
        edge_frame = ttk.Frame(self.prop_notebook)
        self.prop_notebook.add(edge_frame, text="Edge")
        
        # Selected edge info
        info_frame = ttk.LabelFrame(edge_frame, text="Selected Edge", padding=10)
        info_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.edge_info_label = ttk.Label(info_frame, text="No edge selected")
        self.edge_info_label.pack(anchor=tk.W)
        
        # Edge overrides will be dynamically created
        self.edge_props_frame = ttk.Frame(edge_frame)
        self.edge_props_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
    
    def setup_status_bar(self):
        """Setup status bar"""
        self.status_bar = ttk.Label(self.root, text="Ready", relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
    
    def new_project(self):
        """Create new project"""
        if messagebox.askyesno("New Project", "Discard current project and start new?"):
            self.project = Project(name="untitled")
            self.canvas.project = self.project
            self.canvas.refresh()
            self.update_summary()
            self.set_status("New project created")
    
    def open_project(self):
        """Open project from file"""
        filename = filedialog.askopenfilename(
            title="Open Project",
            filetypes=[("YAML files", "*.yaml"), ("All files", "*.*")]
        )
        if filename:
            try:
                with open(filename, 'r') as f:
                    self.project = Project.from_yaml(f.read())
                self.canvas.project = self.project
                self.canvas.refresh()
                self.update_summary()
                self.set_status(f"Opened: {os.path.basename(filename)}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to open project:\n{str(e)}")
    
    def save_project(self):
        """Save current project"""
        if not hasattr(self, 'project_file'):
            self.save_project_as()
        else:
            try:
                with open(self.project_file, 'w') as f:
                    f.write(self.project.to_yaml())
                self.set_status(f"Saved: {os.path.basename(self.project_file)}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save project:\n{str(e)}")
    
    def save_project_as(self):
        """Save project with new name"""
        filename = filedialog.asksaveasfilename(
            title="Save Project As",
            defaultextension=".yaml",
            filetypes=[("YAML files", "*.yaml"), ("All files", "*.*")]
        )
        if filename:
            self.project_file = filename
            self.save_project()
    
    def show_template_gallery(self):
        """Show template gallery dialog"""
        gallery = TemplateGallery(self.root)
        template = gallery.wait()
        
        if template:
            self.project = TemplateGallery.create_template_project(template)
            self.canvas.project = self.project
            self.canvas.refresh()
            self.update_summary()
            self.set_status(f"Loaded template: {template}")
    
    def add_master(self):
        """Add a new master"""
        # Simple dialog for master name
        dialog = tk.Toplevel(self.root)
        dialog.title("Add Master")
        dialog.geometry("300x150")
        dialog.transient(self.root)
        dialog.grab_set()
        
        ttk.Label(dialog, text="Master Name:").pack(pady=10)
        name_var = tk.StringVar(value=f"Master{len(self.project.masters)}")
        name_entry = ttk.Entry(dialog, textvariable=name_var, width=30)
        name_entry.pack(pady=5)
        name_entry.select_range(0, tk.END)
        name_entry.focus()
        
        def on_ok():
            name = name_var.get().strip()
            if name:
                master = self.project.add_master(name)
                self.canvas.refresh()
                self.update_summary()
                self.set_status(f"Added master: {name}")
            dialog.destroy()
        
        button_frame = ttk.Frame(dialog)
        button_frame.pack(pady=10)
        ttk.Button(button_frame, text="OK", command=on_ok).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Cancel", command=dialog.destroy).pack(side=tk.LEFT)
        
        name_entry.bind('<Return>', lambda e: on_ok())
    
    def add_slave(self):
        """Add a new slave"""
        # Dialog for slave configuration
        dialog = tk.Toplevel(self.root)
        dialog.title("Add Slave")
        dialog.geometry("400x250")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Name
        ttk.Label(dialog, text="Slave Name:").grid(row=0, column=0, sticky=tk.W, padx=10, pady=5)
        name_var = tk.StringVar(value=f"Slave{len(self.project.slaves)}")
        name_entry = ttk.Entry(dialog, textvariable=name_var, width=30)
        name_entry.grid(row=0, column=1, padx=10, pady=5)
        
        # Base address
        ttk.Label(dialog, text="Base Address:").grid(row=1, column=0, sticky=tk.W, padx=10, pady=5)
        # Auto-calculate next address
        if self.project.slaves:
            last_slave = self.project.slaves[-1]
            next_base = last_slave.base + last_slave.size
            next_base = ((next_base + 0xFFFF) // 0x10000) * 0x10000  # Align to 64KB
        else:
            next_base = 0x00000000
        
        base_var = tk.StringVar(value=f"0x{next_base:08X}")
        base_entry = ttk.Entry(dialog, textvariable=base_var, width=30)
        base_entry.grid(row=1, column=1, padx=10, pady=5)
        
        # Size
        ttk.Label(dialog, text="Size:").grid(row=2, column=0, sticky=tk.W, padx=10, pady=5)
        size_var = tk.StringVar(value="64KB")
        size_combo = ttk.Combobox(dialog, textvariable=size_var,
                                 values=["4KB", "16KB", "64KB", "256KB", "1MB", "16MB", "256MB", "1GB"],
                                 state="readonly", width=28)
        size_combo.grid(row=2, column=1, padx=10, pady=5)
        
        def on_ok():
            name = name_var.get().strip()
            if name:
                # Parse base address
                base_str = base_var.get().strip()
                try:
                    if base_str.startswith("0x") or base_str.startswith("0X"):
                        base = int(base_str, 16)
                    else:
                        base = int(base_str)
                except ValueError:
                    messagebox.showerror("Error", "Invalid base address")
                    return
                
                # Parse size
                size_map = {
                    "4KB": 0x1000,
                    "16KB": 0x4000,
                    "64KB": 0x10000,
                    "256KB": 0x40000,
                    "1MB": 0x100000,
                    "16MB": 0x1000000,
                    "256MB": 0x10000000,
                    "1GB": 0x40000000
                }
                size = size_map.get(size_var.get(), 0x10000)
                
                slave = self.project.add_slave(name, base=base, size=size)
                self.canvas.refresh()
                self.update_summary()
                self.set_status(f"Added slave: {name}")
            dialog.destroy()
        
        button_frame = ttk.Frame(dialog)
        button_frame.grid(row=3, column=0, columnspan=2, pady=20)
        ttk.Button(button_frame, text="OK", command=on_ok).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Cancel", command=dialog.destroy).pack(side=tk.LEFT)
    
    def delete_selected(self):
        """Delete selected node"""
        if self.canvas.selected_node:
            node_id = self.canvas.selected_node
            if messagebox.askyesno("Delete Node", f"Delete {node_id}?"):
                self.canvas.delete_node(node_id)
                self.update_summary()
                self.set_status(f"Deleted: {node_id}")
    
    def on_node_selected(self, node_id: str):
        """Handle node selection"""
        self.node_info_label.config(text=f"Selected: {node_id}")
        
        # Clear previous properties
        for widget in self.node_props_frame.winfo_children():
            widget.destroy()
        
        # Show node-specific properties
        if node_id.startswith('M'):
            self.show_master_properties(node_id)
        elif node_id.startswith('S'):
            self.show_slave_properties(node_id)
        
        # Switch to node tab
        self.prop_notebook.select(1)
    
    def show_master_properties(self, master_id: str):
        """Show master properties"""
        idx = int(master_id[1:])
        if 0 <= idx < len(self.project.masters):
            master = self.project.masters[idx]
            
            props_frame = ttk.LabelFrame(self.node_props_frame, text="Master Properties", padding=10)
            props_frame.pack(fill=tk.BOTH, expand=True)
            
            # Name
            ttk.Label(props_frame, text="Name:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
            ttk.Label(props_frame, text=master.name).grid(row=0, column=1, sticky=tk.W, padx=5, pady=2)
            
            # QoS
            if self.project.bus.qos:
                ttk.Label(props_frame, text="AWQoS:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
                ttk.Label(props_frame, text=str(master.qos_default.aw)).grid(row=1, column=1, sticky=tk.W, padx=5, pady=2)
                
                ttk.Label(props_frame, text="ARQoS:").grid(row=2, column=0, sticky=tk.W, padx=5, pady=2)
                ttk.Label(props_frame, text=str(master.qos_default.ar)).grid(row=2, column=1, sticky=tk.W, padx=5, pady=2)
    
    def show_slave_properties(self, slave_id: str):
        """Show slave properties"""
        idx = int(slave_id[1:])
        if 0 <= idx < len(self.project.slaves):
            slave = self.project.slaves[idx]
            
            props_frame = ttk.LabelFrame(self.node_props_frame, text="Slave Properties", padding=10)
            props_frame.pack(fill=tk.BOTH, expand=True)
            
            # Name
            ttk.Label(props_frame, text="Name:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
            ttk.Label(props_frame, text=slave.name).grid(row=0, column=1, sticky=tk.W, padx=5, pady=2)
            
            # Address
            ttk.Label(props_frame, text="Base Address:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
            ttk.Label(props_frame, text=f"0x{slave.base:08X}").grid(row=1, column=1, sticky=tk.W, padx=5, pady=2)
            
            ttk.Label(props_frame, text="Size:").grid(row=2, column=0, sticky=tk.W, padx=5, pady=2)
            ttk.Label(props_frame, text=f"{slave.size // 1024}KB").grid(row=2, column=1, sticky=tk.W, padx=5, pady=2)
            
            # Priority button for fixed arbitration
            if self.project.bus.arbitration == "fixed":
                ttk.Button(props_frame, text="Edit Priority...",
                         command=lambda: self.edit_slave_priority(slave)).grid(row=3, column=0, columnspan=2, pady=10)
    
    def edit_slave_priority(self, slave: SlaveNode):
        """Edit slave priority using drag-and-drop editor"""
        editor = PriorityEditor(self.root, slave, self.project)
        result = editor.wait()
        if result:
            self.canvas.refresh()
            self.set_status(f"Updated priority for {slave.name}")
    
    def on_edge_selected(self, from_node: str, to_node: str):
        """Handle edge selection"""
        self.edge_info_label.config(text=f"Selected: {from_node} → {to_node}")
        
        # Clear previous properties
        for widget in self.edge_props_frame.winfo_children():
            widget.destroy()
        
        # Show edge properties
        props_frame = ttk.LabelFrame(self.edge_props_frame, text="Edge Overrides", padding=10)
        props_frame.pack(fill=tk.BOTH, expand=True)
        
        ttk.Label(props_frame, text="QoS overrides not yet implemented").pack()
        
        # Switch to edge tab
        self.prop_notebook.select(2)
    
    def update_view_preferences(self):
        """Update view preferences"""
        self.project.preferences.show_qos = self.show_qos_var.get()
        self.project.preferences.show_priority = self.show_priority_var.get()
        self.project.preferences.show_cache = self.show_cache_var.get()
        self.project.preferences.show_prot = self.show_prot_var.get()
        self.project.preferences.show_region = self.show_region_var.get()
        self.canvas.refresh()
    
    def update_bus_config(self):
        """Update bus configuration from UI"""
        try:
            self.project.bus.addr_width = self.addr_width_var.get()
            self.project.bus.data_width = int(self.data_width_var.get())
            self.project.bus.id_width = self.id_width_var.get()
            self.project.bus.arbitration = self.arbitration_var.get()
            self.project.bus.qos = self.qos_var.get()
            self.project.bus.cache = self.cache_var.get()
            self.project.bus.prot = self.prot_var.get()
            self.project.bus.region = self.region_var.get()
            self.project.bus.qos_default.aw = self.default_awqos_var.get()
            self.project.bus.qos_default.ar = self.default_arqos_var.get()
            
            self.canvas.refresh()
            self.update_summary()
            self.set_status("Bus configuration updated")
        except Exception as e:
            messagebox.showerror("Error", f"Invalid configuration:\n{str(e)}")
    
    def edit_bus_config(self):
        """Edit bus configuration (placeholder)"""
        messagebox.showinfo("Bus Configuration", "Advanced bus configuration dialog")
    
    def edit_preferences(self):
        """Edit preferences (placeholder)"""
        messagebox.showinfo("Preferences", "Preferences dialog")
    
    def auto_layout(self):
        """Auto-arrange nodes"""
        self.canvas.auto_layout()
        self.set_status("Auto layout applied")
    
    def zoom_in(self):
        """Zoom in canvas"""
        # Placeholder for zoom functionality
        self.set_status("Zoom in")
    
    def zoom_out(self):
        """Zoom out canvas"""
        # Placeholder for zoom functionality
        self.set_status("Zoom out")
    
    def zoom_reset(self):
        """Reset zoom"""
        # Placeholder for zoom functionality
        self.set_status("Zoom reset")
    
    def generate_rtl(self):
        """Generate RTL"""
        self.logger.info("Starting RTL generation...")
        
        generator = Generator(self.project)
        
        # Validate first
        valid, errors = generator.validate_configuration()
        if not valid:
            error_msg = "Configuration errors:\n" + "\n".join(errors)
            self.logger.error(f"RTL validation failed: {error_msg}")
            messagebox.showerror("Validation Error", error_msg)
            return
        
        self.logger.info(f"Generating RTL for {len(self.project.masters)}M x {len(self.project.slaves)}S")
        
        # Generate
        success, message = generator.generate_rtl()
        
        if success:
            self.logger.info(f"RTL generation successful: {message}")
            messagebox.showinfo("RTL Generation", message)
            self.add_message(f"[SUCCESS] RTL Generated")
        else:
            self.logger.error(f"RTL generation failed: {message}")
            messagebox.showerror("RTL Generation Failed", message)
            self.add_message(f"[ERROR] RTL Generation Failed")
    
    def generate_vip(self):
        """Generate VIP"""
        self.logger.info("Starting VIP generation...")
        
        generator = Generator(self.project)
        
        # Validate first
        valid, errors = generator.validate_configuration()
        if not valid:
            error_msg = "Configuration errors:\n" + "\n".join(errors)
            self.logger.error(f"VIP validation failed: {error_msg}")
            messagebox.showerror("Validation Error", error_msg)
            return
        
        self.logger.info(f"Generating VIP for {len(self.project.masters)}M x {len(self.project.slaves)}S")
        
        # Generate
        success, message = generator.generate_vip()
        
        if success:
            self.logger.info(f"VIP generation successful: {message}")
            messagebox.showinfo("VIP Generation", message)
            self.add_message(f"[SUCCESS] VIP Generated")
        else:
            self.logger.error(f"VIP generation failed: {message}")
            messagebox.showerror("VIP Generation Failed", message)
            self.add_message(f"[ERROR] VIP Generation Failed")
    
    def validate_config(self):
        """Validate configuration"""
        generator = Generator(self.project)
        valid, errors = generator.validate_configuration()
        
        if valid:
            messagebox.showinfo("Validation", "Configuration is valid!")
            self.add_message("[OK] Configuration validated successfully")
        else:
            messagebox.showerror("Validation Error", 
                               "Configuration errors:\n" + "\n".join(errors))
            for error in errors:
                self.add_message(f"[ERROR] {error}")
    
    def show_help(self):
        """Show help"""
        help_text = """AMBA AXI4 RTL & VIP Generator v3

Based on gui_build.md specification:
• Per-channel QoS configuration (AWQoS/ARQoS)
• Priority drag-and-drop for fixed arbitration
• Add/Delete Masters and Slaves
• Data width: 8-1024 bits
• Address width: 8-64 bits
• Template Gallery with 8×8, 16×16, 32×32 configurations

Keyboard Shortcuts:
• Ctrl+N: New Project
• Ctrl+O: Open Project
• Ctrl+S: Save Project
• Ctrl+M: Add Master
• Ctrl+L: Add Slave (L for sLave)
• F5: Generate RTL
• F6: Generate VIP"""
        
        messagebox.showinfo("Help", help_text)
    
    def show_about(self):
        """Show about dialog"""
        about_text = """AMBA AXI4 RTL & VIP Generator
Version 3.0

Based on gui_build.md specification
Generates synthesizable RTL and UVM VIP
for AMBA AXI4 bus matrices

© 2024 - Educational Tool"""
        
        messagebox.showinfo("About", about_text)
    
    def update_summary(self):
        """Update summary text"""
        self.summary_text.delete(1.0, tk.END)
        
        summary = []
        summary.append("PROJECT SUMMARY")
        summary.append("=" * 30)
        summary.append(f"Name: {self.project.name}")
        summary.append("")
        summary.append("BUS CONFIGURATION")
        summary.append(f"Type: AXI4")
        summary.append(f"Width: {self.project.bus.data_width}-bit data")
        summary.append(f"       {self.project.bus.addr_width}-bit address")
        summary.append(f"ID Width: {self.project.bus.id_width}")
        summary.append(f"Arbitration: {self.project.bus.arbitration}")
        
        if self.project.bus.qos:
            summary.append(f"QoS: Enabled")
            summary.append(f"  Default: AW={self.project.bus.qos_default.aw}, AR={self.project.bus.qos_default.ar}")
        
        summary.append("")
        summary.append(f"MASTERS ({len(self.project.masters)})")
        for master in self.project.masters:
            summary.append(f"  M{master.m_index}: {master.name}")
        
        summary.append("")
        summary.append(f"SLAVES ({len(self.project.slaves)})")
        for slave in self.project.slaves:
            summary.append(f"  S{slave.s_index}: {slave.name}")
            summary.append(f"    0x{slave.base:08X} ({slave.size//1024}KB)")
        
        self.summary_text.insert(1.0, "\n".join(summary))
    
    def setup_log_viewer_tab(self):
        """Setup log viewer tab"""
        log_frame = ttk.Frame(self.prop_notebook)
        self.prop_notebook.add(log_frame, text="Logs")
        
        self.log_viewer = LogViewer(log_frame)
        self.log_viewer.pack(fill=tk.BOTH, expand=True)
    
    def setup_batch_manager_tab(self):
        """Setup batch manager tab"""
        batch_frame = ttk.Frame(self.prop_notebook)
        self.prop_notebook.add(batch_frame, text="Batch")
        
        self.batch_manager = BatchManager(batch_frame)
        self.batch_manager.pack(fill=tk.BOTH, expand=True)
    
    # Batch processing methods
    def start_batch_processor(self):
        """Start batch processor"""
        try:
            self.batch_processor.start()
            self.logger.info("Batch processor started")
            messagebox.showinfo("Success", "Batch processor started successfully")
        except Exception as e:
            self.logger.exception(f"Error starting batch processor: {e}")
            messagebox.showerror("Error", f"Failed to start batch processor: {e}")
    
    def stop_batch_processor(self):
        """Stop batch processor"""
        try:
            self.batch_processor.stop()
            self.logger.info("Batch processor stopped")
            messagebox.showinfo("Success", "Batch processor stopped successfully")
        except Exception as e:
            self.logger.exception(f"Error stopping batch processor: {e}")
            messagebox.showerror("Error", f"Failed to stop batch processor: {e}")
    
    def add_to_batch(self):
        """Add current project to batch queue"""
        try:
            if not self.project.masters or not self.project.slaves:
                messagebox.showwarning("Warning", "Project must have at least one master and one slave")
                return
            
            # Create batch task
            task_id = f"project_{self.project.name}_{int(time.time())}"
            task = BatchTask(
                task_id=task_id,
                task_type="both",  # Generate both RTL and VIP
                project=self.project,
                output_dir=f"batch_output/{task_id}",
                priority=1
            )
            
            self.batch_processor.add_task(task)
            self.logger.info(f"Added project to batch queue: {task_id}")
            messagebox.showinfo("Success", f"Project added to batch queue as {task_id}")
            
        except Exception as e:
            self.logger.exception(f"Error adding project to batch: {e}")
            messagebox.showerror("Error", f"Failed to add project to batch: {e}")
    
    def create_template_batch(self):
        """Create batch from templates"""
        try:
            # Create dialog to select templates
            from log_viewer import TemplateBatchDialog
            dialog = TemplateBatchDialog(self.root)
            
            if dialog.result:
                templates = dialog.result
                tasks = self.batch_processor.create_batch_from_templates(templates)
                self.logger.info(f"Created template batch with {len(tasks)} tasks")
                messagebox.showinfo("Success", f"Created batch with {len(tasks)} tasks")
            
        except Exception as e:
            self.logger.exception(f"Error creating template batch: {e}")
            messagebox.showerror("Error", f"Failed to create template batch: {e}")
    
    def show_batch_manager(self):
        """Show batch manager tab"""
        # Switch to batch manager tab
        for i in range(self.prop_notebook.index("end")):
            if self.prop_notebook.tab(i, "text") == "Batch":
                self.prop_notebook.select(i)
                break
    
    def show_log_viewer(self):
        """Show log viewer tab"""
        # Switch to log viewer tab
        for i in range(self.prop_notebook.index("end")):
            if self.prop_notebook.tab(i, "text") == "Logs":
                self.prop_notebook.select(i)
                break
    
    def on_closing(self):
        """Handle application closing"""
        try:
            self.logger.info("Application closing...")
            
            # Stop batch processor
            if hasattr(self, 'batch_processor'):
                self.batch_processor.stop()
            
            # Cleanup log viewer
            if hasattr(self, 'log_viewer'):
                self.log_viewer.destroy()
            
            self.root.destroy()
            
        except Exception as e:
            self.logger.exception(f"Error during cleanup: {e}")
            self.root.destroy()

    def add_message(self, message: str):
        """Add message to messages panel"""
        self.messages_text.insert(tk.END, message + "\n")
        self.messages_text.see(tk.END)
        self.logger.info(f"GUI Message: {message}")
    
    def set_status(self, message: str):
        """Set status bar message"""
        self.status_bar.config(text=message)
    
    def run(self):
        """Run the application"""
        self.root.mainloop()

def main():
    """Main entry point"""
    app = AXI4GeneratorGUI()
    app.run()

if __name__ == "__main__":
    main()