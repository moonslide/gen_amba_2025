#!/usr/bin/env python3
"""
Template Gallery for quick project setup
Provides pre-configured templates: 8x8, 16x16, 32x32 AXI, and AHB-Lite
Based on gui_build.md specification
"""

import tkinter as tk
from tkinter import ttk
from bus_config import Project, BusConfig, MasterNode, SlaveNode, QoSConfig

class TemplateGallery:
    """Template gallery dialog for quick project setup"""
    
    def __init__(self, parent):
        self.parent = parent
        self.selected_template = None
        
        # Create dialog
        self.dialog = tk.Toplevel(parent)
        self.dialog.title("Template Gallery - Quick Start")
        self.dialog.geometry("800x600")
        self.dialog.transient(parent)
        self.dialog.grab_set()
        
        # Center dialog
        self.dialog.update_idletasks()
        x = (self.dialog.winfo_screenwidth() // 2) - 400
        y = (self.dialog.winfo_screenheight() // 2) - 300
        self.dialog.geometry(f"800x600+{x}+{y}")
        
        self.create_ui()
    
    def create_ui(self):
        """Create the template gallery UI"""
        # Title
        title_frame = ttk.Frame(self.dialog)
        title_frame.pack(fill=tk.X, padx=20, pady=10)
        
        ttk.Label(title_frame, text="Select a Template", 
                 font=('Arial', 16, 'bold')).pack()
        ttk.Label(title_frame, text="Choose a pre-configured bus matrix template to start your project",
                 font=('Arial', 10)).pack()
        
        # Template grid
        template_frame = ttk.Frame(self.dialog)
        template_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Create template cards
        templates = [
            {
                'name': 'AXI 8×8',
                'desc': '8 Masters × 8 Slaves\nMedium complexity\nQoS enabled',
                'icon': '8×8',
                'color': '#4CAF50',
                'template': 'axi_8x8'
            },
            {
                'name': 'AXI 16×16',
                'desc': '16 Masters × 16 Slaves\nHigh complexity\nEnterprise scale',
                'icon': '16×16',
                'color': '#2196F3',
                'template': 'axi_16x16'
            },
            {
                'name': 'AXI 32×32',
                'desc': '32 Masters × 32 Slaves\nUltra-high complexity\nData center scale',
                'icon': '32×32',
                'color': '#9C27B0',
                'template': 'axi_32x32'
            },
            {
                'name': 'AHB-Lite',
                'desc': 'Simple AHB bus\nSingle master\nLegacy compatible',
                'icon': 'AHB',
                'color': '#FF9800',
                'template': 'ahb_lite'
            }
        ]
        
        # Create 2x2 grid
        for i, template in enumerate(templates):
            row = i // 2
            col = i % 2
            
            # Create card frame
            card = tk.Frame(template_frame, relief=tk.RAISED, borderwidth=2, bg='white')
            card.grid(row=row, column=col, padx=20, pady=20, sticky="nsew")
            
            # Configure grid weights
            template_frame.grid_rowconfigure(row, weight=1)
            template_frame.grid_columnconfigure(col, weight=1)
            
            # Icon/badge
            icon_label = tk.Label(card, text=template['icon'], 
                                font=('Arial', 24, 'bold'),
                                fg=template['color'], bg='white')
            icon_label.pack(pady=20)
            
            # Name
            name_label = tk.Label(card, text=template['name'],
                                font=('Arial', 14, 'bold'),
                                bg='white')
            name_label.pack()
            
            # Description
            desc_label = tk.Label(card, text=template['desc'],
                                font=('Arial', 10),
                                justify=tk.CENTER, bg='white')
            desc_label.pack(pady=10)
            
            # Select button
            btn = ttk.Button(card, text="Select This Template",
                           command=lambda t=template['template']: self.select_template(t))
            btn.pack(pady=10)
            
            # Bind click to entire card
            for widget in [card, icon_label, name_label, desc_label]:
                widget.bind('<Button-1>', lambda e, t=template['template']: self.select_template(t))
        
        # Bottom buttons
        button_frame = ttk.Frame(self.dialog)
        button_frame.pack(fill=tk.X, padx=20, pady=10)
        
        ttk.Button(button_frame, text="Cancel", command=self.cancel).pack(side=tk.RIGHT, padx=5)
        ttk.Button(button_frame, text="Start Blank Project", command=self.blank_project).pack(side=tk.LEFT)
    
    def select_template(self, template_name: str):
        """Select a template and close dialog"""
        self.selected_template = template_name
        self.dialog.destroy()
    
    def blank_project(self):
        """Start with blank project"""
        self.selected_template = 'blank'
        self.dialog.destroy()
    
    def cancel(self):
        """Cancel template selection"""
        self.selected_template = None
        self.dialog.destroy()
    
    def wait(self):
        """Wait for dialog to close and return selected template"""
        self.dialog.wait_window()
        return self.selected_template
    
    @staticmethod
    def create_template_project(template_name: str) -> Project:
        """Create a project from template"""
        if template_name == 'axi_8x8':
            return TemplateGallery.create_axi_8x8()
        elif template_name == 'axi_16x16':
            return TemplateGallery.create_axi_16x16()
        elif template_name == 'axi_32x32':
            return TemplateGallery.create_axi_32x32()
        elif template_name == 'ahb_lite':
            return TemplateGallery.create_ahb_lite()
        else:
            return TemplateGallery.create_blank()
    
    @staticmethod
    def create_blank() -> Project:
        """Create blank project with minimal setup"""
        project = Project(name="blank_project")
        # Add one master and one slave as minimum
        project.add_master("Master0")
        project.add_slave("Slave0", base=0x00000000, size=0x10000)
        return project
    
    @staticmethod
    def create_axi_8x8() -> Project:
        """Create 8x8 AXI template"""
        project = Project(name="axi_8x8_template")
        
        # Configure bus
        project.bus = BusConfig(
            addr_width=32,
            data_width=64,
            id_width=4,
            user_width=0,
            qos=True,
            cache=True,
            prot=True,
            region=True,
            qos_default=QoSConfig(aw=0, ar=0),
            arbitration="qos"
        )
        
        # Add 8 masters
        master_names = ["CPU0", "CPU1", "GPU", "DMA0", "DMA1", "USB", "ETH", "DSP"]
        for i, name in enumerate(master_names):
            master = project.add_master(name)
            master.qos_default = QoSConfig(aw=i % 4, ar=i % 4)
            master.outstanding = {"read": 8, "write": 8}
            # Position in grid
            master.x = 100
            master.y = 50 + i * 70
        
        # Add 8 slaves
        slave_configs = [
            ("DDR0", 0x00000000, 0x40000000),  # 1GB
            ("DDR1", 0x40000000, 0x40000000),  # 1GB
            ("SRAM", 0x80000000, 0x00100000),  # 1MB
            ("ROM",  0x90000000, 0x00010000),  # 64KB
            ("UART", 0xA0000000, 0x00001000),  # 4KB
            ("GPIO", 0xA0010000, 0x00001000),  # 4KB
            ("SPI",  0xA0020000, 0x00001000),  # 4KB
            ("I2C",  0xA0030000, 0x00001000),  # 4KB
        ]
        
        for i, (name, base, size) in enumerate(slave_configs):
            slave = SlaveNode(
                name=name,
                s_index=i,
                base=base,
                size=size,
                x=600,
                y=50 + i * 70
            )
            if "DDR" in name:
                slave.attributes = {"cacheable": True, "bufferable": True}
            else:
                slave.attributes = {"cacheable": False, "bufferable": False}
            
            # Set priority for fixed arbitration
            slave.priority = {"type": "fixed", "order": [f"M{j}" for j in range(8)]}
            project.slaves.append(slave)
        
        return project
    
    @staticmethod
    def create_axi_16x16() -> Project:
        """Create 16x16 AXI template"""
        project = Project(name="axi_16x16_template")
        
        # Configure bus for larger system
        project.bus = BusConfig(
            addr_width=40,  # 1TB address space
            data_width=128,  # Wider data bus
            id_width=6,
            user_width=4,
            qos=True,
            cache=True,
            prot=True,
            region=True,
            qos_default=QoSConfig(aw=1, ar=1),
            arbitration="qos"
        )
        
        # Add 16 masters
        for i in range(16):
            master = project.add_master(f"M{i}")
            master.qos_default = QoSConfig(aw=i % 8, ar=i % 8)
            master.outstanding = {"read": 16, "write": 16}
            # Position in grid (4 columns)
            master.x = 50 + (i % 4) * 100
            master.y = 50 + (i // 4) * 60
        
        # Add 16 slaves
        base_addr = 0x00000000
        for i in range(16):
            size = 0x10000000 if i < 4 else 0x1000000  # First 4 are large memories
            slave = project.add_slave(f"S{i}", base=base_addr, size=size)
            # Position in grid (4 columns)
            slave.x = 550 + (i % 4) * 100
            slave.y = 50 + (i // 4) * 60
            base_addr += size
        
        return project
    
    @staticmethod
    def create_axi_32x32() -> Project:
        """Create 32x32 AXI template - Ultra-high complexity"""
        project = Project(name="axi_32x32_template")
        
        # Configure bus for ultra-large system
        project.bus = BusConfig(
            addr_width=48,  # 256TB address space
            data_width=256,  # Very wide data bus
            id_width=8,
            user_width=8,
            qos=True,
            cache=True,
            prot=True,
            region=True,
            qos_default=QoSConfig(aw=2, ar=2),
            arbitration="qos"
        )
        
        # Add 32 masters in compact grid
        for i in range(32):
            master = project.add_master(f"M{i}")
            master.qos_default = QoSConfig(aw=i % 16, ar=i % 16)
            master.outstanding = {"read": 32, "write": 32}
            # Position in grid (8 columns)
            master.x = 30 + (i % 8) * 60
            master.y = 30 + (i // 8) * 50
        
        # Add 32 slaves in compact grid
        base_addr = 0x00000000
        for i in range(32):
            size = 0x100000000 if i < 8 else 0x10000000  # First 8 are very large
            slave = project.add_slave(f"S{i}", base=base_addr, size=size)
            # Position in grid (8 columns)
            slave.x = 550 + (i % 8) * 60
            slave.y = 30 + (i // 8) * 50
            base_addr += size
        
        return project
    
    @staticmethod
    def create_ahb_lite() -> Project:
        """Create AHB-Lite template"""
        project = Project(name="ahb_lite_template")
        
        # Configure bus for AHB-Lite (single master)
        project.bus = BusConfig(
            addr_width=32,
            data_width=32,  # Typical AHB width
            id_width=0,  # No ID in AHB
            user_width=0,
            qos=False,  # No QoS in AHB
            cache=False,  # Simplified
            prot=True,  # HPROT exists
            region=False,  # No regions in AHB
            arbitration="none"  # Single master
        )
        
        # Add single master (AHB-Lite requirement)
        master = project.add_master("CPU")
        master.x = 100
        master.y = 200
        
        # Add typical AHB slaves
        slave_configs = [
            ("ROM",  0x00000000, 0x00010000),  # 64KB
            ("RAM",  0x20000000, 0x00010000),  # 64KB
            ("APB_Bridge", 0x40000000, 0x00100000),  # 1MB APB space
            ("GPIO", 0x50000000, 0x00001000),  # 4KB
        ]
        
        for i, (name, base, size) in enumerate(slave_configs):
            slave = project.add_slave(name, base=base, size=size)
            slave.x = 400
            slave.y = 100 + i * 80
        
        return project