#!/usr/bin/env python3
"""
Create realistic GUI mockups for user guide demonstrations
This creates visual step-by-step screenshots showing bus matrix setup process
"""

import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.patches import FancyBboxPatch, Rectangle, Circle
import matplotlib.image as mpimg
import numpy as np
from datetime import datetime

class GUIMockupGenerator:
    """Generate realistic GUI mockups for documentation"""
    
    def __init__(self):
        self.fig_width = 12
        self.fig_height = 9
        self.colors = {
            'window_bg': '#f0f0f0',
            'menu_bg': '#e8e8e8',
            'toolbar_bg': '#d0d0d0',
            'canvas_bg': '#ffffff',
            'panel_bg': '#f8f8f8',
            'button_bg': '#e0e0e0',
            'button_hover': '#c0c0ff',
            'master_color': '#4CAF50',
            'slave_color': '#2196F3',
            'connection_color': '#FF5722'
        }
        
    def create_main_window_mockup(self, filename="gui_main_window.png"):
        """Create main GUI window mockup"""
        fig, ax = plt.subplots(1, 1, figsize=(self.fig_width, self.fig_height))
        ax.set_xlim(0, 1200)
        ax.set_ylim(0, 900)
        ax.axis('off')
        
        # Window frame
        window_frame = Rectangle((0, 0), 1200, 900, 
                               facecolor=self.colors['window_bg'], 
                               edgecolor='black', linewidth=2)
        ax.add_patch(window_frame)
        
        # Title bar
        title_bar = Rectangle((0, 860), 1200, 40,
                            facecolor='#2c3e50', edgecolor='black')
        ax.add_patch(title_bar)
        ax.text(10, 880, "AMBA Bus Matrix Configuration Tool v1.0", 
               color='white', fontsize=12, fontweight='bold')
        
        # Window controls
        for i, color in enumerate(['#ff5f56', '#ffbd2e', '#27ca3f']):
            circle = Circle((1160 - i*25, 880), 8, facecolor=color, edgecolor='gray')
            ax.add_patch(circle)
        
        # Menu bar
        menu_bar = Rectangle((0, 820), 1200, 40,
                           facecolor=self.colors['menu_bg'], edgecolor='gray')
        ax.add_patch(menu_bar)
        
        # Menu items
        menu_items = ['File', 'Edit', 'View', 'Tools', 'Generate', 'Help']
        x_pos = 20
        for item in menu_items:
            ax.text(x_pos, 840, item, fontsize=11, va='center')
            x_pos += len(item) * 10 + 20
        
        # Toolbar
        toolbar = Rectangle((0, 770), 1200, 50,
                          facecolor=self.colors['toolbar_bg'], edgecolor='gray')
        ax.add_patch(toolbar)
        
        # Toolbar buttons
        toolbar_buttons = [
            ('New', 20), ('Open', 80), ('Save', 140), ('|', 200),
            ('Add Master', 230), ('Add Slave', 320), ('Connect', 410), ('|', 480),
            ('Validate', 510), ('Generate RTL', 600), ('Generate VIP', 720)
        ]
        
        for btn_text, x_pos in toolbar_buttons:
            if btn_text == '|':
                ax.plot([x_pos, x_pos], [775, 815], 'gray', linewidth=1)
            else:
                if btn_text in ['Add Master', 'Add Slave']:
                    btn_color = self.colors['button_hover']
                else:
                    btn_color = self.colors['button_bg']
                    
                btn_width = len(btn_text) * 8 + 20
                btn = Rectangle((x_pos, 780), btn_width, 30,
                              facecolor=btn_color, edgecolor='gray')
                ax.add_patch(btn)
                ax.text(x_pos + btn_width/2, 795, btn_text, 
                       ha='center', va='center', fontsize=9)
        
        # Left panel (Component Library)
        left_panel = Rectangle((10, 10), 200, 750,
                             facecolor=self.colors['panel_bg'], edgecolor='gray')
        ax.add_patch(left_panel)
        ax.text(110, 740, "Component Library", ha='center', fontweight='bold', fontsize=11)
        
        # Component categories
        categories = [
            ('Masters', 700, self.colors['master_color']),
            ('Slaves', 650, self.colors['slave_color']),
            ('Bridges', 600, '#FF9800'),
            ('Monitors', 550, '#9C27B0')
        ]
        
        for cat_name, y_pos, color in categories:
            cat_rect = Rectangle((20, y_pos-15), 180, 30,
                               facecolor=color, alpha=0.3, edgecolor=color)
            ax.add_patch(cat_rect)
            ax.text(110, y_pos, cat_name, ha='center', va='center', fontweight='bold')
        
        # Main canvas
        canvas = Rectangle((220, 10), 760, 750,
                         facecolor=self.colors['canvas_bg'], edgecolor='gray', linewidth=2)
        ax.add_patch(canvas)
        ax.text(600, 740, "Design Canvas", ha='center', fontweight='bold', fontsize=14)
        
        # Grid on canvas
        for i in range(25, 760, 25):
            ax.plot([220+i, 220+i], [10, 760], color='lightgray', linewidth=0.5, alpha=0.5)
        for i in range(25, 750, 25):
            ax.plot([220, 980], [10+i, 10+i], color='lightgray', linewidth=0.5, alpha=0.5)
        
        # Right panel (Properties)
        right_panel = Rectangle((990, 10), 200, 750,
                              facecolor=self.colors['panel_bg'], edgecolor='gray')
        ax.add_patch(right_panel)
        ax.text(1090, 740, "Properties Panel", ha='center', fontweight='bold', fontsize=11)
        
        # Properties content
        ax.text(1000, 700, "Selected: None", fontsize=10)
        ax.text(1000, 680, "Type:", fontsize=10)
        ax.text(1000, 660, "Name:", fontsize=10)
        ax.text(1000, 640, "Configuration:", fontsize=10)
        
        # Status bar
        status_bar = Rectangle((0, 0), 1200, 30,
                             facecolor=self.colors['menu_bg'], edgecolor='gray')
        ax.add_patch(status_bar)
        ax.text(10, 15, "Ready - Click 'Add Master' to start building your bus matrix", 
               fontsize=10, va='center')
        ax.text(1100, 15, "AXI4 Mode", fontsize=10, va='center')
        
        plt.tight_layout()
        plt.savefig(filename, dpi=150, bbox_inches='tight')
        plt.close()
        print(f"Created: {filename}")
        
    def create_add_master_dialog(self, filename="gui_add_master.png"):
        """Create add master dialog mockup"""
        fig, ax = plt.subplots(1, 1, figsize=(10, 8))
        ax.set_xlim(0, 1000)
        ax.set_ylim(0, 800)
        ax.axis('off')
        
        # Background (dimmed main window)
        bg = Rectangle((0, 0), 1000, 800, facecolor='gray', alpha=0.3)
        ax.add_patch(bg)
        
        # Dialog box
        dialog = Rectangle((200, 200), 600, 400,
                         facecolor='white', edgecolor='black', linewidth=2)
        ax.add_patch(dialog)
        
        # Dialog title bar
        title_bar = Rectangle((200, 560), 600, 40,
                            facecolor='#2c3e50', edgecolor='black')
        ax.add_patch(title_bar)
        ax.text(210, 580, "Add Master Configuration", color='white', 
               fontsize=12, fontweight='bold')
        
        # Close button
        close_btn = Rectangle((760, 570), 30, 20, facecolor='#e74c3c')
        ax.add_patch(close_btn)
        ax.text(775, 580, "×", color='white', fontsize=14, ha='center', va='center')
        
        # Form fields
        fields = [
            ("Master Name:", "CPU_0", 500),
            ("ID Width (bits):", "4", 450),
            ("Priority:", "2", 400),
            ("Data Width:", "64", 350),
            ("Address Width:", "32", 300)
        ]
        
        for label, value, y_pos in fields:
            ax.text(220, y_pos, label, fontsize=11, fontweight='bold')
            
            # Input field
            input_field = Rectangle((350, y_pos-10), 200, 25,
                                  facecolor='white', edgecolor='gray')
            ax.add_patch(input_field)
            ax.text(360, y_pos, value, fontsize=10, va='center')
        
        # Checkboxes
        checkboxes = [
            ("Enable QoS Support", True, 240),
            ("Enable Exclusive Access", True, 220)
        ]
        
        for label, checked, y_pos in checkboxes:
            # Checkbox
            checkbox = Rectangle((220, y_pos-5), 15, 15,
                               facecolor='white', edgecolor='gray')
            ax.add_patch(checkbox)
            if checked:
                ax.text(227, y_pos+2, "✓", fontsize=12, ha='center', va='center', color='green')
            
            ax.text(245, y_pos, label, fontsize=11)
        
        # Buttons
        cancel_btn = Rectangle((450, 210), 80, 30,
                             facecolor='#95a5a6', edgecolor='gray')
        ax.add_patch(cancel_btn)
        ax.text(490, 225, "Cancel", ha='center', va='center', fontsize=10)
        
        ok_btn = Rectangle((550, 210), 80, 30,
                         facecolor='#27ae60', edgecolor='gray')
        ax.add_patch(ok_btn)
        ax.text(590, 225, "Add Master", ha='center', va='center', 
               fontsize=10, color='white', fontweight='bold')
        
        plt.tight_layout()
        plt.savefig(filename, dpi=150, bbox_inches='tight')
        plt.close()
        print(f"Created: {filename}")
        
    def create_design_with_components(self, filename="gui_design_canvas.png"):
        """Create design canvas with masters and slaves"""
        fig, ax = plt.subplots(1, 1, figsize=(self.fig_width, self.fig_height))
        ax.set_xlim(0, 1200)
        ax.set_ylim(0, 900)
        ax.axis('off')
        
        # Main window background (simplified)
        window_frame = Rectangle((0, 0), 1200, 900, 
                               facecolor=self.colors['window_bg'], 
                               edgecolor='black', linewidth=1)
        ax.add_patch(window_frame)
        
        # Canvas area
        canvas = Rectangle((220, 60), 760, 700,
                         facecolor=self.colors['canvas_bg'], edgecolor='gray', linewidth=2)
        ax.add_patch(canvas)
        
        # Grid
        for i in range(25, 760, 25):
            ax.plot([220+i, 220+i], [60, 760], color='lightgray', linewidth=0.5, alpha=0.5)
        for i in range(25, 700, 25):
            ax.plot([220, 980], [60+i, 60+i], color='lightgray', linewidth=0.5, alpha=0.5)
        
        # Masters
        masters = [
            ("CPU_0", 280, 600, self.colors['master_color']),
            ("DMA_0", 280, 450, self.colors['master_color'])
        ]
        
        for name, x, y, color in masters:
            # Master box
            master_box = FancyBboxPatch((x, y), 120, 80,
                                      boxstyle="round,pad=5",
                                      facecolor=color, edgecolor='black', linewidth=2)
            ax.add_patch(master_box)
            ax.text(x+60, y+50, name, ha='center', va='center', 
                   fontsize=12, fontweight='bold', color='white')
            ax.text(x+60, y+30, "Master", ha='center', va='center', 
                   fontsize=10, color='white')
            
            # Output port
            port = Circle((x+120, y+40), 8, facecolor='red', edgecolor='black')
            ax.add_patch(port)
        
        # Slaves
        slaves = [
            ("DDR_Memory", 700, 650, "0x00000000", "1GB"),
            ("SRAM_Cache", 700, 500, "0x40000000", "256MB"),
            ("Peripherals", 700, 350, "0x50000000", "256MB")
        ]
        
        for name, x, y, base_addr, size in slaves:
            # Slave box
            slave_box = FancyBboxPatch((x, y), 140, 100,
                                     boxstyle="round,pad=5",
                                     facecolor=self.colors['slave_color'], 
                                     edgecolor='black', linewidth=2)
            ax.add_patch(slave_box)
            ax.text(x+70, y+70, name, ha='center', va='center', 
                   fontsize=11, fontweight='bold', color='white')
            ax.text(x+70, y+50, "Slave", ha='center', va='center', 
                   fontsize=9, color='white')
            ax.text(x+70, y+35, base_addr, ha='center', va='center', 
                   fontsize=8, color='white')
            ax.text(x+70, y+20, size, ha='center', va='center', 
                   fontsize=8, color='white')
            
            # Input port
            port = Circle((x, y+50), 8, facecolor='blue', edgecolor='black')
            ax.add_patch(port)
        
        # Connections
        connections = [
            # CPU_0 to all slaves
            ((400, 640), (700, 700)),  # CPU_0 to DDR
            ((400, 640), (700, 550)),  # CPU_0 to SRAM
            ((400, 640), (700, 400)),  # CPU_0 to Peripherals
            # DMA_0 to DDR and SRAM only
            ((400, 490), (700, 700)),  # DMA_0 to DDR
            ((400, 490), (700, 550)),  # DMA_0 to SRAM
        ]
        
        for (x1, y1), (x2, y2) in connections:
            # Connection line
            ax.plot([x1, x2], [y1, y2], color=self.colors['connection_color'], 
                   linewidth=3, alpha=0.7)
            # Arrow
            dx, dy = x2-x1, y2-y1
            length = np.sqrt(dx*dx + dy*dy)
            dx, dy = dx/length, dy/length
            ax.arrow(x2-20*dx, y2-20*dy, 15*dx, 15*dy,
                    head_width=8, head_length=8, fc=self.colors['connection_color'], 
                    ec=self.colors['connection_color'])
        
        # Title
        ax.text(600, 800, "Bus Matrix Design: 2 Masters × 3 Slaves", 
               ha='center', fontsize=16, fontweight='bold')
        ax.text(600, 780, "CPU and DMA connected to Memory and Peripherals", 
               ha='center', fontsize=12, style='italic')
        
        # Properties panel (simplified)
        right_panel = Rectangle((990, 60), 200, 700,
                              facecolor=self.colors['panel_bg'], edgecolor='gray')
        ax.add_patch(right_panel)
        ax.text(1090, 740, "Properties", ha='center', fontweight='bold', fontsize=12)
        
        # Show selected component
        ax.text(1000, 700, "Selected: CPU_0", fontsize=10, fontweight='bold')
        ax.text(1000, 680, "Type: Master", fontsize=10)
        ax.text(1000, 660, "ID Width: 4 bits", fontsize=10)
        ax.text(1000, 640, "Priority: 2", fontsize=10)
        ax.text(1000, 620, "QoS: Enabled", fontsize=10)
        ax.text(1000, 600, "Exclusive: Enabled", fontsize=10)
        
        # Status
        ax.text(10, 20, "Design validated ✓ - Ready to generate RTL", 
               fontsize=12, color='green', fontweight='bold')
        
        plt.tight_layout()
        plt.savefig(filename, dpi=150, bbox_inches='tight')
        plt.close()
        print(f"Created: {filename}")
        
    def create_rtl_generation_dialog(self, filename="gui_rtl_generation.png"):
        """Create RTL generation dialog"""
        fig, ax = plt.subplots(1, 1, figsize=(12, 9))
        ax.set_xlim(0, 1200)
        ax.set_ylim(0, 900)
        ax.axis('off')
        
        # Background (dimmed)
        bg = Rectangle((0, 0), 1200, 900, facecolor='gray', alpha=0.3)
        ax.add_patch(bg)
        
        # Dialog box
        dialog = Rectangle((200, 150), 800, 600,
                         facecolor='white', edgecolor='black', linewidth=2)
        ax.add_patch(dialog)
        
        # Title bar
        title_bar = Rectangle((200, 710), 800, 40,
                            facecolor='#2c3e50', edgecolor='black')
        ax.add_patch(title_bar)
        ax.text(210, 730, "Generate RTL - Bus Matrix Configuration", 
               color='white', fontsize=14, fontweight='bold')
        
        # Configuration summary
        ax.text(220, 680, "Configuration Summary:", fontsize=12, fontweight='bold')
        summary_text = [
            "• Bus Type: AXI4",
            "• Data Width: 64 bits",
            "• Address Width: 32 bits", 
            "• Masters: 2 (CPU_0, DMA_0)",
            "• Slaves: 3 (DDR_Memory, SRAM_Cache, Peripherals)",
            "• Connections: 5 total"
        ]
        
        y_pos = 650
        for line in summary_text:
            ax.text(240, y_pos, line, fontsize=11)
            y_pos -= 25
        
        # Output directory
        ax.text(220, 500, "Output Directory:", fontsize=12, fontweight='bold')
        output_field = Rectangle((220, 470), 500, 30,
                               facecolor='white', edgecolor='gray', linewidth=1)
        ax.add_patch(output_field)
        ax.text(230, 485, "/home/user/project/output_rtl/", fontsize=11, va='center')
        
        browse_btn = Rectangle((730, 470), 80, 30,
                             facecolor=self.colors['button_bg'], edgecolor='gray')
        ax.add_patch(browse_btn)
        ax.text(770, 485, "Browse...", ha='center', va='center', fontsize=10)
        
        # Generation options
        ax.text(220, 430, "Generation Options:", fontsize=12, fontweight='bold')
        
        options = [
            ("Generate Testbench", True, 400),
            ("Include Timing Constraints", True, 380),
            ("Generate Documentation", False, 360),
            ("Optimize for Area", False, 340),
            ("Optimize for Speed", True, 320)
        ]
        
        for label, checked, y_pos in options:
            checkbox = Rectangle((230, y_pos-5), 15, 15,
                               facecolor='white', edgecolor='gray')
            ax.add_patch(checkbox)
            if checked:
                ax.text(237, y_pos+2, "✓", fontsize=12, ha='center', va='center', color='green')
            
            ax.text(255, y_pos, label, fontsize=11)
        
        # Files to be generated
        ax.text(220, 280, "Files to be Generated:", fontsize=12, fontweight='bold')
        
        files = [
            "axi4_interconnect_m2s3.v",
            "axi4_address_decoder.v", 
            "axi4_arbiter.v",
            "axi4_crossbar.v",
            "tb_axi4_interconnect.v",
            "timing_constraints.sdc"
        ]
        
        y_pos = 250
        for file in files:
            ax.text(240, y_pos, f"✓ {file}", fontsize=10, color='green')
            y_pos -= 20
        
        # Progress bar (showing generation in progress)
        ax.text(220, 120, "Generation Progress:", fontsize=12, fontweight='bold')
        
        progress_bg = Rectangle((220, 90), 500, 20,
                              facecolor='white', edgecolor='gray')
        ax.add_patch(progress_bg)
        
        progress_fill = Rectangle((220, 90), 350, 20,  # 70% complete
                                facecolor='#4CAF50', edgecolor='gray')
        ax.add_patch(progress_fill)
        
        ax.text(470, 100, "70% Complete - Generating arbiter...", 
               ha='center', va='center', fontsize=10, fontweight='bold')
        
        # Buttons
        cancel_btn = Rectangle((650, 170), 80, 35,
                             facecolor='#95a5a6', edgecolor='gray')
        ax.add_patch(cancel_btn)
        ax.text(690, 187, "Cancel", ha='center', va='center', fontsize=11)
        
        generate_btn = Rectangle((750, 170), 100, 35,
                               facecolor='#27ae60', edgecolor='gray')
        ax.add_patch(generate_btn)
        ax.text(800, 187, "Generate RTL", ha='center', va='center', 
               fontsize=11, color='white', fontweight='bold')
        
        plt.tight_layout()
        plt.savefig(filename, dpi=150, bbox_inches='tight')
        plt.close()
        print(f"Created: {filename}")
        
    def create_file_output_view(self, filename="gui_file_output.png"):
        """Create file browser showing generated outputs"""
        fig, ax = plt.subplots(1, 1, figsize=(12, 8))
        ax.set_xlim(0, 1200)
        ax.set_ylim(0, 800)
        ax.axis('off')
        
        # File browser window
        window = Rectangle((50, 50), 1100, 700,
                         facecolor='white', edgecolor='black', linewidth=2)
        ax.add_patch(window)
        
        # Title bar
        title_bar = Rectangle((50, 720), 1100, 30,
                            facecolor='#2c3e50', edgecolor='black')
        ax.add_patch(title_bar)
        ax.text(60, 735, "Generated Files - /home/user/project/output_rtl/", 
               color='white', fontsize=12, fontweight='bold')
        
        # Toolbar
        toolbar = Rectangle((50, 680), 1100, 40,
                          facecolor='#f0f0f0', edgecolor='gray')
        ax.add_patch(toolbar)
        
        # Address bar
        addr_bar = Rectangle((200, 690), 800, 20,
                           facecolor='white', edgecolor='gray')
        ax.add_patch(addr_bar)
        ax.text(210, 700, "/home/user/project/output_rtl/", fontsize=10, va='center')
        
        # File list header
        header = Rectangle((50, 640), 1100, 30,
                         facecolor='#e0e0e0', edgecolor='gray')
        ax.add_patch(header)
        ax.text(70, 655, "Name", fontsize=11, fontweight='bold')
        ax.text(400, 655, "Size", fontsize=11, fontweight='bold')
        ax.text(500, 655, "Type", fontsize=11, fontweight='bold')
        ax.text(650, 655, "Modified", fontsize=11, fontweight='bold')
        
        # Generated files
        files = [
            ("📁 rtl/", "-", "Folder", "Today 14:32"),
            ("📁 tb/", "-", "Folder", "Today 14:32"),
            ("📁 docs/", "-", "Folder", "Today 14:32"),
            ("📄 axi4_interconnect_m2s3.v", "15.2 KB", "Verilog", "Today 14:32"),
            ("📄 axi4_address_decoder.v", "8.7 KB", "Verilog", "Today 14:32"),
            ("📄 axi4_arbiter.v", "12.4 KB", "Verilog", "Today 14:32"),
            ("📄 axi4_crossbar.v", "18.9 KB", "Verilog", "Today 14:32"),
            ("📄 tb_axi4_interconnect.v", "6.3 KB", "Verilog", "Today 14:32"),
            ("📄 timing_constraints.sdc", "2.1 KB", "SDC", "Today 14:32"),
            ("📄 README.txt", "1.8 KB", "Text", "Today 14:32"),
            ("📄 build_script.tcl", "3.2 KB", "TCL", "Today 14:32")
        ]
        
        y_pos = 610
        for i, (name, size, ftype, modified) in enumerate(files):
            # Alternating row colors
            if i % 2 == 0:
                row_bg = Rectangle((50, y_pos-10), 1100, 25,
                                 facecolor='#f8f8f8', edgecolor='none')
                ax.add_patch(row_bg)
            
            ax.text(70, y_pos, name, fontsize=10)
            ax.text(400, y_pos, size, fontsize=10)
            ax.text(500, y_pos, ftype, fontsize=10)
            ax.text(650, y_pos, modified, fontsize=10)
            y_pos -= 25
        
        # Status bar
        status_bar = Rectangle((50, 50), 1100, 30,
                             facecolor='#f0f0f0', edgecolor='gray')
        ax.add_patch(status_bar)
        ax.text(60, 65, "RTL Generation Complete ✓ - 11 files created (68.5 KB total)", 
               fontsize=11, color='green', fontweight='bold')
        
        # Highlight key files
        key_files_rect = Rectangle((60, 550), 400, 90,
                                 facecolor='lightblue', alpha=0.3, edgecolor='blue')
        ax.add_patch(key_files_rect)
        ax.text(260, 620, "Key RTL Files Generated:", ha='center', 
               fontsize=11, fontweight='bold', color='blue')
        
        plt.tight_layout()
        plt.savefig(filename, dpi=150, bbox_inches='tight')
        plt.close()
        print(f"Created: {filename}")
        
    def create_vip_generation_process(self, filename="gui_vip_generation.png"):
        """Create VIP generation process visualization"""
        fig, ax = plt.subplots(1, 1, figsize=(12, 10))
        ax.set_xlim(0, 1200)
        ax.set_ylim(0, 1000)
        ax.axis('off')
        
        # Title
        ax.text(600, 950, "VIP Generation Process", ha='center', 
               fontsize=18, fontweight='bold')
        
        # Process flow boxes
        processes = [
            ("Configuration Analysis", 200, 850, "#3498db"),
            ("UVM Environment Generation", 600, 850, "#2ecc71"),
            ("Test Generation", 1000, 850, "#e74c3c"),
            ("Agent Creation", 200, 650, "#f39c12"),
            ("Sequence Library", 600, 650, "#9b59b6"),
            ("Compilation Check", 1000, 650, "#1abc9c")
        ]
        
        for name, x, y, color in processes:
            # Process box
            box = FancyBboxPatch((x-100, y-50), 200, 100,
                               boxstyle="round,pad=10",
                               facecolor=color, edgecolor='black', linewidth=2)
            ax.add_patch(box)
            ax.text(x, y, name, ha='center', va='center', 
                   fontsize=11, fontweight='bold', color='white')
        
        # Arrows between processes
        arrows = [
            ((300, 850), (500, 850)),  # Config to UVM
            ((700, 850), (900, 850)),  # UVM to Test
            ((200, 800), (200, 700)),  # Config to Agent
            ((600, 800), (600, 700)),  # UVM to Sequence
            ((1000, 800), (1000, 700)) # Test to Compilation
        ]
        
        for (x1, y1), (x2, y2) in arrows:
            ax.annotate('', xy=(x2, y2), xytext=(x1, y1),
                       arrowprops=dict(arrowstyle='->', lw=3, color='black'))
        
        # Generated files preview
        ax.text(600, 550, "Generated VIP Files Structure", ha='center', 
               fontsize=16, fontweight='bold')
        
        # File tree
        file_tree = Rectangle((150, 100), 900, 400,
                            facecolor='#f8f8f8', edgecolor='black', linewidth=1)
        ax.add_patch(file_tree)
        
        tree_text = """vip_output/
├── env/
│   ├── axi4_env.sv
│   ├── axi4_master_agent.sv
│   ├── axi4_slave_agent.sv
│   ├── axi4_scoreboard.sv
│   └── axi4_coverage.sv
├── sequences/
│   ├── axi4_base_sequence.sv
│   ├── axi4_read_sequence.sv
│   ├── axi4_write_sequence.sv
│   └── axi4_burst_sequence.sv
├── tests/
│   ├── axi4_base_test.sv
│   ├── axi4_basic_test.sv
│   ├── axi4_stress_test.sv
│   └── axi4_directed_test.sv
├── tb/
│   ├── hvl_top.sv
│   ├── hdl_top.sv
│   └── tb_axi4_interconnect.sv
└── sim/
    ├── Makefile
    ├── run_test.sh
    └── compile.do"""
        
        ax.text(170, 450, tree_text, fontsize=9, fontfamily='monospace', va='top')
        
        # Status indicator
        status_box = Rectangle((50, 20), 1100, 60,
                             facecolor='#d4edda', edgecolor='#28a745', linewidth=2)
        ax.add_patch(status_box)
        ax.text(600, 50, "✅ VIP Generation Complete!", ha='center', 
               fontsize=14, fontweight='bold', color='#28a745')
        ax.text(600, 30, "Ready to run: cd vip_output/sim && make compile && make run", 
               ha='center', fontsize=12, color='#155724')
        
        plt.tight_layout()
        plt.savefig(filename, dpi=150, bbox_inches='tight')
        plt.close()
        print(f"Created: {filename}")

def main():
    """Generate all GUI mockups"""
    print("Creating GUI mockup images for user guide...")
    
    generator = GUIMockupGenerator()
    
    # Generate all mockups
    generator.create_main_window_mockup()
    generator.create_add_master_dialog()
    generator.create_design_with_components()
    generator.create_rtl_generation_dialog()
    generator.create_file_output_view()
    generator.create_vip_generation_process()
    
    print("\nAll GUI mockup images created successfully!")
    print("Images created:")
    print("- gui_main_window.png - Main GUI interface")
    print("- gui_add_master.png - Add master dialog")
    print("- gui_design_canvas.png - Design with components")
    print("- gui_rtl_generation.png - RTL generation process")
    print("- gui_file_output.png - Generated file browser")
    print("- gui_vip_generation.png - VIP generation process")

if __name__ == "__main__":
    main()