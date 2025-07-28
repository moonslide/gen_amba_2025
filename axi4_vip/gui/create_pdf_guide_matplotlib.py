#!/usr/bin/env python3
"""
Create a comprehensive PDF user guide using matplotlib
This provides a rich PDF without requiring reportlab
"""

import matplotlib.pyplot as plt
from matplotlib.backends.backend_pdf import PdfPages
import matplotlib.patches as patches
from datetime import datetime
import textwrap

class MatplotlibUserGuide:
    """Create PDF user guide using matplotlib"""
    
    def __init__(self):
        self.filename = "userguide.pdf"
        self.title = "AMBA Bus Matrix Configuration Tool"
        self.subtitle = "User Guide and Reference Manual"
        self.version = "1.0.0"
        self.date = datetime.now().strftime("%B %Y")
        
    def create_cover_page(self, pdf):
        """Create cover page"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Title
        ax.text(0.5, 0.8, self.title, 
                horizontalalignment='center',
                verticalalignment='center',
                fontsize=28, fontweight='bold',
                transform=ax.transAxes)
        
        # Subtitle
        ax.text(0.5, 0.7, self.subtitle,
                horizontalalignment='center',
                verticalalignment='center', 
                fontsize=20,
                transform=ax.transAxes)
        
        # Version info
        ax.text(0.5, 0.3, f"Version {self.version}",
                horizontalalignment='center',
                fontsize=14,
                transform=ax.transAxes)
        
        ax.text(0.5, 0.25, self.date,
                horizontalalignment='center',
                fontsize=14,
                transform=ax.transAxes)
        
        # Decorative border
        rect = patches.Rectangle((0.1, 0.1), 0.8, 0.8, 
                               linewidth=2, edgecolor='#2c3e50', 
                               facecolor='none', transform=ax.transAxes)
        ax.add_patch(rect)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_toc_page(self, pdf):
        """Create table of contents"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Title
        ax.text(0.1, 0.95, "Table of Contents",
                fontsize=24, fontweight='bold',
                transform=ax.transAxes)
        
        # TOC items
        toc_items = [
            ("1. Introduction", "3"),
            ("2. Getting Started", "5"),
            ("3. GUI Overview", "8"),
            ("4. Creating Bus Designs", "12"),
            ("5. RTL Generation", "18"),
            ("6. VIP Generation", "24"),
            ("7. Configuration Reference", "30"),
            ("8. Advanced Features", "36"),
            ("9. Troubleshooting", "42"),
            ("10. API Reference", "48"),
            ("Appendix A: AXI Protocol Overview", "54"),
            ("Appendix B: Example Configurations", "60"),
        ]
        
        y_pos = 0.85
        for item, page in toc_items:
            ax.text(0.1, y_pos, item, fontsize=12, transform=ax.transAxes)
            ax.text(0.85, y_pos, page, fontsize=12, transform=ax.transAxes)
            
            # Dotted line
            ax.plot([0.5, 0.83], [y_pos, y_pos], 'k:', 
                   transform=ax.transAxes, alpha=0.5)
            
            y_pos -= 0.06
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_chapter_page(self, pdf, chapter_num, title, content_sections):
        """Create a chapter page"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Chapter title
        ax.text(0.1, 0.95, f"{chapter_num}. {title}",
                fontsize=22, fontweight='bold',
                transform=ax.transAxes)
        
        # Content
        y_pos = 0.88
        for section in content_sections:
            if section['type'] == 'heading':
                ax.text(0.1, y_pos, section['text'],
                       fontsize=16, fontweight='bold',
                       transform=ax.transAxes)
                y_pos -= 0.05
            elif section['type'] == 'text':
                # Wrap text
                wrapped = textwrap.fill(section['text'], width=80)
                for line in wrapped.split('\n'):
                    ax.text(0.1, y_pos, line, fontsize=11,
                           transform=ax.transAxes)
                    y_pos -= 0.03
            elif section['type'] == 'bullet':
                ax.text(0.12, y_pos, f"• {section['text']}", 
                       fontsize=11, transform=ax.transAxes)
                y_pos -= 0.03
            elif section['type'] == 'code':
                # Code block with background
                code_lines = section['text'].split('\n')
                code_y = y_pos
                
                # Background rectangle
                rect = patches.Rectangle((0.1, code_y - 0.03 * len(code_lines) - 0.01), 
                                       0.8, 0.03 * len(code_lines) + 0.02,
                                       facecolor='#f5f5f5', edgecolor='#cccccc',
                                       transform=ax.transAxes)
                ax.add_patch(rect)
                
                for line in code_lines:
                    ax.text(0.12, code_y, line, fontsize=9,
                           fontfamily='monospace',
                           transform=ax.transAxes)
                    code_y -= 0.03
                y_pos = code_y - 0.02
            elif section['type'] == 'image':
                # Add image support
                import matplotlib.image as mpimg
                import os
                
                image_path = section['path']
                if os.path.exists(image_path):
                    try:
                        img = mpimg.imread(image_path)
                        # Create image area
                        img_height = 0.3  # 30% of page height
                        img_rect = patches.Rectangle((0.1, y_pos - img_height), 0.8, img_height,
                                                   facecolor='white', edgecolor='gray',
                                                   transform=ax.transAxes)
                        ax.add_patch(img_rect)
                        
                        # Add image (simplified for this implementation)
                        ax.text(0.5, y_pos - img_height/2, f"[GUI Screenshot: {section.get('caption', 'Image')}]",
                               ha='center', va='center', fontsize=12, style='italic',
                               transform=ax.transAxes)
                        y_pos -= img_height + 0.02
                    except:
                        ax.text(0.1, y_pos, f"[Image: {section.get('caption', 'Screenshot')}]",
                               fontsize=11, style='italic', transform=ax.transAxes)
                        y_pos -= 0.03
                else:
                    ax.text(0.1, y_pos, f"[Image: {section.get('caption', 'Screenshot')}]",
                           fontsize=11, style='italic', transform=ax.transAxes)
                    y_pos -= 0.03
            
            y_pos -= 0.02
            
            if y_pos < 0.1:
                break
        
        # Page number
        ax.text(0.5, 0.05, f"Page {chapter_num + 2}", 
               horizontalalignment='center',
               fontsize=10, transform=ax.transAxes)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_diagram_page(self, pdf, title, diagram_type):
        """Create a page with a diagram"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Title
        ax.text(0.5, 0.95, title,
                horizontalalignment='center',
                fontsize=20, fontweight='bold',
                transform=ax.transAxes)
        
        if diagram_type == 'architecture':
            self.draw_architecture_diagram(ax)
        elif diagram_type == 'gui_layout':
            self.draw_gui_layout(ax)
        elif diagram_type == 'axi_channels':
            self.draw_axi_channels(ax)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def draw_architecture_diagram(self, ax):
        """Draw system architecture diagram"""
        # GUI Layer
        gui_rect = patches.Rectangle((0.2, 0.7), 0.6, 0.15,
                                   facecolor='#3498db', edgecolor='black')
        ax.add_patch(gui_rect)
        ax.text(0.5, 0.775, 'GUI Layer', ha='center', va='center',
               fontsize=12, fontweight='bold', color='white',
               transform=ax.transAxes)
        
        # Generator Layer
        gen_rect = patches.Rectangle((0.1, 0.45), 0.35, 0.2,
                                   facecolor='#2ecc71', edgecolor='black')
        ax.add_patch(gen_rect)
        ax.text(0.275, 0.55, 'RTL\nGenerator', ha='center', va='center',
               fontsize=11, fontweight='bold', color='white',
               transform=ax.transAxes)
        
        vip_rect = patches.Rectangle((0.55, 0.45), 0.35, 0.2,
                                   facecolor='#e74c3c', edgecolor='black')
        ax.add_patch(vip_rect)
        ax.text(0.725, 0.55, 'VIP\nGenerator', ha='center', va='center',
               fontsize=11, fontweight='bold', color='white',
               transform=ax.transAxes)
        
        # Output Layer
        rtl_rect = patches.Rectangle((0.1, 0.2), 0.35, 0.2,
                                   facecolor='#95a5a6', edgecolor='black')
        ax.add_patch(rtl_rect)
        ax.text(0.275, 0.3, 'Verilog\nRTL', ha='center', va='center',
               fontsize=11, transform=ax.transAxes)
        
        vip_rect = patches.Rectangle((0.55, 0.2), 0.35, 0.2,
                                   facecolor='#95a5a6', edgecolor='black')
        ax.add_patch(vip_rect)
        ax.text(0.725, 0.3, 'UVM\nTestbench', ha='center', va='center',
               fontsize=11, transform=ax.transAxes)
        
        # Arrows
        ax.arrow(0.5, 0.7, 0, -0.04, head_width=0.02, head_length=0.01,
                fc='black', ec='black', transform=ax.transAxes)
        ax.arrow(0.275, 0.45, 0, -0.04, head_width=0.02, head_length=0.01,
                fc='black', ec='black', transform=ax.transAxes)
        ax.arrow(0.725, 0.45, 0, -0.04, head_width=0.02, head_length=0.01,
                fc='black', ec='black', transform=ax.transAxes)
        
    def draw_gui_layout(self, ax):
        """Draw GUI layout diagram"""
        # Main window
        main_rect = patches.Rectangle((0.1, 0.2), 0.8, 0.6,
                                    facecolor='white', edgecolor='black', linewidth=2)
        ax.add_patch(main_rect)
        
        # Menu bar
        menu_rect = patches.Rectangle((0.1, 0.75), 0.8, 0.05,
                                    facecolor='#ecf0f1', edgecolor='black')
        ax.add_patch(menu_rect)
        ax.text(0.5, 0.775, 'Menu Bar', ha='center', va='center',
               fontsize=10, transform=ax.transAxes)
        
        # Toolbar
        toolbar_rect = patches.Rectangle((0.1, 0.7), 0.8, 0.05,
                                       facecolor='#bdc3c7', edgecolor='black')
        ax.add_patch(toolbar_rect)
        ax.text(0.5, 0.725, 'Toolbar', ha='center', va='center',
               fontsize=10, transform=ax.transAxes)
        
        # Canvas
        canvas_rect = patches.Rectangle((0.1, 0.25), 0.55, 0.45,
                                      facecolor='#f8f9fa', edgecolor='black')
        ax.add_patch(canvas_rect)
        ax.text(0.375, 0.475, 'Design Canvas', ha='center', va='center',
               fontsize=12, transform=ax.transAxes)
        
        # Properties panel
        props_rect = patches.Rectangle((0.65, 0.25), 0.25, 0.45,
                                     facecolor='#e8f4f8', edgecolor='black')
        ax.add_patch(props_rect)
        ax.text(0.775, 0.475, 'Properties\nPanel', ha='center', va='center',
               fontsize=11, transform=ax.transAxes)
        
        # Status bar
        status_rect = patches.Rectangle((0.1, 0.2), 0.8, 0.05,
                                      facecolor='#ecf0f1', edgecolor='black')
        ax.add_patch(status_rect)
        ax.text(0.5, 0.225, 'Status Bar', ha='center', va='center',
               fontsize=10, transform=ax.transAxes)
        
    def draw_axi_channels(self, ax):
        """Draw AXI channel diagram"""
        # Master
        master_rect = patches.Rectangle((0.1, 0.4), 0.2, 0.3,
                                      facecolor='#3498db', edgecolor='black')
        ax.add_patch(master_rect)
        ax.text(0.2, 0.55, 'Master', ha='center', va='center',
               fontsize=12, fontweight='bold', color='white',
               transform=ax.transAxes, rotation=90)
        
        # Slave
        slave_rect = patches.Rectangle((0.7, 0.4), 0.2, 0.3,
                                     facecolor='#e74c3c', edgecolor='black')
        ax.add_patch(slave_rect)
        ax.text(0.8, 0.55, 'Slave', ha='center', va='center',
               fontsize=12, fontweight='bold', color='white',
               transform=ax.transAxes, rotation=90)
        
        # Channels
        channels = [
            ('Write Address (AW)', 0.65, '#2ecc71'),
            ('Write Data (W)', 0.6, '#27ae60'),
            ('Write Response (B)', 0.55, '#16a085'),
            ('Read Address (AR)', 0.5, '#f39c12'),
            ('Read Data (R)', 0.45, '#e67e22')
        ]
        
        for i, (name, y, color) in enumerate(channels):
            if i < 3:  # Write channels
                ax.arrow(0.3, y, 0.38, 0, head_width=0.02, head_length=0.02,
                        fc=color, ec=color, transform=ax.transAxes)
                if i == 2:  # Write response goes back
                    ax.arrow(0.7, y-0.01, -0.38, 0, head_width=0.02, head_length=0.02,
                            fc=color, ec=color, transform=ax.transAxes)
            else:  # Read channels
                ax.arrow(0.3, y, 0.38, 0, head_width=0.02, head_length=0.02,
                        fc=color, ec=color, transform=ax.transAxes)
                if i == 4:  # Read data goes back
                    ax.arrow(0.7, y-0.01, -0.38, 0, head_width=0.02, head_length=0.02,
                            fc=color, ec=color, transform=ax.transAxes)
            
            ax.text(0.5, y + 0.015, name, ha='center', va='bottom',
                   fontsize=9, transform=ax.transAxes)
        
    def create(self):
        """Create the complete PDF"""
        with PdfPages(self.filename) as pdf:
            # Cover page
            self.create_cover_page(pdf)
            
            # Table of contents
            self.create_toc_page(pdf)
            
            # Chapter 1: Introduction
            self.create_chapter_page(pdf, 1, "Introduction", [
                {'type': 'text', 'text': 'The AMBA Bus Matrix Configuration Tool is a comprehensive solution for designing and implementing ARM AMBA-based System-on-Chip (SoC) interconnects. This tool provides both a graphical user interface for visual design and a powerful backend for generating synthesizable RTL and verification environments.'},
                {'type': 'heading', 'text': '1.1 Key Features'},
                {'type': 'bullet', 'text': 'Visual bus matrix design with drag-and-drop interface'},
                {'type': 'bullet', 'text': 'Support for AXI4, AXI3, AHB, and APB protocols'},
                {'type': 'bullet', 'text': 'Automatic RTL generation with parameterizable configurations'},
                {'type': 'bullet', 'text': 'Complete UVM-based verification environment generation'},
                {'type': 'bullet', 'text': 'Built-in address overlap detection and validation'},
                {'type': 'bullet', 'text': 'Security and QoS configuration support'},
                {'type': 'heading', 'text': '1.2 System Requirements'},
                {'type': 'bullet', 'text': 'Python 3.6 or higher'},
                {'type': 'bullet', 'text': 'Tkinter GUI library'},
                {'type': 'bullet', 'text': 'SystemVerilog simulator (VCS, Questa, or Xcelium)'},
                {'type': 'bullet', 'text': 'UVM 1.2 library'},
            ])
            
            # Architecture diagram
            self.create_diagram_page(pdf, "System Architecture", "architecture")
            
            # Chapter 2: Getting Started
            self.create_chapter_page(pdf, 2, "Getting Started", [
                {'type': 'heading', 'text': '2.1 Installation'},
                {'type': 'text', 'text': 'Clone the repository and install dependencies:'},
                {'type': 'code', 'text': 'cd /your/project/directory\ngit clone <repository_url>\ncd axi4_vip/gui\npip install -r requirements.txt'},
                {'type': 'heading', 'text': '2.2 Launching the GUI'},
                {'type': 'text', 'text': 'Start the GUI application:'},
                {'type': 'code', 'text': './launch_gui.sh\n# OR\npython3 src/bus_matrix_gui.py'},
                {'type': 'text', 'text': 'If GUI fails to launch:'},
                {'type': 'bullet', 'text': 'Check Python 3.6+ is installed: python3 --version'},
                {'type': 'bullet', 'text': 'Install tkinter if missing: sudo apt-get install python3-tk'},
                {'type': 'bullet', 'text': 'Make script executable: chmod +x launch_gui.sh'},
                {'type': 'heading', 'text': '2.3 Setting Up Bus Matrix - Step by Step'},
                {'type': 'text', 'text': 'Complete workflow to build a 2x3 system (CPU+DMA → DDR+SRAM+Peripherals):'},
                {'type': 'text', 'text': 'STEP 1: Create New Project'},
                {'type': 'bullet', 'text': 'File → New Project (or Ctrl+N)'},
                {'type': 'bullet', 'text': 'Enter project name: "cpu_dma_system"'},
                {'type': 'bullet', 'text': 'Select bus type: AXI4 (recommended)'},
                {'type': 'bullet', 'text': 'Set data width: 64 bits (typical choice)'},
                {'type': 'text', 'text': 'STEP 2: Add Masters'},
                {'type': 'bullet', 'text': 'Click "Add Master" button in left panel'},
                {'type': 'bullet', 'text': 'Master 1: Name="CPU_0", ID Width=4, Priority=2, QoS=Yes'},
                {'type': 'bullet', 'text': 'Click "Add Master" again'},
                {'type': 'bullet', 'text': 'Master 2: Name="DMA_0", ID Width=6, Priority=1, QoS=Yes'},
                {'type': 'text', 'text': 'STEP 3: Add Slaves (CRITICAL - Address Configuration)'},
                {'type': 'bullet', 'text': 'Click "Add Slave" button'},
                {'type': 'bullet', 'text': 'Slave 1: Name="DDR_Memory", Base=0x00000000, Size=1GB'},
                {'type': 'bullet', 'text': 'Slave 2: Name="SRAM_Cache", Base=0x40000000, Size=256MB'},  
                {'type': 'bullet', 'text': 'Slave 3: Name="Peripherals", Base=0x50000000, Size=256MB'},
                {'type': 'text', 'text': 'STEP 4: Make Connections'},
                {'type': 'bullet', 'text': 'Drag from CPU_0 output port to each slave input port'},
                {'type': 'bullet', 'text': 'Drag from DMA_0 output port to DDR and SRAM (skip peripherals)'},
                {'type': 'bullet', 'text': 'OR use Connection Matrix: View → Connection Matrix'},
                {'type': 'text', 'text': 'STEP 5: Validate Design'},
                {'type': 'bullet', 'text': 'Tools → Validate Design (or Ctrl+V)'},
                {'type': 'bullet', 'text': 'Fix any errors (typically address overlaps) before proceeding'},
                {'type': 'text', 'text': 'STEP 6: Generate RTL'},
                {'type': 'bullet', 'text': 'Generate → Generate RTL (or Ctrl+G)'},
                {'type': 'bullet', 'text': 'Choose output directory (default: output_rtl/)'},
                {'type': 'bullet', 'text': 'Click Generate - creates .v files for synthesis'},
                {'type': 'text', 'text': 'STEP 7: Generate VIP (Verification IP)'},
                {'type': 'bullet', 'text': 'Generate → Generate VIP (or Ctrl+Shift+G)'},
                {'type': 'bullet', 'text': 'Choose output directory (default: vip_output/)'},
                {'type': 'bullet', 'text': 'Creates complete UVM verification environment'},
                {'type': 'text', 'text': 'STEP 8: Run VIP Simulation'},
                {'type': 'bullet', 'text': 'cd vip_output/sim'},
                {'type': 'bullet', 'text': 'make compile && make sim TEST=basic_test'},
                {'type': 'bullet', 'text': 'View results: cat logs/basic_test.log'},
            ])
            
            # GUI Layout diagram
            self.create_diagram_page(pdf, "GUI Layout", "gui_layout")
            
            # Chapter 3: Creating Bus Designs
            self.create_chapter_page(pdf, 3, "Creating Bus Designs", [
                {'type': 'heading', 'text': '3.1 Adding Masters'},
                {'type': 'text', 'text': 'Masters represent components that initiate transactions:'},
                {'type': 'bullet', 'text': 'CPU cores'},
                {'type': 'bullet', 'text': 'DMA engines'},
                {'type': 'bullet', 'text': 'GPU processors'},
                {'type': 'bullet', 'text': 'PCIe endpoints'},
                {'type': 'heading', 'text': '3.2 Configuring Masters'},
                {'type': 'bullet', 'text': 'Name: Descriptive identifier'},
                {'type': 'bullet', 'text': 'ID Width: Transaction ID bits'},
                {'type': 'bullet', 'text': 'Priority: Arbitration priority'},
                {'type': 'bullet', 'text': 'QoS Support: Enable quality of service'},
                {'type': 'bullet', 'text': 'Exclusive Support: Enable exclusive access'},
                {'type': 'heading', 'text': '3.3 Adding Slaves'},
                {'type': 'text', 'text': 'Slaves respond to transactions:'},
                {'type': 'bullet', 'text': 'Memory controllers (DDR, SRAM)'},
                {'type': 'bullet', 'text': 'Peripheral registers'},
                {'type': 'bullet', 'text': 'Configuration spaces'},
            ])
            
            # AXI Channels diagram
            self.create_diagram_page(pdf, "AXI Protocol Channels", "axi_channels")
            
            # Chapter 4: RTL Generation
            self.create_chapter_page(pdf, 4, "RTL Generation", [
                {'type': 'heading', 'text': '4.1 Generated Files'},
                {'type': 'bullet', 'text': 'axi4_interconnect_mNsM.v - Top-level module'},
                {'type': 'bullet', 'text': 'axi4_address_decoder.v - Address decoding'},
                {'type': 'bullet', 'text': 'axi4_arbiter.v - Arbitration logic'},
                {'type': 'bullet', 'text': 'axi4_router.v - Transaction routing'},
                {'type': 'bullet', 'text': 'tb_axi4_interconnect.v - Basic testbench'},
                {'type': 'heading', 'text': '4.2 Module Parameters'},
                {'type': 'code', 'text': 'module axi4_interconnect_m2s3 #(\n  parameter DATA_WIDTH = 128,\n  parameter ADDR_WIDTH = 40,\n  parameter ID_WIDTH   = 4\n)'},
            ])
            
            # Chapter 5: Troubleshooting
            self.create_chapter_page(pdf, 5, "Troubleshooting", [
                {'type': 'heading', 'text': '5.1 Common Issues'},
                {'type': 'text', 'text': 'Port Width Mismatch Warnings:'},
                {'type': 'code', 'text': 'Lint-[PCWM-L] Port connection width mismatch'},
                {'type': 'text', 'text': 'Solution: Regenerate RTL with latest version'},
                {'type': 'text', 'text': 'GUI Launch Issues:'},
                {'type': 'code', 'text': 'ImportError: No module named tkinter'},
                {'type': 'text', 'text': 'Solution: Install tkinter package'},
                {'type': 'heading', 'text': '5.2 Debug Mode'},
                {'type': 'text', 'text': 'Enable debug output:'},
                {'type': 'code', 'text': 'export AXI_VIP_DEBUG=1\n./launch_gui.sh --debug'},
            ])
            
            # Metadata
            d = pdf.infodict()
            d['Title'] = self.title
            d['Author'] = 'AMBA Bus Matrix Tool Team'
            d['Subject'] = self.subtitle
            d['Keywords'] = 'AMBA AXI SystemVerilog UVM RTL'
            d['CreationDate'] = datetime.now()

def main():
    """Create the PDF user guide"""
    print("Creating comprehensive PDF user guide using matplotlib...")
    
    guide = MatplotlibUserGuide()
    guide.create()
    
    print(f"\nUser guide created: {guide.filename}")
    
    # Get file size
    import os
    size_kb = os.path.getsize(guide.filename) / 1024
    print(f"File size: {size_kb:.1f} KB")
    print("\nThe PDF contains:")
    print("- Cover page")
    print("- Table of contents")
    print("- Introduction and getting started")
    print("- Architecture diagrams")
    print("- GUI layout diagrams")
    print("- AXI protocol diagrams")
    print("- Configuration guides")
    print("- Troubleshooting section")

if __name__ == "__main__":
    main()