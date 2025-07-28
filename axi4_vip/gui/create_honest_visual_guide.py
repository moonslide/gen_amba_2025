#!/usr/bin/env python3
"""
Create HONEST visual user guide with clear mockup disclaimers
This addresses the issue that current "screenshots" are actually programmatic mockups
"""

import matplotlib.pyplot as plt
from matplotlib.backends.backend_pdf import PdfPages
import matplotlib.patches as patches
from datetime import datetime
import textwrap
import os

class HonestVisualGuide:
    """Create user guide with honest mockup disclaimers"""
    
    def __init__(self):
        self.filename = "honest_visual_userguide.pdf"
        self.title = "AMBA Bus Matrix Configuration Tool"
        self.subtitle = "Visual Guide with Conceptual Mockups"
        self.version = "1.0.0"
        self.date = datetime.now().strftime("%B %Y")
        
    def create_disclaimer_page(self, pdf):
        """Create clear disclaimer about mockup nature"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Warning header
        warning_rect = patches.Rectangle((0.1, 0.8), 0.8, 0.15,
                                       facecolor='#ffebee', 
                                       edgecolor='#f44336', linewidth=3,
                                       transform=ax.transAxes)
        ax.add_patch(warning_rect)
        
        ax.text(0.5, 0.875, "⚠️ IMPORTANT DISCLAIMER ⚠️",
                ha='center', va='center', fontsize=18, fontweight='bold',
                color='#d32f2f', transform=ax.transAxes)
        
        # Disclaimer text
        disclaimer_text = """
CURRENT STATUS OF GUI IMAGES:

❌ NOT REAL SCREENSHOTS
The images in this guide are PROGRAMMATICALLY GENERATED MOCKUPS created with 
matplotlib, not actual screenshots from the running GUI application.

✅ WHAT THESE IMAGES ARE:
• Conceptual representations of GUI layout and workflow
• Based on analysis of the actual GUI source code (bus_matrix_gui.py)
• Designed to show expected interface structure and functionality
• Created to demonstrate the intended user workflow

❌ WHAT THESE IMAGES ARE NOT:
• Actual screenshots from a running GUI application
• Real captures of the interface in action
• Guaranteed to match the exact appearance of the running application

🔧 TO GET REAL SCREENSHOTS:
1. Launch the actual GUI: ./launch_gui.sh
2. Follow the workflow steps described in this guide
3. Use screenshot tools (Print Screen, snipping tool, etc.)
4. Replace mockup images with real captures

📋 VERIFICATION NEEDED:
This documentation needs to be updated with real screenshots from the 
actual running GUI application to provide authentic visual guidance.

🎯 PURPOSE OF THIS GUIDE:
Until real screenshots are available, this guide provides the conceptual 
workflow and expected interface behavior based on the source code analysis.
        """
        
        ax.text(0.05, 0.75, disclaimer_text,
                fontsize=10, va='top', ha='left',
                transform=ax.transAxes, 
                bbox=dict(boxstyle="round,pad=0.02", facecolor='#fff3e0', alpha=0.8))
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_mockup_comparison_page(self, pdf):
        """Show what mockups vs real GUI would look like"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.5, 0.95, "Mockup vs Real GUI Comparison",
                ha='center', fontsize=18, fontweight='bold',
                transform=ax.transAxes)
        
        # Left side - Current Mockups
        mockup_rect = patches.Rectangle((0.05, 0.4), 0.4, 0.5,
                                      facecolor='#ffebee', edgecolor='red', linewidth=2,
                                      transform=ax.transAxes)
        ax.add_patch(mockup_rect)
        ax.text(0.25, 0.85, "CURRENT: Programmatic Mockups",
                ha='center', fontweight='bold', fontsize=12,
                transform=ax.transAxes)
        
        mockup_text = """
• Created with matplotlib rectangles/text
• Based on GUI source code analysis
• Shows expected layout structure
• Colors match actual GUI constants:
  - Master: #4CAF50 (green)
  - Slave: #2196F3 (blue)
  - Interconnect: #FFC107 (amber)
• Demonstrates workflow concepts
• NOT captured from running application
        """
        ax.text(0.07, 0.8, mockup_text, fontsize=9, va='top',
                transform=ax.transAxes)
        
        # Right side - Real GUI Needed
        real_rect = patches.Rectangle((0.55, 0.4), 0.4, 0.5,
                                    facecolor='#e8f5e8', edgecolor='green', linewidth=2,
                                    transform=ax.transAxes)
        ax.add_patch(real_rect)
        ax.text(0.75, 0.85, "NEEDED: Real GUI Screenshots",
                ha='center', fontweight='bold', fontsize=12,
                transform=ax.transAxes)
        
        real_text = """
• Captured from running bus_matrix_gui.py
• Shows actual Tkinter interface
• Real drag-and-drop interactions
• Authentic dialog boxes
• Actual button/menu appearances
• True canvas rendering
• Live configuration panels
• Real-time validation messages
        """
        ax.text(0.57, 0.8, real_text, fontsize=9, va='top',
                transform=ax.transAxes)
        
        # Instructions box
        instruct_rect = patches.Rectangle((0.1, 0.05), 0.8, 0.3,
                                        facecolor='#f0f4f8', edgecolor='blue', linewidth=2,
                                        transform=ax.transAxes)
        ax.add_patch(instruct_rect)
        ax.text(0.5, 0.32, "How to Replace with Real Screenshots",
                ha='center', fontweight='bold', fontsize=14,
                transform=ax.transAxes)
        
        instructions = """
1. Navigate to: /home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/
2. Run: ./launch_gui.sh (requires GUI environment with DISPLAY)
3. Take screenshots at each workflow step:
   - Main window after launch
   - Add Master dialog (click "Add Master" button)
   - Canvas with 2 masters + 3 slaves designed
   - RTL Generation dialog (click "Generate RTL")
   - File browser showing generated outputs
   - VIP Generation process (click "Generate VIP")
4. Save as PNG files with same names as current mockups
5. Regenerate this PDF with real images embedded
        """
        
        ax.text(0.12, 0.28, instructions, fontsize=10, va='top',
                transform=ax.transAxes)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_gui_source_analysis_page(self, pdf):
        """Show what we learned from analyzing the GUI source code"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.5, 0.95, "GUI Source Code Analysis",
                ha='center', fontsize=18, fontweight='bold',
                transform=ax.transAxes)
        
        analysis_text = """
ANALYSIS OF bus_matrix_gui.py (Actual GUI Application):

🏗️ GUI FRAMEWORK:
• Built with Python Tkinter
• Uses tk.Canvas for visual bus matrix representation
• Implements drag-and-drop functionality for masters/slaves
• Has zoom and grid snapping capabilities

🎨 VISUAL ELEMENTS:
• Masters: Green blocks (#4CAF50) with drag handles
• Slaves: Blue blocks (#2196F3) with address/size info
• Interconnect: Amber color (#FFC107) for connections
• Connection lines: Gray (#757575) with arrows
• Selected items flash with yellow highlight
• Security indicators: [SEC] and [PERM] tags

📱 GUI COMPONENTS:
• BusMatrixCanvas - main visual design area
• Master/Slave configuration dialogs
• Properties panels for component configuration
• Menu bar with File, Edit, View, Tools, Generate options
• Toolbar with quick access buttons
• Status bar for validation messages

⚙️ FUNCTIONALITY:
• Add/remove masters and slaves visually
• Drag to reposition components on canvas
• Right-click context menus for configuration
• Address overlap detection and validation
• RTL generation with progress dialogs
• VIP generation with UVM output
• Configuration save/load (JSON format)
• Integration with AXI Verilog generator

🔧 CONFIGURATION CLASSES:
• MasterConfig: name, id_width, qos_support, priority, etc.
• SlaveConfig: name, base_address, size, memory_type, etc.
• BusConfig: bus_type, data_width, addr_width, arbitration

📂 KEY FEATURES IDENTIFIED:
• Visual bus matrix design with real-time validation
• Support for AXI4, AXI3, AHB, APB protocols
• Security and permission controls
• QoS and priority configuration
• Export to synthesizable Verilog RTL
• Complete UVM verification environment generation

This analysis confirms the GUI is a fully functional application that can be 
launched and used to create real screenshots for documentation.
        """
        
        ax.text(0.05, 0.9, analysis_text, fontsize=9, va='top',
                transform=ax.transAxes, fontfamily='monospace')
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_workflow_with_honest_mockups(self, pdf):
        """Create workflow page with clear mockup labels"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.5, 0.95, "Expected GUI Workflow (Conceptual)",
                ha='center', fontsize=18, fontweight='bold',
                transform=ax.transAxes)
        
        # Add mockup disclaimer at top
        disclaimer_box = patches.Rectangle((0.1, 0.85), 0.8, 0.08,
                                         facecolor='#fff3e0', edgecolor='orange', linewidth=1,
                                         transform=ax.transAxes)
        ax.add_patch(disclaimer_box)
        ax.text(0.5, 0.89, "⚠️ CONCEPTUAL MOCKUPS BELOW - NOT REAL SCREENSHOTS ⚠️",
                ha='center', va='center', fontsize=11, fontweight='bold',
                color='#e65100', transform=ax.transAxes)
        
        workflow_text = """
STEP-BY-STEP WORKFLOW (Based on Source Code Analysis):

1️⃣ LAUNCH GUI
   Command: ./launch_gui.sh
   Expected: Tkinter window opens with canvas, toolbar, properties panel
   [MOCKUP PLACEHOLDER - Need real screenshot of main window]

2️⃣ ADD MASTER
   Action: Click "Add Master" button in toolbar
   Expected: Dialog box with fields for Name, ID Width, Priority, QoS
   [MOCKUP PLACEHOLDER - Need real screenshot of add master dialog]

3️⃣ ADD SLAVES  
   Action: Click "Add Slave" button, configure addresses
   Expected: Dialog with Name, Base Address, Size, Memory Type fields
   [MOCKUP PLACEHOLDER - Need real screenshot of add slave dialog]

4️⃣ DESIGN CANVAS
   Result: Canvas shows green master blocks, blue slave blocks
   Expected: Drag-and-drop repositioning, connection lines, address labels
   [MOCKUP PLACEHOLDER - Need real screenshot of design canvas]

5️⃣ VALIDATE DESIGN
   Action: Tools → Validate Design
   Expected: Status messages, address overlap checking
   [MOCKUP PLACEHOLDER - Need real screenshot of validation]

6️⃣ GENERATE RTL
   Action: Generate → Generate RTL
   Expected: Dialog showing file list, output directory, progress bar
   [MOCKUP PLACEHOLDER - Need real screenshot of RTL generation]

7️⃣ GENERATE VIP
   Action: Generate → Generate VIP  
   Expected: VIP generation dialog, UVM environment creation
   [MOCKUP PLACEHOLDER - Need real screenshot of VIP generation]

8️⃣ VIEW OUTPUT
   Result: File browser showing generated .v files and VIP structure
   [MOCKUP PLACEHOLDER - Need real screenshot of output files]

ACCURACY NOTE:
This workflow is based on source code analysis of bus_matrix_gui.py.
The actual GUI may have additional features, different layouts, or
modified behavior that can only be captured through real screenshots.
        """
        
        ax.text(0.05, 0.8, workflow_text, fontsize=10, va='top',
                transform=ax.transAxes, fontfamily='monospace')
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create(self):
        """Create the honest visual guide"""
        with PdfPages(self.filename) as pdf:
            # Cover page
            fig = plt.figure(figsize=(8.5, 11))
            ax = fig.add_subplot(111)
            ax.axis('off')
            
            ax.text(0.5, 0.8, self.title, 
                    ha='center', va='center', fontsize=28, fontweight='bold',
                    transform=ax.transAxes)
            
            ax.text(0.5, 0.7, self.subtitle,
                    ha='center', va='center', fontsize=18,
                    color='#e65100', transform=ax.transAxes)
            
            ax.text(0.5, 0.6, "⚠️ Contains Mockups, Not Real Screenshots ⚠️",
                    ha='center', va='center', fontsize=14, fontweight='bold',
                    color='red', transform=ax.transAxes)
            
            ax.text(0.5, 0.3, f"Version {self.version}",
                    ha='center', fontsize=14, transform=ax.transAxes)
            
            ax.text(0.5, 0.25, self.date,
                    ha='center', fontsize=14, transform=ax.transAxes)
            
            # Border
            rect = patches.Rectangle((0.1, 0.1), 0.8, 0.8, 
                                   linewidth=2, edgecolor='red', 
                                   facecolor='none', transform=ax.transAxes)
            ax.add_patch(rect)
            
            pdf.savefig(fig, bbox_inches='tight')
            plt.close()
            
            # Disclaimer page
            self.create_disclaimer_page(pdf)
            
            # Mockup vs Real comparison
            self.create_mockup_comparison_page(pdf)
            
            # GUI source analysis
            self.create_gui_source_analysis_page(pdf)
            
            # Workflow with honest mockups
            self.create_workflow_with_honest_mockups(pdf)
            
            # Metadata
            d = pdf.infodict()
            d['Title'] = self.title + " - " + self.subtitle
            d['Author'] = 'AMBA Bus Matrix Tool Team'
            d['Subject'] = 'Honest Documentation - Mockups Only'
            d['Keywords'] = 'AMBA AXI GUI Mockups Documentation Disclaimer'
            d['CreationDate'] = datetime.now()

def main():
    """Create the honest visual guide"""
    print("Creating HONEST visual user guide with mockup disclaimers...")
    
    guide = HonestVisualGuide()
    guide.create()
    
    print(f"\nHonest visual guide created: {guide.filename}")
    
    # Get file size
    import os
    size_kb = os.path.getsize(guide.filename) / 1024
    print(f"File size: {size_kb:.1f} KB")
    print("\nThis PDF contains:")
    print("- Clear disclaimer about mockup nature")
    print("- Explanation of current limitations")
    print("- Analysis of actual GUI source code")
    print("- Instructions for capturing real screenshots")
    print("- Honest comparison of mockups vs real GUI needs")
    print("\n⚠️  This addresses the issue that current 'screenshots' are mockups")

if __name__ == "__main__":
    main()