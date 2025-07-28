#!/usr/bin/env python3
"""
Create comprehensive GUI usage guide with detailed step-by-step instructions
Ultra-think approach - complete GUI workflow documentation
"""

import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.patches import Rectangle, Circle, FancyBboxPatch, Polygon
import numpy as np
from datetime import datetime

class CompleteGUIGuide:
    """Create ultra-comprehensive GUI usage guide"""
    
    def __init__(self):
        self.filename = "complete_gui_userguide.pdf"
        
    def create(self):
        """Generate the complete GUI guide"""
        from matplotlib.backends.backend_pdf import PdfPages
        
        with PdfPages(self.filename) as pdf:
            # Cover and TOC
            self.create_cover(pdf)
            self.create_toc(pdf)
            
            # Part 1: GUI Basics
            self.create_gui_overview(pdf)
            self.create_launching_gui(pdf)
            self.create_gui_interface_tour(pdf)
            
            # Part 2: Setting up Bus Matrix
            self.create_new_project_setup(pdf)
            self.create_adding_masters_detailed(pdf)
            self.create_adding_slaves_detailed(pdf)
            self.create_making_connections_detailed(pdf)
            self.create_configuration_parameters(pdf)
            
            # Part 3: RTL Generation
            self.create_rtl_generation_detailed(pdf)
            self.create_rtl_output_explanation(pdf)
            self.create_rtl_integration_steps(pdf)
            
            # Part 4: VIP Generation
            self.create_vip_generation_detailed(pdf)
            self.create_vip_output_explanation(pdf)
            self.create_vip_simulation_steps(pdf)
            
            # Part 5: Complete Workflows
            self.create_complete_workflow_example(pdf)
            self.create_advanced_gui_features(pdf)
            self.create_troubleshooting_gui(pdf)
            
            # Part 6: Real Examples
            self.create_example_2x3_system(pdf)
            self.create_example_complex_system(pdf)
            self.create_common_patterns(pdf)
            
        print(f"\nComplete GUI guide created: {self.filename}")
        import os
        size = os.path.getsize(self.filename) / 1024
        print(f"File size: {size:.1f} KB")
        
    def create_cover(self, pdf):
        """Create cover page"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Background
        gradient = np.linspace(0, 1, 256).reshape(256, 1)
        gradient = np.hstack((gradient, gradient, gradient))
        ax.imshow(gradient, extent=[0, 10, 0, 10], aspect='auto', cmap='Blues_r', alpha=0.3)
        
        # Title
        ax.text(5, 8, 'AMBA Bus Matrix GUI\nComplete User Guide', 
                fontsize=32, weight='bold', ha='center', va='center',
                bbox=dict(boxstyle='round,pad=1', facecolor='white', alpha=0.9))
        
        # Subtitle
        ax.text(5, 6.5, 'Step-by-Step GUI Workflow', 
                fontsize=20, ha='center', va='center', style='italic')
        
        # GUI mockup
        self._draw_gui_preview(ax, 5, 4, 3)
        
        # Version
        ax.text(5, 2, 'Version 1.0.0 - Complete Edition\nJuly 2025', 
                fontsize=14, ha='center', va='center')
        
        ax.set_xlim(0, 10)
        ax.set_ylim(0, 10)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_toc(self, pdf):
        """Create table of contents"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.5, 0.95, 'Table of Contents', fontsize=24, weight='bold', 
                transform=ax.transAxes, ha='center')
        
        toc_items = [
            ("Part 1: GUI Basics", ""),
            ("  1. GUI Overview", "3"),
            ("  2. Launching the GUI", "4"),
            ("  3. Interface Tour", "5"),
            ("Part 2: Setting up Bus Matrix", ""),
            ("  4. New Project Setup", "7"),
            ("  5. Adding Masters (Detailed)", "8"),
            ("  6. Adding Slaves (Detailed)", "10"),
            ("  7. Making Connections (Detailed)", "12"),
            ("  8. Configuration Parameters", "14"),
            ("Part 3: RTL Generation", ""),
            ("  9. RTL Generation Process", "16"),
            ("  10. RTL Output Files", "18"),
            ("  11. RTL Integration", "20"),
            ("Part 4: VIP Generation", ""),
            ("  12. VIP Generation Process", "22"),
            ("  13. VIP Output Structure", "24"),
            ("  14. VIP Simulation Setup", "26"),
            ("Part 5: Complete Workflows", ""),
            ("  15. Complete Example Workflow", "28"),
            ("  16. Advanced GUI Features", "30"),
            ("  17. Troubleshooting", "32"),
            ("Part 6: Real Examples", ""),
            ("  18. Example: 2×3 System", "34"),
            ("  19. Example: Complex System", "36"),
            ("  20. Common Design Patterns", "38")
        ]
        
        y_pos = 0.88
        for item, page in toc_items:
            if item.startswith("Part"):
                # Part headers
                ax.text(0.1, y_pos, item, fontsize=14, weight='bold', 
                       transform=ax.transAxes)
                y_pos -= 0.04
            else:
                # Chapter items
                ax.text(0.1, y_pos, item, fontsize=12, transform=ax.transAxes)
                if page:
                    ax.text(0.9, y_pos, page, fontsize=12, ha='right', 
                           transform=ax.transAxes)
                y_pos -= 0.035
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_gui_overview(self, pdf):
        """Create GUI overview"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('GUI Overview', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # What the GUI does
        overview_box = FancyBboxPatch((0.05, 0.7), 0.9, 0.25,
                                     boxstyle="round,pad=0.02",
                                     facecolor='lightblue', 
                                     edgecolor='darkblue')
        ax.add_patch(overview_box)
        
        ax.text(0.1, 0.9, 'What the GUI Does:', fontsize=16, weight='bold')
        
        features = [
            "• Visual design of AMBA bus interconnects",
            "• Drag-and-drop master and slave configuration",
            "• Real-time validation and error checking",
            "• Automatic RTL generation (Verilog)",
            "• Complete UVM VIP environment generation",
            "• Project save/load functionality"
        ]
        
        y_pos = 0.85
        for feature in features:
            ax.text(0.12, y_pos, feature, fontsize=12)
            y_pos -= 0.03
            
        # GUI workflow overview
        ax.text(0.1, 0.6, 'Complete GUI Workflow:', fontsize=16, weight='bold')
        
        workflow_steps = [
            "1. Launch GUI → 2. Create/Load Project → 3. Add Masters",
            "4. Add Slaves → 5. Make Connections → 6. Configure Parameters", 
            "7. Validate Design → 8. Generate RTL → 9. Generate VIP"
        ]
        
        y_pos = 0.55
        for step in workflow_steps:
            ax.text(0.1, y_pos, step, fontsize=11, 
                   bbox=dict(boxstyle='round,pad=0.3', facecolor='lightyellow'))
            y_pos -= 0.08
            
        # Key benefits
        benefits_box = FancyBboxPatch((0.05, 0.1), 0.9, 0.2,
                                     boxstyle="round,pad=0.02",
                                     facecolor='lightgreen', 
                                     edgecolor='darkgreen')
        ax.add_patch(benefits_box)
        
        ax.text(0.1, 0.25, 'Key Benefits:', fontsize=14, weight='bold')
        ax.text(0.1, 0.21, '✓ No command-line knowledge required', fontsize=11)
        ax.text(0.1, 0.18, '✓ Visual validation prevents errors', fontsize=11)
        ax.text(0.1, 0.15, '✓ Generates production-ready code', fontsize=11)
        ax.text(0.1, 0.12, '✓ Complete verification environment', fontsize=11)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_launching_gui(self, pdf):
        """Create detailed GUI launching instructions"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Launching the GUI', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Method 1: Shell script
        method1_box = FancyBboxPatch((0.05, 0.75), 0.9, 0.2,
                                    boxstyle="round,pad=0.02",
                                    facecolor='lightgreen', 
                                    edgecolor='darkgreen')
        ax.add_patch(method1_box)
        
        ax.text(0.1, 0.9, 'Method 1: Shell Script (Recommended)', 
               fontsize=14, weight='bold')
        
        steps1 = [
            "Step 1: Open terminal in project directory",
            "Step 2: Navigate to GUI folder:",
            "        cd axi4_vip/gui",
            "Step 3: Run launch script:",
            "        ./launch_gui.sh"
        ]
        
        y_pos = 0.86
        for step in steps1:
            if step.startswith("        "):
                ax.text(0.15, y_pos, step, fontsize=10, family='monospace',
                       bbox=dict(boxstyle='round,pad=0.2', facecolor='white'))
            else:
                ax.text(0.12, y_pos, step, fontsize=11)
            y_pos -= 0.025
            
        # Method 2: Python direct
        method2_box = FancyBboxPatch((0.05, 0.45), 0.9, 0.25,
                                    boxstyle="round,pad=0.02",
                                    facecolor='lightblue', 
                                    edgecolor='darkblue')
        ax.add_patch(method2_box)
        
        ax.text(0.1, 0.65, 'Method 2: Direct Python Launch', 
               fontsize=14, weight='bold')
        
        steps2 = [
            "Step 1: Ensure Python 3.6+ is installed:",
            "        python3 --version",
            "Step 2: Install dependencies (if needed):",
            "        pip3 install -r requirements.txt",
            "Step 3: Launch GUI directly:",
            "        python3 src/bus_matrix_gui.py"
        ]
        
        y_pos = 0.61
        for step in steps2:
            if step.startswith("        "):
                ax.text(0.15, y_pos, step, fontsize=10, family='monospace',
                       bbox=dict(boxstyle='round,pad=0.2', facecolor='white'))
            else:
                ax.text(0.12, y_pos, step, fontsize=11)
            y_pos -= 0.025
            
        # Troubleshooting
        trouble_box = FancyBboxPatch((0.05, 0.15), 0.9, 0.25,
                                    boxstyle="round,pad=0.02",
                                    facecolor='#ffe6e6', 
                                    edgecolor='red')
        ax.add_patch(trouble_box)
        
        ax.text(0.1, 0.35, 'Common Launch Issues:', fontsize=14, weight='bold')
        
        issues = [
            "Problem: 'tkinter not found'",
            "Solution: sudo apt-get install python3-tk",
            "",
            "Problem: 'Permission denied'", 
            "Solution: chmod +x launch_gui.sh",
            "",
            "Problem: GUI window doesn't appear",
            "Solution: Check DISPLAY variable: echo $DISPLAY"
        ]
        
        y_pos = 0.31
        for issue in issues:
            if issue.startswith("Problem:"):
                ax.text(0.12, y_pos, issue, fontsize=11, weight='bold', color='red')
            elif issue.startswith("Solution:"):
                ax.text(0.12, y_pos, issue, fontsize=11, color='green')
            else:
                ax.text(0.12, y_pos, issue, fontsize=11)
            y_pos -= 0.02
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_gui_interface_tour(self, pdf):
        """Create detailed GUI interface tour"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('GUI Interface Tour', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Draw detailed GUI layout
        self._draw_detailed_gui_layout(ax)
        
        # Interface elements explanation
        elements = [
            ("1. Menu Bar", "File, Edit, View, Tools, Help menus"),
            ("2. Toolbar", "Quick access: New, Open, Save, Generate"),
            ("3. Master Panel", "Add/configure master components"),
            ("4. Slave Panel", "Add/configure slave components"),
            ("5. Design Canvas", "Visual design area with grid"),
            ("6. Properties Panel", "Configure selected components"),
            ("7. Connection Panel", "View/edit bus connections"),
            ("8. Status Bar", "Validation messages and progress"),
            ("9. Output Panel", "Generation logs and messages")
        ]
        
        y_pos = 0.3
        ax.text(0.05, 0.35, 'Interface Elements:', fontsize=14, weight='bold')
        
        for elem, desc in elements:
            ax.text(0.05, y_pos, elem, fontsize=11, weight='bold')
            ax.text(0.25, y_pos, desc, fontsize=10, style='italic')
            y_pos -= 0.025
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_new_project_setup(self, pdf):
        """Create new project setup instructions"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Setting Up a New Project', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Step-by-step project setup
        ax.text(0.1, 0.9, 'Creating Your First Bus Matrix Project', 
               fontsize=16, weight='bold')
        
        setup_steps = [
            {
                'step': 'Step 1: Start New Project',
                'details': [
                    '• Click File → New Project (or Ctrl+N)',
                    '• Choose project template or start blank',
                    '• Set project name and location'
                ]
            },
            {
                'step': 'Step 2: Choose Bus Type',
                'details': [
                    '• Select AXI4 (recommended for new designs)',
                    '• Or AXI3 for legacy compatibility',
                    '• Set global parameters (data width, address width)'
                ]
            },
            {
                'step': 'Step 3: Configure Global Settings',
                'details': [
                    '• Data Width: 32, 64, 128, 256, 512 bits',
                    '• Address Width: 32 or 64 bits (typically 32)',
                    '• Clock/Reset naming conventions'
                ]
            },
            {
                'step': 'Step 4: Save Project',
                'details': [
                    '• File → Save Project As...',
                    '• Choose .json format for compatibility',
                    '• Remember location for future use'
                ]
            }
        ]
        
        y_pos = 0.8
        for step_info in setup_steps:
            # Step header
            step_box = FancyBboxPatch((0.05, y_pos-0.02), 0.9, 0.04,
                                     boxstyle="round,pad=0.01",
                                     facecolor='lightblue', 
                                     edgecolor='darkblue')
            ax.add_patch(step_box)
            ax.text(0.1, y_pos, step_info['step'], fontsize=12, weight='bold')
            y_pos -= 0.06
            
            # Step details
            for detail in step_info['details']:
                ax.text(0.15, y_pos, detail, fontsize=10)
                y_pos -= 0.025
            y_pos -= 0.02
            
        # Quick tips
        tips_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.15,
                                 boxstyle="round,pad=0.02",
                                 facecolor='lightyellow', 
                                 edgecolor='orange')
        ax.add_patch(tips_box)
        
        ax.text(0.1, 0.17, '💡 Quick Tips:', fontsize=12, weight='bold')
        tips = [
            "• Start with AXI4 64-bit data width for most designs",
            "• Use descriptive project names (e.g., 'cpu_gpu_ddr_system')",
            "• Save frequently - GUI auto-saves every 5 minutes",
            "• Templates are available in File → Templates menu"
        ]
        
        y_pos = 0.14
        for tip in tips:
            ax.text(0.12, y_pos, tip, fontsize=10)
            y_pos -= 0.025
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_adding_masters_detailed(self, pdf):
        """Create detailed master addition instructions"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Adding Masters to Your Design', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Visual step-by-step
        ax.text(0.1, 0.95, 'Step-by-Step: Adding a Master Component', 
               fontsize=16, weight='bold')
        
        # Step 1: Click Add Master
        step1_box = FancyBboxPatch((0.05, 0.8), 0.9, 0.12,
                                  boxstyle="round,pad=0.02",
                                  facecolor='#e8f4fd', 
                                  edgecolor='blue')
        ax.add_patch(step1_box)
        
        ax.text(0.1, 0.88, 'Step 1: Click "Add Master" Button', 
               fontsize=13, weight='bold')
        ax.text(0.12, 0.85, '• Located in left panel or toolbar', fontsize=11)
        ax.text(0.12, 0.82, '• Alternative: Right-click canvas → Add Master', fontsize=11)
        
        # Step 2: Master appears on canvas
        step2_box = FancyBboxPatch((0.05, 0.65), 0.9, 0.12,
                                  boxstyle="round,pad=0.02",
                                  facecolor='#e8f4fd', 
                                  edgecolor='blue')
        ax.add_patch(step2_box)
        
        ax.text(0.1, 0.73, 'Step 2: Master Icon Appears on Canvas', 
               fontsize=13, weight='bold')
        ax.text(0.12, 0.7, '• Default name: "Master_0", "Master_1", etc.', fontsize=11)
        ax.text(0.12, 0.67, '• Can be dragged to different position', fontsize=11)
        
        # Step 3: Configure master
        step3_box = FancyBboxPatch((0.05, 0.4), 0.9, 0.22,
                                  boxstyle="round,pad=0.02",
                                  facecolor='#e8f4fd', 
                                  edgecolor='blue')
        ax.add_patch(step3_box)
        
        ax.text(0.1, 0.59, 'Step 3: Configure Master Properties', 
               fontsize=13, weight='bold')
        ax.text(0.12, 0.56, '• Double-click master icon OR select and use properties panel', fontsize=11)
        ax.text(0.12, 0.53, '• Configuration Dialog Opens:', fontsize=11, weight='bold')
        
        config_items = [
            "  - Name: Descriptive name (e.g., 'CPU_0', 'DMA_Controller')",
            "  - ID Width: 4-8 bits (affects outstanding transactions)",
            "  - Priority: 0-15 (higher = higher priority in arbitration)",
            "  - QoS Enable: Yes for latency-sensitive masters",
            "  - Security: Secure/Non-secure for TrustZone systems"
        ]
        
        y_pos = 0.5
        for item in config_items:
            ax.text(0.14, y_pos, item, fontsize=10)
            y_pos -= 0.025
            
        # Step 4: Apply settings
        step4_box = FancyBboxPatch((0.05, 0.25), 0.9, 0.12,
                                  boxstyle="round,pad=0.02",
                                  facecolor='#e8f4fd', 
                                  edgecolor='blue')
        ax.add_patch(step4_box)
        
        ax.text(0.1, 0.33, 'Step 4: Apply Configuration', 
               fontsize=13, weight='bold')
        ax.text(0.12, 0.3, '• Click "Apply" or "OK" to save settings', fontsize=11)
        ax.text(0.12, 0.27, '• Master icon updates with new name', fontsize=11)
        
        # Common master types
        types_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.17,
                                  boxstyle="round,pad=0.02",
                                  facecolor='lightgreen', 
                                  edgecolor='darkgreen')
        ax.add_patch(types_box)
        
        ax.text(0.1, 0.19, 'Common Master Types & Settings:', 
               fontsize=12, weight='bold')
        
        master_types = [
            "CPU: ID=4-6 bits, Priority=High, QoS=Yes, Security=Secure",
            "DMA: ID=4-8 bits, Priority=Medium, QoS=Yes, Security=Match data",
            "GPU: ID=6-8 bits, Priority=High, QoS=Yes, Security=Non-secure",
            "Debug: ID=2-4 bits, Priority=Low, QoS=No, Security=Secure"
        ]
        
        y_pos = 0.16
        for mtype in master_types:
            ax.text(0.12, y_pos, f"• {mtype}", fontsize=10)
            y_pos -= 0.025
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_adding_slaves_detailed(self, pdf):
        """Create detailed slave addition instructions"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Adding Slaves to Your Design', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Step-by-Step: Adding a Slave Component', 
               fontsize=16, weight='bold')
        
        # Step 1: Click Add Slave
        step1_box = FancyBboxPatch((0.05, 0.8), 0.9, 0.12,
                                  boxstyle="round,pad=0.02",
                                  facecolor='#f0f8e8', 
                                  edgecolor='darkgreen')
        ax.add_patch(step1_box)
        
        ax.text(0.1, 0.88, 'Step 1: Click "Add Slave" Button', 
               fontsize=13, weight='bold')
        ax.text(0.12, 0.85, '• Located in right panel or toolbar', fontsize=11)
        ax.text(0.12, 0.82, '• Alternative: Right-click canvas → Add Slave', fontsize=11)
        
        # Step 2: Configure slave - most important part
        step2_box = FancyBboxPatch((0.05, 0.35), 0.9, 0.42,
                                  boxstyle="round,pad=0.02",
                                  facecolor='#f0f8e8', 
                                  edgecolor='darkgreen')
        ax.add_patch(step2_box)
        
        ax.text(0.1, 0.74, 'Step 2: Configure Slave Properties (CRITICAL)', 
               fontsize=13, weight='bold')
        ax.text(0.12, 0.71, '• Slave configuration dialog appears automatically', fontsize=11)
        ax.text(0.12, 0.68, '• MUST configure address mapping:', fontsize=11, weight='bold')
        
        # Address configuration details
        addr_config = [
            "Name: Descriptive name (e.g., 'DDR_Memory', 'UART_0')",
            "Base Address: Starting address in hex (e.g., 0x00000000)",
            "Size: Memory/peripheral size (e.g., 1GB, 4KB, 1MB)",
            "Memory Type: Memory or Peripheral",
            "Security: Secure/Non-secure access requirements",
            "Read Latency: Response delay in clock cycles",
            "Write Latency: Response delay in clock cycles"
        ]
        
        y_pos = 0.65
        for config in addr_config:
            ax.text(0.14, y_pos, f"• {config}", fontsize=10)
            y_pos -= 0.03
            
        ax.text(0.12, 0.42, '⚠️  IMPORTANT: No overlapping addresses allowed!', 
               fontsize=11, weight='bold', color='red')
        ax.text(0.12, 0.39, 'GUI will show error if addresses overlap', 
               fontsize=10, color='red')
        
        # Step 3: Address examples
        step3_box = FancyBboxPatch((0.05, 0.15), 0.9, 0.17,
                                  boxstyle="round,pad=0.02",
                                  facecolor='lightyellow', 
                                  edgecolor='orange')
        ax.add_patch(step3_box)
        
        ax.text(0.1, 0.29, 'Example Address Map:', fontsize=12, weight='bold')
        
        addr_examples = [
            "DDR Memory:    Base=0x00000000, Size=1GB   (0x00000000-0x3FFFFFFF)",
            "SRAM:          Base=0x40000000, Size=256MB (0x40000000-0x4FFFFFFF)", 
            "Peripherals:   Base=0x50000000, Size=256MB (0x50000000-0x5FFFFFFF)",
            "Debug ROM:     Base=0xF0000000, Size=64KB  (0xF0000000-0xF000FFFF)"
        ]
        
        y_pos = 0.26
        for example in addr_examples:
            ax.text(0.12, y_pos, example, fontsize=9, family='monospace')
            y_pos -= 0.025
            
        # Quick tips
        ax.text(0.1, 0.1, '💡 Quick Tips:', fontsize=11, weight='bold')
        ax.text(0.12, 0.07, '• Use power-of-2 sizes when possible', fontsize=10)
        ax.text(0.12, 0.04, '• Align base addresses to size boundaries', fontsize=10)
        ax.text(0.12, 0.01, '• Leave gaps for future expansion', fontsize=10)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_making_connections_detailed(self, pdf):
        """Create detailed connection instructions"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Making Bus Connections', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Connecting Masters to Slaves', fontsize=16, weight='bold')
        
        # Method 1: Drag and Drop
        method1_box = FancyBboxPatch((0.05, 0.75), 0.9, 0.17,
                                    boxstyle="round,pad=0.02",
                                    facecolor='lightblue', 
                                    edgecolor='darkblue')
        ax.add_patch(method1_box)
        
        ax.text(0.1, 0.89, 'Method 1: Drag and Drop (Recommended)', 
               fontsize=13, weight='bold')
        
        drag_steps = [
            "1. Click and hold on master output port (right side of master)",
            "2. Drag mouse to slave input port (left side of slave)",
            "3. Release mouse - connection line appears",
            "4. Connection is automatically validated"
        ]
        
        y_pos = 0.86
        for step in drag_steps:
            ax.text(0.12, y_pos, step, fontsize=11)
            y_pos -= 0.025
            
        # Visual representation of drag and drop
        self._draw_connection_demo(ax, 0.7, 0.78)
        
        # Method 2: Connection Matrix
        method2_box = FancyBboxPatch((0.05, 0.5), 0.9, 0.2,
                                    boxstyle="round,pad=0.02",
                                    facecolor='lightgreen', 
                                    edgecolor='darkgreen')
        ax.add_patch(method2_box)
        
        ax.text(0.1, 0.67, 'Method 2: Connection Matrix', 
               fontsize=13, weight='bold')
        
        matrix_steps = [
            "1. Click 'View' → 'Connection Matrix' (or Ctrl+M)",
            "2. Matrix shows all masters (rows) vs slaves (columns)",
            "3. Click checkboxes to enable/disable connections",
            "4. Click 'Apply' to update visual design"
        ]
        
        y_pos = 0.64
        for step in matrix_steps:
            ax.text(0.12, y_pos, step, fontsize=11)
            y_pos -= 0.025
            
        # Connection rules
        rules_box = FancyBboxPatch((0.05, 0.25), 0.9, 0.2,
                                  boxstyle="round,pad=0.02",
                                  facecolor='#ffe6e6', 
                                  edgecolor='red')
        ax.add_patch(rules_box)
        
        ax.text(0.1, 0.42, 'Connection Rules & Validation:', 
               fontsize=13, weight='bold')
        
        rules = [
            "✓ Each master can connect to multiple slaves",
            "✓ Each slave can be accessed by multiple masters", 
            "✓ GUI prevents invalid connections automatically",
            "✗ Cannot connect master to master",
            "✗ Cannot connect slave to slave",
            "⚠️  Unconnected masters/slaves show warnings"
        ]
        
        y_pos = 0.39
        for rule in rules:
            color = 'green' if rule.startswith('✓') else 'red' if rule.startswith('✗') else 'orange'
            ax.text(0.12, y_pos, rule, fontsize=11, color=color)
            y_pos -= 0.025
            
        # Connection indicators
        indicators_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.15,
                                       boxstyle="round,pad=0.02",
                                       facecolor='lightyellow', 
                                       edgecolor='orange')
        ax.add_patch(indicators_box)
        
        ax.text(0.1, 0.17, 'Visual Connection Indicators:', 
               fontsize=12, weight='bold')
        
        indicators = [
            "Solid Blue Line: Valid connection",
            "Dashed Red Line: Invalid/problematic connection",
            "Green Dots: Connection endpoints",
            "No line: Components not connected"
        ]
        
        y_pos = 0.14
        for indicator in indicators:
            ax.text(0.12, y_pos, f"• {indicator}", fontsize=10)
            y_pos -= 0.025
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_configuration_parameters(self, pdf):
        """Create configuration parameters guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Configuration Parameters', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Global System Configuration', fontsize=16, weight='bold')
        
        # Global parameters
        global_box = FancyBboxPatch((0.05, 0.75), 0.9, 0.17,
                                   boxstyle="round,pad=0.02",
                                   facecolor='lightblue', 
                                   edgecolor='darkblue')
        ax.add_patch(global_box)
        
        ax.text(0.1, 0.89, 'Access: Edit → Global Parameters', 
               fontsize=12, weight='bold')
        
        global_params = [
            "Bus Type: AXI4, AXI3, AHB (affects generated RTL)",
            "Data Width: 32, 64, 128, 256, 512 bits (system-wide)",
            "Address Width: 32 or 64 bits (memory addressing range)",
            "Clock Domain: Single or multiple clock domains",
            "Reset Style: Synchronous or asynchronous reset"
        ]
        
        y_pos = 0.86
        for param in global_params:
            ax.text(0.12, y_pos, f"• {param}", fontsize=10)
            y_pos -= 0.025
            
        # Interconnect parameters
        interconnect_box = FancyBboxPatch((0.05, 0.5), 0.9, 0.2,
                                         boxstyle="round,pad=0.02",
                                         facecolor='lightgreen', 
                                         edgecolor='darkgreen')
        ax.add_patch(interconnect_box)
        
        ax.text(0.1, 0.67, 'Interconnect Configuration', 
               fontsize=12, weight='bold')
        ax.text(0.12, 0.64, 'Access: Select interconnect → Properties panel', 
               fontsize=11, style='italic')
        
        interconnect_params = [
            "Arbitration: Round-robin, Priority-based, QoS-aware",
            "Pipeline Stages: 0-3 stages (affects timing/area)",
            "Outstanding Transactions: Per-master limits",
            "Timeout Detection: Enable/disable transaction timeouts",
            "Error Handling: SLVERR, DECERR response generation"
        ]
        
        y_pos = 0.61
        for param in interconnect_params:
            ax.text(0.12, y_pos, f"• {param}", fontsize=10)
            y_pos -= 0.025
            
        # Advanced features
        advanced_box = FancyBboxPatch((0.05, 0.25), 0.9, 0.2,
                                     boxstyle="round,pad=0.02",
                                     facecolor='lightyellow', 
                                     edgecolor='orange')
        ax.add_patch(advanced_box)
        
        ax.text(0.1, 0.42, 'Advanced Features (Optional)', 
               fontsize=12, weight='bold')
        
        advanced_params = [
            "QoS (Quality of Service): 4-bit priority levels",
            "Security: TrustZone secure/non-secure regions",
            "Region Support: 4-bit region identifiers",
            "User Signals: Custom user-defined signals",
            "Cache Hints: ARCACHE/AWCACHE signal generation"
        ]
        
        y_pos = 0.39
        for param in advanced_params:
            ax.text(0.12, y_pos, f"• {param}", fontsize=10)
            y_pos -= 0.025
            
        # Configuration tips
        tips_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.15,
                                 boxstyle="round,pad=0.02",
                                 facecolor='#f0f0f0', 
                                 edgecolor='gray')
        ax.add_patch(tips_box)
        
        ax.text(0.1, 0.17, '💡 Configuration Tips:', 
               fontsize=12, weight='bold')
        
        tips = [
            "• Start with defaults, modify only what you need",
            "• Higher data widths = better performance but more area",
            "• QoS only needed for mixed-criticality systems",
            "• Pipeline stages help timing closure in large designs"
        ]
        
        y_pos = 0.14
        for tip in tips:
            ax.text(0.12, y_pos, tip, fontsize=10)
            y_pos -= 0.025
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_rtl_generation_detailed(self, pdf):
        """Create detailed RTL generation instructions"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('RTL Generation Process', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Generating RTL from Your Design', fontsize=16, weight='bold')
        
        # Pre-generation validation
        validation_box = FancyBboxPatch((0.05, 0.8), 0.9, 0.12,
                                       boxstyle="round,pad=0.02",
                                       facecolor='#ffe6e6', 
                                       edgecolor='red')
        ax.add_patch(validation_box)
        
        ax.text(0.1, 0.88, 'STEP 0: Pre-Generation Validation (REQUIRED)', 
               fontsize=13, weight='bold')
        ax.text(0.12, 0.85, '• Click "Tools" → "Validate Design" (or Ctrl+V)', fontsize=11)
        ax.text(0.12, 0.82, '• Fix any errors shown in red before proceeding', fontsize=11)
        
        # RTL generation steps
        rtl_steps = [
            {
                'title': 'STEP 1: Access RTL Generation',
                'color': 'lightblue',
                'details': [
                    '• Click "Generate" → "Generate RTL" (or Ctrl+G)',
                    '• Alternative: Click RTL button in toolbar',
                    '• RTL Generation dialog opens'
                ]
            },
            {
                'title': 'STEP 2: Configure RTL Options',
                'color': 'lightgreen',
                'details': [
                    '• Output Directory: Choose where to save files',
                    '• File Naming: Prefix for generated modules',
                    '• Target: Synthesis (default) or Simulation',
                    '• Include Testbench: Generate basic testbench'
                ]
            },
            {
                'title': 'STEP 3: Generate RTL Files',
                'color': 'lightyellow',
                'details': [
                    '• Click "Generate" button',
                    '• Progress bar shows generation status',
                    '• Output panel shows generated files',
                    '• Success message appears when complete'
                ]
            },
            {
                'title': 'STEP 4: Verify Output',
                'color': 'lightcoral',
                'details': [
                    '• Check output directory for .v files',
                    '• Review generation log for warnings',
                    '• Optionally run syntax check',
                    '• Files ready for synthesis/simulation'
                ]
            }
        ]
        
        y_pos = 0.75
        for step_info in rtl_steps:
            # Step box
            step_box = FancyBboxPatch((0.05, y_pos-0.14), 0.9, 0.14,
                                     boxstyle="round,pad=0.02",
                                     facecolor=step_info['color'], 
                                     edgecolor='black')
            ax.add_patch(step_box)
            
            # Step title
            ax.text(0.1, y_pos-0.02, step_info['title'], 
                   fontsize=12, weight='bold')
            
            # Step details
            detail_y = y_pos - 0.05
            for detail in step_info['details']:
                ax.text(0.12, detail_y, detail, fontsize=10)
                detail_y -= 0.025
                
            y_pos -= 0.16
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_rtl_output_explanation(self, pdf):
        """Create RTL output explanation"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Understanding RTL Output Files', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Generated RTL File Structure', fontsize=16, weight='bold')
        
        # File structure
        structure_box = FancyBboxPatch((0.05, 0.65), 0.9, 0.27,
                                      boxstyle="round,pad=0.02",
                                      facecolor='lightgray', 
                                      edgecolor='black')
        ax.add_patch(structure_box)
        
        ax.text(0.1, 0.89, 'Generated Files (Example for 2 masters, 3 slaves):', 
               fontsize=12, weight='bold')
        
        files = [
            "output_rtl/",
            "├── axi4_interconnect_m2s3.v      # Top-level interconnect",
            "├── axi4_address_decoder.v        # Address decoding logic", 
            "├── axi4_arbiter.v               # Arbitration logic",
            "├── axi4_router.v                # Transaction routing",
            "├── tb_axi4_interconnect.v       # Basic testbench",
            "└── run_synthesis.tcl            # Synthesis script"
        ]
        
        y_pos = 0.86
        for file_item in files:
            if file_item.endswith('/'):
                ax.text(0.12, y_pos, file_item, fontsize=11, weight='bold')
            else:
                ax.text(0.12, y_pos, file_item, fontsize=10, family='monospace')
            y_pos -= 0.025
            
        # File descriptions
        desc_box = FancyBboxPatch((0.05, 0.35), 0.9, 0.27,
                                 boxstyle="round,pad=0.02",
                                 facecolor='lightblue', 
                                 edgecolor='darkblue')
        ax.add_patch(desc_box)
        
        ax.text(0.1, 0.59, 'File Descriptions:', fontsize=12, weight='bold')
        
        descriptions = [
            "axi4_interconnect_m2s3.v: Main module to instantiate in your design",
            "axi4_address_decoder.v: Decodes addresses to route to correct slave",
            "axi4_arbiter.v: Handles multiple masters accessing same slave",
            "axi4_router.v: Routes transactions between masters and slaves",
            "tb_axi4_interconnect.v: Basic testbench for functional verification"
        ]
        
        y_pos = 0.56
        for desc in descriptions:
            ax.text(0.12, y_pos, f"• {desc}", fontsize=10)
            y_pos -= 0.03
            
        # Integration instructions
        integration_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.27,
                                        boxstyle="round,pad=0.02",
                                        facecolor='lightgreen', 
                                        edgecolor='darkgreen')
        ax.add_patch(integration_box)
        
        ax.text(0.1, 0.29, 'How to Use Generated RTL:', fontsize=12, weight='bold')
        
        usage_steps = [
            "1. Copy generated .v files to your project directory",
            "2. Add files to your synthesis/simulation tool",
            "3. Instantiate axi4_interconnect_m2s3 in your top module:",
            "",
            "   axi4_interconnect_m2s3 u_interconnect (",
            "     .clk(clk),",
            "     .rst_n(rst_n),",
            "     // Master 0 interface",
            "     .m0_axi_awvalid(cpu_awvalid),",
            "     .m0_axi_awready(cpu_awready),",
            "     // ... other signals",
            "   );",
            "",
            "4. Connect your masters and slaves to the interface ports"
        ]
        
        y_pos = 0.26
        for step in usage_steps:
            if step.startswith("   "):
                ax.text(0.14, y_pos, step, fontsize=9, family='monospace',
                       bbox=dict(boxstyle='round,pad=0.1', facecolor='white'))
            else:
                ax.text(0.12, y_pos, step, fontsize=10)
            y_pos -= 0.015
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_rtl_integration_steps(self, pdf):
        """Create RTL integration steps"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('RTL Integration Steps', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Integrating Generated RTL into Your Design', 
               fontsize=16, weight='bold')
        
        # Integration workflow
        workflow_steps = [
            {
                'title': 'Step 1: Prepare Your Environment',
                'details': [
                    '• Create project in your synthesis tool (Vivado, Quartus, etc.)',
                    '• Set up directory structure for RTL files',
                    '• Ensure proper tool versions and settings'
                ]
            },
            {
                'title': 'Step 2: Add Generated Files',
                'details': [
                    '• Copy all .v files from output directory',
                    '• Add files to project (maintaining hierarchy)',
                    '• Set axi4_interconnect_m2s3.v as top-level if standalone'
                ]
            },
            {
                'title': 'Step 3: Create Wrapper Module',
                'details': [
                    '• Create your system top-level module',
                    '• Instantiate interconnect with proper port connections',
                    '• Add clock/reset generation logic'
                ]
            },
            {
                'title': 'Step 4: Connect Masters and Slaves',
                'details': [
                    '• Connect CPU, DMA, GPU to master ports',
                    '• Connect memories, peripherals to slave ports',
                    '• Ensure signal widths match interconnect interface'
                ]
            },
            {
                'title': 'Step 5: Verify and Synthesize',
                'details': [
                    '• Run syntax check on all files',
                    '• Simulate basic functionality',
                    '• Run synthesis and check for errors',
                    '• Analyze resource utilization and timing'
                ]
            }
        ]
        
        y_pos = 0.85
        for step_info in workflow_steps:
            # Step header
            step_box = FancyBboxPatch((0.05, y_pos-0.02), 0.9, 0.03,
                                     boxstyle="round,pad=0.01",
                                     facecolor='lightblue', 
                                     edgecolor='darkblue')
            ax.add_patch(step_box)
            ax.text(0.1, y_pos, step_info['title'], fontsize=12, weight='bold')
            y_pos -= 0.05
            
            # Step details
            for detail in step_info['details']:
                ax.text(0.12, y_pos, f"• {detail}", fontsize=10)
                y_pos -= 0.025
            y_pos -= 0.02
            
        # Common issues
        issues_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.15,
                                   boxstyle="round,pad=0.02",
                                   facecolor='#ffe6e6', 
                                   edgecolor='red')
        ax.add_patch(issues_box)
        
        ax.text(0.1, 0.17, 'Common Integration Issues:', fontsize=12, weight='bold')
        
        issues = [
            "Port width mismatch: Check master/slave interface widths",
            "Clock domain crossing: Add proper synchronizers",
            "Reset timing: Ensure reset is properly distributed",
            "Synthesis warnings: Review and fix constraint violations"
        ]
        
        y_pos = 0.14
        for issue in issues:
            ax.text(0.12, y_pos, f"• {issue}", fontsize=10)
            y_pos -= 0.025
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_vip_generation_detailed(self, pdf):
        """Create detailed VIP generation instructions"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('VIP Generation Process', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Generating UVM VIP from Your Design', fontsize=16, weight='bold')
        
        # What is VIP explanation
        vip_explanation = FancyBboxPatch((0.05, 0.8), 0.9, 0.12,
                                        boxstyle="round,pad=0.02",
                                        facecolor='lightcyan', 
                                        edgecolor='darkblue')
        ax.add_patch(vip_explanation)
        
        ax.text(0.1, 0.88, 'What is VIP (Verification Intellectual Property)?', 
               fontsize=12, weight='bold')
        ax.text(0.12, 0.85, '• Complete UVM-based verification environment', fontsize=10)
        ax.text(0.12, 0.82, '• Includes agents, sequences, tests, and scoreboards', fontsize=10)
        
        # VIP generation steps
        vip_steps = [
            {
                'title': 'STEP 1: Access VIP Generation',
                'color': 'lightblue',
                'details': [
                    '• Ensure RTL is generated first (VIP needs RTL files)',
                    '• Click "Generate" → "Generate VIP" (or Ctrl+Shift+G)',
                    '• VIP Generation dialog opens'
                ]
            },
            {
                'title': 'STEP 2: Configure VIP Options',
                'color': 'lightgreen',
                'details': [
                    '• Output Directory: Choose VIP output location',
                    '• Test Suite: Basic, Comprehensive, or Custom',
                    '• Simulator: VCS, Questa, Xcelium, or Generic',
                    '• Coverage: Enable functional and code coverage'
                ]
            },
            {
                'title': 'STEP 3: Generate VIP Environment',
                'color': 'lightyellow',
                'details': [
                    '• Click "Generate VIP" button',
                    '• Progress shows: Agents → Sequences → Tests → Scripts',
                    '• Generation log shows detailed progress',
                    '• Success message when complete'
                ]
            },
            {
                'title': 'STEP 4: Verify VIP Output',
                'color': 'lightcoral',
                'details': [
                    '• Check vip_output/ directory structure',
                    '• Review generated test list',
                    '• Compilation scripts created for target simulator',
                    '• VIP ready for simulation'
                ]
            }
        ]
        
        y_pos = 0.75
        for step_info in vip_steps:
            # Step box
            step_box = FancyBboxPatch((0.05, y_pos-0.12), 0.9, 0.12,
                                     boxstyle="round,pad=0.02",
                                     facecolor=step_info['color'], 
                                     edgecolor='black')
            ax.add_patch(step_box)
            
            # Step title
            ax.text(0.1, y_pos-0.02, step_info['title'], 
                   fontsize=11, weight='bold')
            
            # Step details
            detail_y = y_pos - 0.05
            for detail in step_info['details']:
                ax.text(0.12, detail_y, detail, fontsize=9)
                detail_y -= 0.02
                
            y_pos -= 0.14
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_vip_output_explanation(self, pdf):
        """Create VIP output explanation"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Understanding VIP Output', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Generated VIP Directory Structure', fontsize=16, weight='bold')
        
        # Directory structure
        structure_box = FancyBboxPatch((0.05, 0.6), 0.9, 0.32,
                                      boxstyle="round,pad=0.02",
                                      facecolor='lightgray', 
                                      edgecolor='black')
        ax.add_patch(structure_box)
        
        ax.text(0.1, 0.89, 'VIP Output Structure:', fontsize=12, weight='bold')
        
        vip_structure = [
            "vip_output/",
            "├── env/                    # UVM Environment",
            "│   ├── axi4_env.sv        # Top environment class",
            "│   ├── axi4_scoreboard.sv # Transaction checking",
            "│   └── axi4_coverage.sv   # Functional coverage",
            "├── agents/                 # Master/Slave agents",
            "│   ├── master_agent/      # Master BFM and driver",
            "│   └── slave_agent/       # Slave BFM and driver", 
            "├── sequences/              # Test sequences",
            "│   ├── basic_sequences.sv # Basic read/write",
            "│   ├── burst_sequences.sv # Burst transfers",
            "│   └── error_sequences.sv # Error injection",
            "├── tests/                  # UVM tests",
            "│   ├── base_test.sv       # Base test class",
            "│   ├── basic_test.sv      # Basic functionality",
            "│   └── stress_test.sv     # Stress testing",
            "├── rtl_wrapper/            # RTL integration",
            "│   └── dut_wrapper.sv     # DUT instantiation",
            "└── sim/                    # Simulation scripts",
            "    ├── Makefile           # Build automation",
            "    └── run_sim.sh         # Simulation runner"
        ]
        
        y_pos = 0.86
        for item in vip_structure:
            if '│' in item or '├' in item or '└' in item:
                ax.text(0.12, y_pos, item, fontsize=9, family='monospace')
            else:
                ax.text(0.12, y_pos, item, fontsize=10, family='monospace', weight='bold')
            y_pos -= 0.015
            
        # Key components explanation
        components_box = FancyBboxPatch((0.05, 0.25), 0.9, 0.32,
                                       boxstyle="round,pad=0.02",
                                       facecolor='lightblue', 
                                       edgecolor='darkblue')
        ax.add_patch(components_box)
        
        ax.text(0.1, 0.54, 'Key VIP Components:', fontsize=12, weight='bold')
        
        components = [
            "Environment (env/): Top-level UVM environment coordinating all agents",
            "Agents (agents/): Master and slave BFMs with drivers and monitors",
            "Sequences (sequences/): Reusable transaction sequences for testing",
            "Tests (tests/): Complete test scenarios with pass/fail criteria",
            "RTL Wrapper: Integration layer connecting VIP to generated RTL",
            "Simulation Scripts: Automated compilation and execution scripts"
        ]
        
        y_pos = 0.51
        for component in components:
            ax.text(0.12, y_pos, f"• {component}", fontsize=10)
            y_pos -= 0.035
            
        # Usage instructions
        usage_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.17,
                                  boxstyle="round,pad=0.02",
                                  facecolor='lightgreen', 
                                  edgecolor='darkgreen')
        ax.add_patch(usage_box)
        
        ax.text(0.1, 0.19, 'How to Use Generated VIP:', fontsize=12, weight='bold')
        
        usage_steps = [
            "1. Navigate to vip_output/sim/ directory",
            "2. Run: make compile (compiles all VIP and RTL)",
            "3. Run: make sim TEST=basic_test (runs specific test)",
            "4. View results in logs/ directory",
            "5. Open waveforms for debugging: verdi -ssf waves.fsdb"
        ]
        
        y_pos = 0.16
        for step in usage_steps:
            ax.text(0.12, y_pos, step, fontsize=10)
            y_pos -= 0.025
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_vip_simulation_steps(self, pdf):
        """Create VIP simulation steps"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Running VIP Simulations', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Step-by-Step VIP Simulation Guide', fontsize=16, weight='bold')
        
        # Simulation steps
        sim_steps = [
            {
                'title': 'Step 1: Setup Environment',
                'details': [
                    'cd vip_output/sim',
                    'source /path/to/simulator/setup.sh  # VCS, Questa, etc.',
                    'export UVM_HOME=/path/to/uvm/library'
                ],
                'color': 'lightblue'
            },
            {
                'title': 'Step 2: Compile VIP and RTL',
                'details': [
                    'make compile                    # Compile everything',
                    '# OR compile manually:',
                    'vcs -sverilog -ntb_opts uvm -f compile.f'
                ],
                'color': 'lightgreen'
            },
            {
                'title': 'Step 3: Run Basic Test',
                'details': [
                    'make sim TEST=basic_test        # Run basic test',
                    '# OR run manually:',
                    './simv +UVM_TESTNAME=basic_test +UVM_VERBOSITY=LOW'
                ],
                'color': 'lightyellow'
            },
            {
                'title': 'Step 4: View Results',
                'details': [
                    'cat logs/basic_test.log         # View test log',
                    'verdi -ssf waves/basic_test.fsdb # View waveforms',
                    'firefox coverage_report.html    # View coverage'
                ],
                'color': 'lightcoral'
            }
        ]
        
        y_pos = 0.85
        for step_info in sim_steps:
            # Step header
            step_box = FancyBboxPatch((0.05, y_pos-0.15), 0.9, 0.15,
                                     boxstyle="round,pad=0.02",
                                     facecolor=step_info['color'], 
                                     edgecolor='black')
            ax.add_patch(step_box)
            ax.text(0.1, y_pos-0.02, step_info['title'], fontsize=12, weight='bold')
            
            # Commands
            cmd_y = y_pos - 0.05
            for cmd in step_info['details']:
                if cmd.startswith('#'):
                    ax.text(0.12, cmd_y, cmd, fontsize=9, style='italic', color='gray')
                else:
                    ax.text(0.12, cmd_y, cmd, fontsize=10, family='monospace',
                           bbox=dict(boxstyle='round,pad=0.2', facecolor='white'))
                cmd_y -= 0.025
                
            y_pos -= 0.17
            
        # Available tests
        tests_box = FancyBboxPatch((0.05, 0.15), 0.9, 0.15,
                                  boxstyle="round,pad=0.02",
                                  facecolor='#f0f8ff', 
                                  edgecolor='blue')
        ax.add_patch(tests_box)
        
        ax.text(0.1, 0.27, 'Available Test Suite:', fontsize=12, weight='bold')
        
        tests = [
            "basic_test: Simple read/write operations",
            "burst_test: Various burst types and sizes", 
            "stress_test: High-traffic scenarios",
            "error_test: Error injection and recovery",
            "coverage_test: Maximum coverage collection"
        ]
        
        y_pos = 0.24
        for test in tests:
            ax.text(0.12, y_pos, f"• {test}", fontsize=10)
            y_pos -= 0.025
            
        # Debugging tips
        debug_box = FancyBboxPatch((0.05, 0.02), 0.9, 0.1,
                                  boxstyle="round,pad=0.02",
                                  facecolor='lightyellow', 
                                  edgecolor='orange')
        ax.add_patch(debug_box)
        
        ax.text(0.1, 0.1, '🔧 Debugging Tips:', fontsize=11, weight='bold')
        ax.text(0.12, 0.07, '• Use +UVM_VERBOSITY=HIGH for detailed logs', fontsize=9)
        ax.text(0.12, 0.04, '• Enable waveform dumping: +fsdb+all', fontsize=9)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_complete_workflow_example(self, pdf):
        """Create complete workflow example"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Complete Workflow: CPU + GPU + DDR System', fontsize=18, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Real Example: Building a CPU+GPU+DDR System', 
               fontsize=16, weight='bold')
        
        # System overview
        overview_box = FancyBboxPatch((0.05, 0.85), 0.9, 0.08,
                                     boxstyle="round,pad=0.02",
                                     facecolor='lightcyan', 
                                     edgecolor='darkblue')
        ax.add_patch(overview_box)
        
        ax.text(0.1, 0.89, 'System Goal: 2 Masters (CPU, GPU) → 3 Slaves (DDR, SRAM, Peripherals)', 
               fontsize=11, weight='bold')
        
        # Complete workflow
        workflow = [
            "1. Launch GUI: ./launch_gui.sh",
            "2. New Project: File → New Project → 'cpu_gpu_system'",
            "3. Add CPU Master:",
            "   - Click 'Add Master' → Name: 'CPU_0'",
            "   - ID Width: 4, Priority: 2, QoS: Yes, Security: Secure",
            "4. Add GPU Master:", 
            "   - Click 'Add Master' → Name: 'GPU_0'",
            "   - ID Width: 6, Priority: 1, QoS: Yes, Security: Non-secure",
            "5. Add DDR Slave:",
            "   - Click 'Add Slave' → Name: 'DDR_Memory'",
            "   - Base: 0x00000000, Size: 2GB, Type: Memory",
            "6. Add SRAM Slave:",
            "   - Click 'Add Slave' → Name: 'SRAM_Cache'", 
            "   - Base: 0x80000000, Size: 256MB, Type: Memory",
            "7. Add Peripheral Slave:",
            "   - Click 'Add Slave' → Name: 'Peripherals'",
            "   - Base: 0xA0000000, Size: 256MB, Type: Peripheral",
            "8. Make Connections:",
            "   - Drag CPU_0 → DDR_Memory, SRAM_Cache, Peripherals",
            "   - Drag GPU_0 → DDR_Memory, SRAM_Cache (no peripherals)",
            "9. Validate: Tools → Validate Design (fix any errors)",
            "10. Generate RTL: Generate → Generate RTL → output_rtl/",
            "11. Generate VIP: Generate → Generate VIP → vip_output/",
            "12. Test VIP: cd vip_output/sim && make sim TEST=basic_test"
        ]
        
        y_pos = 0.82
        for step in workflow:
            if step[0].isdigit() and not step.startswith("   "):
                # Main steps
                ax.text(0.1, y_pos, step, fontsize=10, weight='bold')
            else:
                # Sub-steps
                ax.text(0.12, y_pos, step, fontsize=9)
            y_pos -= 0.025
            
        # Expected results
        results_box = FancyBboxPatch((0.05, 0.02), 0.9, 0.15,
                                    boxstyle="round,pad=0.02",
                                    facecolor='lightgreen', 
                                    edgecolor='darkgreen')
        ax.add_patch(results_box)
        
        ax.text(0.1, 0.14, 'Expected Results:', fontsize=12, weight='bold')
        
        results = [
            "✓ RTL: axi4_interconnect_m2s3.v + support files (~5 files)",
            "✓ VIP: Complete UVM environment (~50+ files)",
            "✓ Simulation: All tests pass with 100% functional coverage",
            "✓ Ready for: Synthesis, FPGA implementation, ASIC flow"
        ]
        
        y_pos = 0.11
        for result in results:
            ax.text(0.12, y_pos, result, fontsize=10, color='darkgreen')
            y_pos -= 0.025
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_advanced_gui_features(self, pdf):
        """Create advanced GUI features guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Advanced GUI Features', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Advanced features list
        features = [
            {
                'title': 'Project Templates',
                'description': 'Pre-configured system templates',
                'usage': 'File → New From Template → Select template'
            },
            {
                'title': 'Batch Generation',
                'description': 'Generate multiple configurations',
                'usage': 'Tools → Batch Generation → Configure variants'
            },
            {
                'title': 'Address Map Viewer',
                'description': 'Visual address space layout',
                'usage': 'View → Address Map → Interactive viewer'
            },
            {
                'title': 'Performance Analysis',
                'description': 'Bandwidth and latency analysis',
                'usage': 'Tools → Performance Analysis → Run analysis'
            },
            {
                'title': 'Design Rule Check',
                'description': 'Comprehensive design validation',
                'usage': 'Tools → Design Rule Check → Full validation'
            },
            {
                'title': 'Export/Import',
                'description': 'Configuration file management',
                'usage': 'File → Export/Import → Various formats'
            }
        ]
        
        y_pos = 0.9
        for feature in features:
            # Feature box
            feature_box = FancyBboxPatch((0.05, y_pos-0.1), 0.9, 0.1,
                                        boxstyle="round,pad=0.02",
                                        facecolor='lightblue', 
                                        edgecolor='darkblue')
            ax.add_patch(feature_box)
            
            ax.text(0.1, y_pos-0.02, feature['title'], fontsize=12, weight='bold')
            ax.text(0.1, y_pos-0.05, feature['description'], fontsize=10)
            ax.text(0.1, y_pos-0.08, f"Usage: {feature['usage']}", fontsize=9, style='italic')
            
            y_pos -= 0.12
            
        # Keyboard shortcuts
        shortcuts_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.2,
                                      boxstyle="round,pad=0.02",
                                      facecolor='lightyellow', 
                                      edgecolor='orange')
        ax.add_patch(shortcuts_box)
        
        ax.text(0.1, 0.22, 'Keyboard Shortcuts:', fontsize=12, weight='bold')
        
        shortcuts = [
            "Ctrl+N: New Project          Ctrl+G: Generate RTL",
            "Ctrl+O: Open Project         Ctrl+Shift+G: Generate VIP", 
            "Ctrl+S: Save Project         Ctrl+V: Validate Design",
            "Ctrl+M: Connection Matrix    F5: Refresh Canvas",
            "Delete: Remove Selected      Ctrl+Z: Undo"
        ]
        
        y_pos = 0.19
        for shortcut in shortcuts:
            ax.text(0.12, y_pos, shortcut, fontsize=10, family='monospace')
            y_pos -= 0.025
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_troubleshooting_gui(self, pdf):
        """Create GUI troubleshooting guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('GUI Troubleshooting', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Common issues and solutions
        issues = [
            {
                'problem': 'GUI won\'t launch',
                'symptoms': ['Command not found', 'Permission denied'],
                'solutions': [
                    'chmod +x launch_gui.sh',
                    'sudo apt-get install python3-tk',
                    'Check Python 3.6+ is installed'
                ]
            },
            {
                'problem': 'Can\'t add masters/slaves',
                'symptoms': ['Buttons greyed out', 'No response to clicks'],
                'solutions': [
                    'Create new project first',
                    'Check project is not read-only',
                    'Restart GUI and try again'
                ]
            },
            {
                'problem': 'Address overlap errors',
                'symptoms': ['Red error messages', 'Can\'t generate RTL'],
                'solutions': [
                    'Check slave address ranges',
                    'Use Address Map viewer',
                    'Adjust base addresses or sizes'
                ]
            },
            {
                'problem': 'RTL generation fails',
                'symptoms': ['Generation stops', 'Error in output panel'],
                'solutions': [
                    'Run validation first (Ctrl+V)',
                    'Fix all validation errors',
                    'Check output directory permissions'
                ]
            },
            {
                'problem': 'VIP generation fails',
                'symptoms': ['Missing VIP files', 'Compilation errors'],
                'solutions': [
                    'Generate RTL first',
                    'Check RTL files exist',
                    'Verify simulator setup'
                ]
            }
        ]
        
        y_pos = 0.9
        for issue in issues:
            # Problem header
            problem_box = FancyBboxPatch((0.05, y_pos-0.03), 0.9, 0.03,
                                        boxstyle="round,pad=0.01",
                                        facecolor='#ffe6e6', 
                                        edgecolor='red')
            ax.add_patch(problem_box)
            ax.text(0.1, y_pos-0.015, f"Problem: {issue['problem']}", 
                   fontsize=11, weight='bold')
            y_pos -= 0.05
            
            # Symptoms
            ax.text(0.12, y_pos, "Symptoms:", fontsize=10, weight='bold')
            y_pos -= 0.02
            for symptom in issue['symptoms']:
                ax.text(0.15, y_pos, f"• {symptom}", fontsize=9)
                y_pos -= 0.02
                
            # Solutions
            ax.text(0.12, y_pos, "Solutions:", fontsize=10, weight='bold', color='green')
            y_pos -= 0.02
            for solution in issue['solutions']:
                ax.text(0.15, y_pos, f"• {solution}", fontsize=9, color='green')
                y_pos -= 0.02
                
            y_pos -= 0.02
            
        # Getting help
        help_box = FancyBboxPatch((0.05, 0.02), 0.9, 0.08,
                                 boxstyle="round,pad=0.02",
                                 facecolor='lightblue', 
                                 edgecolor='darkblue')
        ax.add_patch(help_box)
        
        ax.text(0.1, 0.08, 'Getting Additional Help:', fontsize=12, weight='bold')
        ax.text(0.12, 0.05, '• Check Help → User Manual for detailed documentation', fontsize=10)
        ax.text(0.12, 0.03, '• Enable debug logging: Help → Enable Debug Logging', fontsize=10)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_example_2x3_system(self, pdf):
        """Create 2x3 system example"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Example: 2×3 System Design', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Building a 2 Master × 3 Slave System', 
               fontsize=16, weight='bold')
        
        # System diagram
        self._draw_2x3_system_example(ax, 0.5, 0.8, 0.3)
        
        # Configuration table
        config_box = FancyBboxPatch((0.05, 0.4), 0.9, 0.3,
                                   boxstyle="round,pad=0.02",
                                   facecolor='lightgray', 
                                   edgecolor='black')
        ax.add_patch(config_box)
        
        ax.text(0.1, 0.67, 'Component Configuration:', fontsize=14, weight='bold')
        
        # Masters table
        ax.text(0.1, 0.63, 'Masters:', fontsize=12, weight='bold')
        masters_config = [
            "CPU_0:  ID=4, Priority=2, QoS=Yes, Security=Secure",
            "DMA_0:  ID=6, Priority=1, QoS=Yes, Security=Match"
        ]
        
        y_pos = 0.6
        for config in masters_config:
            ax.text(0.12, y_pos, config, fontsize=10, family='monospace')
            y_pos -= 0.025
            
        # Slaves table
        ax.text(0.1, 0.52, 'Slaves:', fontsize=12, weight='bold')
        slaves_config = [
            "DDR:    Base=0x00000000, Size=1GB,   Type=Memory",
            "SRAM:   Base=0x40000000, Size=256MB, Type=Memory", 
            "PERIPH: Base=0x50000000, Size=256MB, Type=Peripheral"
        ]
        
        y_pos = 0.49
        for config in slaves_config:
            ax.text(0.12, y_pos, config, fontsize=10, family='monospace')
            y_pos -= 0.025
            
        # Step by step
        steps_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.32,
                                  boxstyle="round,pad=0.02",
                                  facecolor='lightblue', 
                                  edgecolor='darkblue')
        ax.add_patch(steps_box)
        
        ax.text(0.1, 0.34, 'GUI Steps to Build This System:', fontsize=12, weight='bold')
        
        build_steps = [
            "1. New Project → Name: '2x3_system'",
            "2. Add Master → Name: 'CPU_0', configure as above",
            "3. Add Master → Name: 'DMA_0', configure as above", 
            "4. Add Slave → Name: 'DDR', Base: 0x00000000, Size: 1GB",
            "5. Add Slave → Name: 'SRAM', Base: 0x40000000, Size: 256MB",
            "6. Add Slave → Name: 'PERIPH', Base: 0x50000000, Size: 256MB",
            "7. Connect: CPU_0 → All slaves, DMA_0 → DDR+SRAM only",
            "8. Validate → Generate RTL → Generate VIP",
            "9. Result: axi4_interconnect_m2s3.v + complete VIP"
        ]
        
        y_pos = 0.31
        for step in build_steps:
            ax.text(0.12, y_pos, step, fontsize=10)
            y_pos -= 0.025
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_example_complex_system(self, pdf):
        """Create complex system example"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Example: Complex Multi-Master System', fontsize=18, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.1, 0.95, 'Advanced: 4 Master × 6 Slave System', 
               fontsize=16, weight='bold')
        
        # System overview
        overview_box = FancyBboxPatch((0.05, 0.8), 0.9, 0.12,
                                     boxstyle="round,pad=0.02",
                                     facecolor='lightcyan', 
                                     edgecolor='darkblue')
        ax.add_patch(overview_box)
        
        ax.text(0.1, 0.88, 'System: Multi-core CPU + GPU + AI Accelerator + Debug', 
               fontsize=12, weight='bold')
        ax.text(0.1, 0.85, 'Use Case: High-performance SoC with AI capabilities', 
               fontsize=11)
        ax.text(0.1, 0.82, 'Features: QoS, Security zones, Performance monitoring', 
               fontsize=11)
        
        # Component details
        components = [
            ("Masters:", [
                "CPU_Cluster: 4-bit ID, High priority, Secure",
                "GPU_Engine:  6-bit ID, High priority, Non-secure",
                "AI_Accel:    8-bit ID, Medium priority, Non-secure", 
                "Debug_Port:  2-bit ID, Low priority, Secure"
            ]),
            ("Slaves:", [
                "DDR_0: 0x00000000, 2GB, Main memory",
                "DDR_1: 0x80000000, 2GB, Graphics memory",
                "SRAM:  0x40000000, 512MB, Fast cache",
                "ROM:   0xF0000000, 64MB, Boot code",
                "AI_MEM: 0x60000000, 1GB, AI model storage",
                "PERIPH: 0x50000000, 256MB, System peripherals"
            ])
        ]
        
        y_pos = 0.75
        for comp_type, comp_list in components:
            ax.text(0.1, y_pos, comp_type, fontsize=12, weight='bold')
            y_pos -= 0.03
            
            for comp in comp_list:
                ax.text(0.12, y_pos, f"• {comp}", fontsize=10)
                y_pos -= 0.025
            y_pos -= 0.02
            
        # Advanced configuration
        advanced_box = FancyBboxPatch((0.05, 0.25), 0.9, 0.2,
                                     boxstyle="round,pad=0.02",
                                     facecolor='lightyellow', 
                                     edgecolor='orange')
        ax.add_patch(advanced_box)
        
        ax.text(0.1, 0.42, 'Advanced Configuration Settings:', fontsize=12, weight='bold')
        
        advanced_settings = [
            "• QoS Arbitration: Weighted round-robin with latency bounds",
            "• Security: TrustZone with secure/non-secure partitioning",
            "• Performance: Outstanding transaction limits per master",
            "• Monitoring: Transaction counters and bandwidth meters",
            "• Error Handling: Comprehensive timeout and error injection"
        ]
        
        y_pos = 0.39
        for setting in advanced_settings:
            ax.text(0.12, y_pos, setting, fontsize=10)
            y_pos -= 0.025
            
        # Build complexity
        complexity_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.17,
                                       boxstyle="round,pad=0.02",
                                       facecolor='#ffe6e6', 
                                       edgecolor='red')
        ax.add_patch(complexity_box)
        
        ax.text(0.1, 0.19, 'Build Considerations:', fontsize=12, weight='bold')
        
        considerations = [
            "• Design time: ~30 minutes in GUI vs hours manually",
            "• Generated RTL: ~15 files, ~5000 lines of optimized Verilog",
            "• VIP complexity: 80+ files, comprehensive test suite",
            "• Validation: 20+ test scenarios, full coverage analysis",
            "• Integration: Ready for synthesis and FPGA implementation"
        ]
        
        y_pos = 0.16
        for consideration in considerations:
            ax.text(0.12, y_pos, consideration, fontsize=10)
            y_pos -= 0.025
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_common_patterns(self, pdf):
        """Create common design patterns"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Common Design Patterns', fontsize=20, weight='bold')
        
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Design patterns
        patterns = [
            {
                'title': 'CPU + Memory Pattern',
                'description': '1 Master → 1-2 Slaves (DDR + optional cache)',
                'use_case': 'Simple microcontroller systems',
                'config': 'Master: CPU, ID=4 | Slaves: DDR, SRAM'
            },
            {
                'title': 'Multi-Core Pattern', 
                'description': '2-4 Masters → Shared memory hierarchy',
                'use_case': 'Multi-core processors, parallel computing',
                'config': 'Masters: CPU0-3, ID=4-6 | Slaves: L3, DDR, Peripherals'
            },
            {
                'title': 'SoC Multimedia Pattern',
                'description': 'CPU + GPU + Specialized accelerators',
                'use_case': 'Graphics, video processing, mobile SoCs',
                'config': 'Masters: CPU, GPU, DSP | Slaves: DDR, SRAM, Peripherals'
            },
            {
                'title': 'AI/ML Accelerator Pattern',
                'description': 'CPU + AI engine + High-bandwidth memory',
                'use_case': 'Machine learning inference/training',
                'config': 'Masters: CPU, AI, DMA | Slaves: HBM, DDR, Model cache'
            },
            {
                'title': 'IoT Edge Pattern',
                'description': 'Low-power CPU + Sensor interfaces',
                'use_case': 'IoT devices, sensor networks',
                'config': 'Master: MCU | Slaves: Flash, SRAM, Peripheral hub'
            }
        ]
        
        y_pos = 0.9
        for pattern in patterns:
            # Pattern box
            pattern_box = FancyBboxPatch((0.05, y_pos-0.15), 0.9, 0.15,
                                        boxstyle="round,pad=0.02",
                                        facecolor='lightblue', 
                                        edgecolor='darkblue')
            ax.add_patch(pattern_box)
            
            ax.text(0.1, y_pos-0.02, pattern['title'], fontsize=12, weight='bold')
            ax.text(0.1, y_pos-0.05, pattern['description'], fontsize=10)
            ax.text(0.1, y_pos-0.08, f"Use Case: {pattern['use_case']}", 
                   fontsize=9, style='italic')
            ax.text(0.1, y_pos-0.11, f"Config: {pattern['config']}", 
                   fontsize=9, family='monospace')
            
            y_pos -= 0.17
            
        # Design guidelines
        guidelines_box = FancyBboxPatch((0.05, 0.02), 0.9, 0.1,
                                       boxstyle="round,pad=0.02",
                                       facecolor='lightgreen', 
                                       edgecolor='darkgreen')
        ax.add_patch(guidelines_box)
        
        ax.text(0.1, 0.1, 'Design Guidelines:', fontsize=12, weight='bold')
        ax.text(0.12, 0.07, '• Start simple, add complexity gradually', fontsize=10)
        ax.text(0.12, 0.04, '• Use templates for common patterns', fontsize=10)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    # Helper drawing methods
    def _draw_gui_preview(self, ax, x, y, size):
        """Draw GUI preview"""
        # Window frame
        frame = Rectangle((x-size/2, y-size/2), size, size*0.7, 
                         facecolor='lightgray', edgecolor='black')
        ax.add_patch(frame)
        
        # Menu bar
        menu = Rectangle((x-size/2, y+size/2-0.1), size, 0.1, 
                        facecolor='darkgray', edgecolor='black')
        ax.add_patch(menu)
        
        # Canvas area
        canvas = Rectangle((x-size/2+0.2, y-size/2+0.1), size-0.4, size*0.5, 
                          facecolor='white', edgecolor='black')
        ax.add_patch(canvas)
        
        # Sample components
        master = Circle((x-0.5, y), 0.1, facecolor='lightblue', edgecolor='black')
        slave = Circle((x+0.5, y), 0.1, facecolor='lightgreen', edgecolor='black')
        ax.add_patch(master)
        ax.add_patch(slave)
        
        # Connection line
        ax.plot([x-0.4, x+0.4], [y, y], 'k-', linewidth=2)
        
    def _draw_detailed_gui_layout(self, ax):
        """Draw detailed GUI layout with numbered elements"""
        # Main window
        main_win = Rectangle((0.1, 0.4), 0.8, 0.5, facecolor='white', edgecolor='black')
        ax.add_patch(main_win)
        
        # Menu bar (1)
        menu_bar = Rectangle((0.1, 0.85), 0.8, 0.05, facecolor='lightgray', edgecolor='black')
        ax.add_patch(menu_bar)
        ax.text(0.15, 0.875, '1', fontsize=12, weight='bold', 
               bbox=dict(boxstyle='circle', facecolor='red', alpha=0.7))
        
        # Toolbar (2)
        toolbar = Rectangle((0.1, 0.8), 0.8, 0.05, facecolor='#f0f0f0', edgecolor='black')
        ax.add_patch(toolbar)
        ax.text(0.15, 0.825, '2', fontsize=12, weight='bold',
               bbox=dict(boxstyle='circle', facecolor='red', alpha=0.7))
        
        # Left panels (3,4)
        master_panel = Rectangle((0.1, 0.65), 0.15, 0.15, facecolor='lightblue', edgecolor='black')
        ax.add_patch(master_panel)
        ax.text(0.175, 0.725, '3', fontsize=12, weight='bold',
               bbox=dict(boxstyle='circle', facecolor='red', alpha=0.7))
        
        slave_panel = Rectangle((0.1, 0.5), 0.15, 0.15, facecolor='lightgreen', edgecolor='black')
        ax.add_patch(slave_panel)
        ax.text(0.175, 0.575, '4', fontsize=12, weight='bold',
               bbox=dict(boxstyle='circle', facecolor='red', alpha=0.7))
        
        # Design canvas (5)
        canvas = Rectangle((0.3, 0.5), 0.4, 0.3, facecolor='#fafafa', edgecolor='black')
        ax.add_patch(canvas)
        ax.text(0.5, 0.65, '5', fontsize=12, weight='bold',
               bbox=dict(boxstyle='circle', facecolor='red', alpha=0.7))
        
        # Right panels (6,7)
        props_panel = Rectangle((0.75, 0.65), 0.15, 0.15, facecolor='#f5f5f5', edgecolor='black')
        ax.add_patch(props_panel)
        ax.text(0.825, 0.725, '6', fontsize=12, weight='bold',
               bbox=dict(boxstyle='circle', facecolor='red', alpha=0.7))
        
        conn_panel = Rectangle((0.75, 0.5), 0.15, 0.15, facecolor='#fff5f5', edgecolor='black')
        ax.add_patch(conn_panel)
        ax.text(0.825, 0.575, '7', fontsize=12, weight='bold',
               bbox=dict(boxstyle='circle', facecolor='red', alpha=0.7))
        
        # Status bar (8)
        status_bar = Rectangle((0.1, 0.45), 0.8, 0.05, facecolor='lightgray', edgecolor='black')
        ax.add_patch(status_bar)
        ax.text(0.15, 0.475, '8', fontsize=12, weight='bold',
               bbox=dict(boxstyle='circle', facecolor='red', alpha=0.7))
        
        # Output panel (9)
        output_panel = Rectangle((0.1, 0.4), 0.8, 0.05, facecolor='#f8f8f8', edgecolor='black')
        ax.add_patch(output_panel)
        ax.text(0.15, 0.425, '9', fontsize=12, weight='bold',
               bbox=dict(boxstyle='circle', facecolor='red', alpha=0.7))
        
    def _draw_connection_demo(self, ax, x, y):
        """Draw connection demonstration"""
        # Master
        master = Rectangle((x-0.1, y-0.03), 0.08, 0.06, 
                          facecolor='lightblue', edgecolor='black')
        ax.add_patch(master)
        ax.text(x-0.06, y, 'M', ha='center', fontsize=8, weight='bold')
        
        # Drag arrow
        arrow = patches.FancyArrowPatch((x-0.02, y), (x+0.02, y),
                                      arrowstyle='->', mutation_scale=15,
                                      color='red', linewidth=2, linestyle='--')
        ax.add_patch(arrow)
        
        # Slave
        slave = Rectangle((x+0.02, y-0.03), 0.08, 0.06, 
                         facecolor='lightgreen', edgecolor='black')
        ax.add_patch(slave)
        ax.text(x+0.06, y, 'S', ha='center', fontsize=8, weight='bold')
        
    def _draw_2x3_system_example(self, ax, x, y, size):
        """Draw 2x3 system example"""
        # Masters (left side)
        masters = ['CPU_0', 'DMA_0']
        for i, master in enumerate(masters):
            master_y = y + (i-0.5) * 0.2
            master_rect = Rectangle((x-size, master_y-0.05), 0.15, 0.1,
                                   facecolor='lightblue', edgecolor='black')
            ax.add_patch(master_rect)
            ax.text(x-size+0.075, master_y, master, ha='center', fontsize=9, weight='bold')
            
        # Interconnect (center)
        ic_rect = Rectangle((x-0.075, y-0.15), 0.15, 0.3,
                           facecolor='gray', edgecolor='black')
        ax.add_patch(ic_rect)
        ax.text(x, y, 'AXI4\nIC', ha='center', va='center', 
               fontsize=10, color='white', weight='bold')
        
        # Slaves (right side)
        slaves = ['DDR', 'SRAM', 'PERIPH']
        for i, slave in enumerate(slaves):
            slave_y = y + (i-1) * 0.15
            slave_rect = Rectangle((x+size-0.15, slave_y-0.05), 0.15, 0.1,
                                  facecolor='lightgreen', edgecolor='black')
            ax.add_patch(slave_rect)
            ax.text(x+size-0.075, slave_y, slave, ha='center', fontsize=8, weight='bold')
            
        # Connection lines
        # All connections shown
        for i in range(2):  # Masters
            master_y = y + (i-0.5) * 0.2
            for j in range(3):  # Slaves
                slave_y = y + (j-1) * 0.15
                # CPU connects to all, DMA skips peripherals
                if not (i == 1 and j == 2):  # DMA doesn't connect to PERIPH
                    ax.plot([x-size+0.15, x-0.075], [master_y, master_y], 'k-', linewidth=1)
                    ax.plot([x+0.075, x+size-0.15], [slave_y, slave_y], 'k-', linewidth=1)

def main():
    """Create the complete GUI guide"""
    print("Creating complete GUI usage guide with detailed workflows...")
    guide = CompleteGUIGuide()
    guide.create()

if __name__ == "__main__":
    main()