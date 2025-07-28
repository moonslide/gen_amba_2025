#!/usr/bin/env python3
"""
Create an ultra-comprehensive step-by-step user guide with matplotlib
This guide includes detailed workflows, decision trees, and visual instructions
"""

import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.patches import FancyBboxPatch, Circle, Rectangle, Arrow
import matplotlib.lines as mlines
import numpy as np
from datetime import datetime

class StepByStepGuide:
    """Create ultra-detailed step-by-step guide with visualizations"""
    
    def __init__(self):
        self.filename = "stepbystep_userguide.pdf"
        self.fig_count = 1
        
    def create(self):
        """Create the comprehensive guide"""
        from matplotlib.backends.backend_pdf import PdfPages
        
        with PdfPages(self.filename) as pdf:
            # Cover page
            self.create_cover_page(pdf)
            
            # Table of contents
            self.create_toc(pdf)
            
            # Step 1: Installation
            self.create_installation_steps(pdf)
            
            # Step 2: First Launch
            self.create_first_launch_guide(pdf)
            
            # Step 3: Creating First Design
            self.create_first_design_tutorial(pdf)
            
            # Step 4: Master Configuration
            self.create_master_config_guide(pdf)
            
            # Step 5: Slave Configuration
            self.create_slave_config_guide(pdf)
            
            # Step 6: Making Connections
            self.create_connection_guide(pdf)
            
            # Step 7: Validation
            self.create_validation_guide(pdf)
            
            # Step 8: RTL Generation
            self.create_rtl_generation_guide(pdf)
            
            # Step 9: VIP Generation
            self.create_vip_generation_guide(pdf)
            
            # Step 10: Simulation
            self.create_simulation_guide(pdf)
            
            # Workflow diagrams
            self.create_workflow_diagrams(pdf)
            
            # Decision trees
            self.create_decision_trees(pdf)
            
            # Best practices
            self.create_best_practices(pdf)
            
            # Quick reference
            self.create_quick_reference(pdf)
            
        print(f"\nStep-by-step guide created: {self.filename}")
        import os
        size = os.path.getsize(self.filename) / 1024
        print(f"File size: {size:.1f} KB")
        
    def create_cover_page(self, pdf):
        """Create an attractive cover page"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Background gradient
        gradient = np.linspace(0, 1, 256).reshape(256, 1)
        gradient = np.hstack((gradient, gradient, gradient))
        ax.imshow(gradient, extent=[0, 10, 0, 10], aspect='auto', cmap='Blues_r', alpha=0.3)
        
        # Title
        ax.text(5, 8, 'AMBA Bus Matrix\nConfiguration Tool', 
                fontsize=32, weight='bold', ha='center', va='center',
                bbox=dict(boxstyle='round,pad=1', facecolor='white', alpha=0.8))
        
        # Subtitle
        ax.text(5, 6.5, 'Step-by-Step User Guide', 
                fontsize=24, ha='center', va='center', style='italic')
        
        # Visual elements
        self._draw_bus_icon(ax, 5, 4.5, 2)
        
        # Version info
        ax.text(5, 2, 'Version 1.0.0\nJuly 2025', 
                fontsize=14, ha='center', va='center')
        
        # Ultra-think badge
        ax.text(8.5, 0.5, '🧠 Ultra-Think Edition', 
                fontsize=12, ha='right', va='center',
                bbox=dict(boxstyle='round,pad=0.5', facecolor='yellow', alpha=0.7))
        
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
                transform=ax.transAxes)
        
        toc_items = [
            ("Step 1: Installation and Setup", "3"),
            ("Step 2: First Launch", "5"),
            ("Step 3: Creating Your First Design", "7"),
            ("Step 4: Configuring Masters", "10"),
            ("Step 5: Configuring Slaves", "13"),
            ("Step 6: Making Connections", "16"),
            ("Step 7: Design Validation", "19"),
            ("Step 8: RTL Generation", "22"),
            ("Step 9: VIP Generation", "25"),
            ("Step 10: Running Simulations", "28"),
            ("Workflow Diagrams", "31"),
            ("Decision Trees", "34"),
            ("Best Practices", "37"),
            ("Quick Reference", "40")
        ]
        
        y_pos = 0.85
        for item, page in toc_items:
            ax.text(0.1, y_pos, item, fontsize=14, transform=ax.transAxes)
            ax.text(0.9, y_pos, page, fontsize=14, ha='right', transform=ax.transAxes)
            ax.plot([0.1, 0.9], [y_pos-0.01, y_pos-0.01], 'k--', alpha=0.3, 
                   transform=ax.transAxes)
            y_pos -= 0.06
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_installation_steps(self, pdf):
        """Create installation guide with visual steps"""
        fig = plt.figure(figsize=(8.5, 11))
        
        # Title
        fig.suptitle('Step 1: Installation and Setup', fontsize=20, weight='bold')
        
        # Step flow diagram
        ax1 = plt.subplot(3, 1, 1)
        ax1.set_title('Installation Flow', fontsize=16)
        ax1.axis('off')
        
        steps = ['Check\nPython', 'Install\nDependencies', 'Clone\nRepository', 
                'Verify\nInstallation', 'Ready!']
        x_positions = np.linspace(0.1, 0.9, len(steps))
        
        for i, (step, x) in enumerate(zip(steps, x_positions)):
            # Step box
            box = FancyBboxPatch((x-0.08, 0.3), 0.16, 0.4,
                                boxstyle="round,pad=0.02",
                                facecolor='lightblue' if i < 4 else 'lightgreen',
                                edgecolor='black', linewidth=2)
            ax1.add_patch(box)
            ax1.text(x, 0.5, step, ha='center', va='center', fontsize=12, weight='bold')
            
            # Arrow
            if i < len(steps) - 1:
                arrow = patches.FancyArrowPatch((x+0.08, 0.5), (x_positions[i+1]-0.08, 0.5),
                                              arrowstyle='->', mutation_scale=20,
                                              color='darkgreen', linewidth=2)
                ax1.add_patch(arrow)
        
        ax1.set_xlim(0, 1)
        ax1.set_ylim(0, 1)
        
        # Detailed steps
        ax2 = plt.subplot(3, 1, 2)
        ax2.axis('off')
        ax2.text(0.05, 0.9, 'Detailed Installation Steps:', fontsize=14, weight='bold')
        
        install_steps = [
            "1. Check Python version (requires 3.6+):\n   $ python3 --version",
            "2. Install pip if not available:\n   $ sudo apt-get install python3-pip",
            "3. Clone the repository:\n   $ git clone <repository_url>\n   $ cd gen_amba_2025/axi4_vip/gui",
            "4. Install dependencies:\n   $ pip3 install -r requirements.txt",
            "5. Verify installation:\n   $ python3 -c 'import tkinter; print(\"OK\")'"
        ]
        
        y_pos = 0.7
        for step in install_steps:
            ax2.text(0.05, y_pos, step, fontsize=11, family='monospace',
                    bbox=dict(boxstyle='round,pad=0.5', facecolor='lightyellow'))
            y_pos -= 0.15
            
        # Troubleshooting tips
        ax3 = plt.subplot(3, 1, 3)
        ax3.axis('off')
        ax3.text(0.05, 0.9, '⚠️ Common Issues:', fontsize=14, weight='bold')
        
        issues = [
            "• No tkinter: sudo apt-get install python3-tk",
            "• Permission denied: use 'pip3 install --user'",
            "• Python too old: upgrade to Python 3.6+"
        ]
        
        y_pos = 0.6
        for issue in issues:
            ax3.text(0.05, y_pos, issue, fontsize=11)
            y_pos -= 0.2
            
        plt.tight_layout()
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_first_launch_guide(self, pdf):
        """Create first launch guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Step 2: First Launch', fontsize=20, weight='bold')
        
        # Launch methods
        ax1 = plt.subplot(2, 1, 1)
        ax1.set_title('Launch Methods', fontsize=16)
        ax1.axis('off')
        
        # Method 1
        box1 = FancyBboxPatch((0.05, 0.5), 0.4, 0.4,
                             boxstyle="round,pad=0.02",
                             facecolor='lightgreen', edgecolor='black')
        ax1.add_patch(box1)
        ax1.text(0.25, 0.8, 'Method 1: Shell Script', ha='center', fontsize=12, weight='bold')
        ax1.text(0.25, 0.65, './launch_gui.sh', ha='center', fontsize=11, family='monospace')
        
        # Method 2
        box2 = FancyBboxPatch((0.55, 0.5), 0.4, 0.4,
                             boxstyle="round,pad=0.02",
                             facecolor='lightblue', edgecolor='black')
        ax1.add_patch(box2)
        ax1.text(0.75, 0.8, 'Method 2: Python', ha='center', fontsize=12, weight='bold')
        ax1.text(0.75, 0.65, 'python3 src/bus_matrix_gui.py', ha='center', 
                fontsize=11, family='monospace')
        
        # GUI layout preview
        ax2 = plt.subplot(2, 1, 2)
        ax2.set_title('Main Window Layout', fontsize=16)
        ax2.axis('off')
        
        # Draw GUI mockup
        self._draw_gui_mockup(ax2)
        
        plt.tight_layout()
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_first_design_tutorial(self, pdf):
        """Create first design tutorial"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Step 3: Creating Your First Design', fontsize=20, weight='bold')
        
        # Overview
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # Step-by-step visual
        steps = [
            (0.2, 0.8, "1. Click 'Add Master'", 'lightblue'),
            (0.2, 0.65, "2. Configure Master Properties", 'lightblue'),
            (0.2, 0.5, "3. Click 'Add Slave'", 'lightgreen'),
            (0.2, 0.35, "4. Configure Slave Properties", 'lightgreen'),
            (0.2, 0.2, "5. Connect Master to Slave", 'lightyellow'),
            (0.2, 0.05, "6. Validate Design", 'lightcoral')
        ]
        
        for x, y, text, color in steps:
            # Step box
            box = FancyBboxPatch((x-0.15, y-0.05), 0.7, 0.12,
                               boxstyle="round,pad=0.02",
                               facecolor=color, edgecolor='black')
            ax.add_patch(box)
            ax.text(x, y, text, fontsize=14, weight='bold', va='center')
            
        # Visual representation
        self._draw_simple_bus_system(ax, 0.7, 0.45, 0.25)
        
        # Tips box
        tips_box = FancyBboxPatch((0.05, -0.15), 0.9, 0.15,
                                 boxstyle="round,pad=0.02",
                                 facecolor='lightyellow', edgecolor='orange')
        ax.add_patch(tips_box)
        ax.text(0.5, -0.075, '💡 Tip: Start with a simple 2×2 system to learn the basics',
               ha='center', va='center', fontsize=12)
        
        ax.set_xlim(0, 1)
        ax.set_ylim(-0.2, 1)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_master_config_guide(self, pdf):
        """Create master configuration guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Step 4: Configuring Masters', fontsize=20, weight='bold')
        
        # Configuration panel mockup
        ax1 = plt.subplot(2, 1, 1)
        ax1.set_title('Master Configuration Panel', fontsize=16)
        ax1.axis('off')
        
        # Draw config panel
        panel = Rectangle((0.1, 0.1), 0.8, 0.8, facecolor='lightgray', edgecolor='black')
        ax1.add_patch(panel)
        
        # Configuration fields
        fields = [
            ("Name:", "CPU_0", "Unique identifier"),
            ("Type:", "AXI4", "Protocol type"),
            ("ID Width:", "4", "Transaction ID bits"),
            ("Priority:", "1", "Arbitration priority"),
            ("QoS:", "Enabled", "Quality of Service"),
            ("Security:", "Secure", "TrustZone setting")
        ]
        
        y_pos = 0.8
        for label, value, desc in fields:
            ax1.text(0.15, y_pos, label, fontsize=12, weight='bold')
            ax1.text(0.35, y_pos, value, fontsize=12, 
                    bbox=dict(boxstyle='round,pad=0.3', facecolor='white'))
            ax1.text(0.55, y_pos, f"← {desc}", fontsize=10, style='italic', color='blue')
            y_pos -= 0.12
            
        # Best practices
        ax2 = plt.subplot(2, 1, 2)
        ax2.set_title('Master Configuration Best Practices', fontsize=16)
        ax2.axis('off')
        
        practices = [
            "✓ Use descriptive names (CPU_0, DMA_1, GPU_0)",
            "✓ Set appropriate ID width (4-8 bits typical)",
            "✓ Higher priority = higher arbitration preference",
            "✓ Enable QoS for latency-sensitive masters",
            "✓ Match security settings to system requirements"
        ]
        
        y_pos = 0.8
        for practice in practices:
            ax2.text(0.1, y_pos, practice, fontsize=12)
            y_pos -= 0.15
            
        plt.tight_layout()
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_slave_config_guide(self, pdf):
        """Create slave configuration guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Step 5: Configuring Slaves', fontsize=20, weight='bold')
        
        # Address map visualization
        ax1 = plt.subplot(2, 1, 1)
        ax1.set_title('Address Map Configuration', fontsize=16)
        ax1.axis('off')
        
        # Memory map
        base_y = 0.2
        height = 0.6
        slaves = [
            ("DDR", 0x00000000, 0x40000000, 'lightblue'),
            ("SRAM", 0x40000000, 0x10000000, 'lightgreen'),
            ("Peripherals", 0x50000000, 0x10000000, 'lightyellow'),
            ("Reserved", 0x60000000, 0xA0000000, 'lightgray')
        ]
        
        total_size = 0x100000000
        for name, base, size, color in slaves:
            y_start = base_y + (base / total_size) * height
            y_height = (size / total_size) * height
            
            rect = Rectangle((0.3, y_start), 0.4, y_height, 
                           facecolor=color, edgecolor='black')
            ax1.add_patch(rect)
            ax1.text(0.5, y_start + y_height/2, name, ha='center', va='center', 
                    fontsize=12, weight='bold')
            ax1.text(0.75, y_start + y_height/2, f'0x{base:08X}', fontsize=10, 
                    family='monospace')
            
        ax1.text(0.1, 0.85, 'Address Space', fontsize=14, weight='bold')
        ax1.text(0.3, 0.15, '0x00000000', fontsize=10, family='monospace')
        ax1.text(0.3, 0.8, '0xFFFFFFFF', fontsize=10, family='monospace')
        
        # Configuration tips
        ax2 = plt.subplot(2, 1, 2)
        ax2.set_title('Slave Configuration Tips', fontsize=16)
        ax2.axis('off')
        
        tips = [
            "📍 Align base addresses to size boundaries",
            "📏 Use power-of-2 sizes when possible",
            "🔒 Set appropriate access permissions",
            "⚡ Configure realistic latency values",
            "🎯 Avoid address overlaps"
        ]
        
        y_pos = 0.8
        for tip in tips:
            ax2.text(0.1, y_pos, tip, fontsize=12)
            y_pos -= 0.15
            
        plt.tight_layout()
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_connection_guide(self, pdf):
        """Create connection guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Step 6: Making Connections', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.set_title('Connection Methods', fontsize=16)
        ax.axis('off')
        
        # Method 1: Drag and drop
        ax.text(0.1, 0.85, 'Method 1: Drag and Drop', fontsize=14, weight='bold')
        self._draw_drag_drop_demo(ax, 0.1, 0.7)
        
        # Method 2: Connection matrix
        ax.text(0.1, 0.45, 'Method 2: Connection Matrix', fontsize=14, weight='bold')
        self._draw_connection_matrix(ax, 0.1, 0.3)
        
        # Connection rules
        rules_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.2,
                                  boxstyle="round,pad=0.02",
                                  facecolor='lightyellow', edgecolor='orange')
        ax.add_patch(rules_box)
        ax.text(0.5, 0.18, 'Connection Rules:', fontsize=12, weight='bold', ha='center')
        ax.text(0.5, 0.12, '• Each master can connect to multiple slaves', 
               fontsize=11, ha='center')
        ax.text(0.5, 0.08, '• Each slave can be accessed by multiple masters', 
               fontsize=11, ha='center')
        
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_validation_guide(self, pdf):
        """Create validation guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Step 7: Design Validation', fontsize=20, weight='bold')
        
        # Validation checklist
        ax1 = plt.subplot(2, 1, 1)
        ax1.set_title('Validation Checklist', fontsize=16)
        ax1.axis('off')
        
        checks = [
            ("Address Overlap", "No overlapping slave addresses", True),
            ("Connection Check", "All masters have valid connections", True),
            ("ID Width", "Sufficient ID bits for all masters", True),
            ("Data Width", "Compatible data widths", True),
            ("Security", "Security settings are consistent", False),
            ("Performance", "No bandwidth bottlenecks", True)
        ]
        
        y_pos = 0.9
        for check, desc, passed in checks:
            # Status indicator
            color = 'green' if passed else 'red'
            symbol = '✓' if passed else '✗'
            
            circle = Circle((0.1, y_pos), 0.03, facecolor=color, edgecolor='black')
            ax1.add_patch(circle)
            ax1.text(0.1, y_pos, symbol, ha='center', va='center', 
                    color='white', fontsize=14, weight='bold')
            
            ax1.text(0.2, y_pos, check, fontsize=12, weight='bold')
            ax1.text(0.5, y_pos, desc, fontsize=11, style='italic')
            y_pos -= 0.12
            
        # Error resolution
        ax2 = plt.subplot(2, 1, 2)
        ax2.set_title('Resolving Validation Errors', fontsize=16)
        ax2.axis('off')
        
        error_box = FancyBboxPatch((0.05, 0.5), 0.9, 0.3,
                                  boxstyle="round,pad=0.02",
                                  facecolor='#ffcccc', edgecolor='red')
        ax2.add_patch(error_box)
        ax2.text(0.5, 0.7, '❌ Security settings are inconsistent', 
                ha='center', fontsize=12, weight='bold')
        ax2.text(0.5, 0.6, 'Solution: Ensure secure masters only connect to secure slaves',
                ha='center', fontsize=11)
        
        plt.tight_layout()
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_rtl_generation_guide(self, pdf):
        """Create RTL generation guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Step 8: RTL Generation', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # Generation flow
        ax.text(0.5, 0.9, 'RTL Generation Flow', fontsize=16, weight='bold', ha='center')
        
        # Flow diagram
        flow_steps = [
            (0.5, 0.8, "Validated Design", 'lightblue'),
            (0.5, 0.65, "Click 'Generate RTL'", 'lightgreen'),
            (0.5, 0.5, "Select Output Directory", 'lightyellow'),
            (0.5, 0.35, "Configure Options", 'lightyellow'),
            (0.5, 0.2, "RTL Files Generated", 'lightcoral')
        ]
        
        for i, (x, y, text, color) in enumerate(flow_steps):
            box = FancyBboxPatch((x-0.15, y-0.05), 0.3, 0.08,
                               boxstyle="round,pad=0.02",
                               facecolor=color, edgecolor='black')
            ax.add_patch(box)
            ax.text(x, y, text, ha='center', va='center', fontsize=12, weight='bold')
            
            if i < len(flow_steps) - 1:
                arrow = patches.FancyArrowPatch((x, y-0.05), (x, flow_steps[i+1][1]+0.05),
                                              arrowstyle='->', mutation_scale=20,
                                              color='black', linewidth=2)
                ax.add_patch(arrow)
        
        # Generated files
        files_box = FancyBboxPatch((0.05, 0.01), 0.9, 0.15,
                                  boxstyle="round,pad=0.02",
                                  facecolor='lightgray', edgecolor='black')
        ax.add_patch(files_box)
        ax.text(0.1, 0.12, 'Generated Files:', fontsize=12, weight='bold')
        ax.text(0.1, 0.08, '• axi4_interconnect.v - Top module', fontsize=10)
        ax.text(0.1, 0.05, '• axi4_decoder.v - Address decoder', fontsize=10)
        ax.text(0.55, 0.08, '• axi4_arbiter.v - Arbitration', fontsize=10)
        ax.text(0.55, 0.05, '• tb_axi4.v - Testbench', fontsize=10)
        
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_vip_generation_guide(self, pdf):
        """Create VIP generation guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Step 9: VIP Generation', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # VIP structure
        ax.text(0.5, 0.9, 'VIP Directory Structure', fontsize=16, weight='bold', ha='center')
        
        # Directory tree
        tree_data = [
            (0.2, 0.8, "vip_output/", 'folder'),
            (0.25, 0.75, "├── env/", 'folder'),
            (0.3, 0.7, "│   ├── axi4_env.sv", 'file'),
            (0.3, 0.65, "│   └── axi4_scoreboard.sv", 'file'),
            (0.25, 0.6, "├── sequences/", 'folder'),
            (0.3, 0.55, "│   ├── axi4_base_seq.sv", 'file'),
            (0.3, 0.5, "│   └── axi4_rand_seq.sv", 'file'),
            (0.25, 0.45, "├── tests/", 'folder'),
            (0.3, 0.4, "│   └── axi4_base_test.sv", 'file'),
            (0.25, 0.35, "└── sim/", 'folder'),
            (0.3, 0.3, "    └── run.sh", 'file')
        ]
        
        for x, y, text, ftype in tree_data:
            color = 'lightyellow' if ftype == 'folder' else 'lightblue'
            ax.text(x, y, text, fontsize=11, family='monospace',
                   bbox=dict(boxstyle='round,pad=0.2', facecolor=color))
            
        # Usage instructions
        usage_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.2,
                                  boxstyle="round,pad=0.02",
                                  facecolor='lightgreen', edgecolor='black')
        ax.add_patch(usage_box)
        ax.text(0.5, 0.18, 'To run VIP simulations:', fontsize=12, weight='bold', ha='center')
        ax.text(0.5, 0.13, '1. cd vip_output/sim', fontsize=11, ha='center', family='monospace')
        ax.text(0.5, 0.09, '2. ./run.sh +UVM_TESTNAME=axi4_base_test', fontsize=11, 
               ha='center', family='monospace')
        
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_simulation_guide(self, pdf):
        """Create simulation guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Step 10: Running Simulations', fontsize=20, weight='bold')
        
        # Simulation flow
        ax1 = plt.subplot(2, 1, 1)
        ax1.set_title('Simulation Flow', fontsize=16)
        ax1.axis('off')
        
        # Timeline
        timeline_steps = [
            (0.1, "Compile\nRTL+VIP"),
            (0.3, "Elaborate\nDesign"),
            (0.5, "Run\nSimulation"),
            (0.7, "Analyze\nResults"),
            (0.9, "Debug\n(if needed)")
        ]
        
        y = 0.5
        for x, text in timeline_steps:
            circle = Circle((x, y), 0.05, facecolor='lightblue', edgecolor='black')
            ax1.add_patch(circle)
            ax1.text(x, y-0.15, text, ha='center', fontsize=11)
            
            if x < 0.9:
                ax1.plot([x+0.05, x+0.15], [y, y], 'k-', linewidth=2)
                
        ax1.set_xlim(0, 1)
        ax1.set_ylim(0, 1)
        
        # Common commands
        ax2 = plt.subplot(2, 1, 2)
        ax2.set_title('Simulator Commands', fontsize=16)
        ax2.axis('off')
        
        simulators = [
            ("VCS:", "vcs -sverilog -ntb_opts uvm -f files.f\n./simv +UVM_TESTNAME=test"),
            ("Questa:", "vlog -sv -f files.f\nvsim -c -do \"run -all\""),
            ("Xcelium:", "xrun -sv -uvm -f files.f +UVM_TESTNAME=test")
        ]
        
        y_pos = 0.8
        for sim, cmd in simulators:
            ax2.text(0.1, y_pos, sim, fontsize=12, weight='bold')
            ax2.text(0.25, y_pos-0.05, cmd, fontsize=10, family='monospace',
                    bbox=dict(boxstyle='round,pad=0.3', facecolor='lightgray'))
            y_pos -= 0.25
            
        plt.tight_layout()
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_workflow_diagrams(self, pdf):
        """Create workflow diagrams"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Complete Workflow Diagram', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # Main workflow
        workflow_boxes = [
            (0.1, 0.8, 0.15, 0.1, "Design\nCapture", 'lightblue'),
            (0.3, 0.8, 0.15, 0.1, "Configure\nComponents", 'lightgreen'),
            (0.5, 0.8, 0.15, 0.1, "Connect\nBus Matrix", 'lightyellow'),
            (0.7, 0.8, 0.15, 0.1, "Validate\nDesign", 'lightcoral'),
            
            (0.1, 0.5, 0.15, 0.1, "Generate\nRTL", 'lightblue'),
            (0.3, 0.5, 0.15, 0.1, "Generate\nVIP", 'lightgreen'),
            (0.5, 0.5, 0.15, 0.1, "Run\nSimulation", 'lightyellow'),
            (0.7, 0.5, 0.15, 0.1, "Analyze\nResults", 'lightcoral'),
            
            (0.3, 0.2, 0.15, 0.1, "Synthesis", 'lavender'),
            (0.5, 0.2, 0.15, 0.1, "Integration", 'lavender')
        ]
        
        for x, y, w, h, text, color in workflow_boxes:
            box = FancyBboxPatch((x, y), w, h,
                               boxstyle="round,pad=0.02",
                               facecolor=color, edgecolor='black')
            ax.add_patch(box)
            ax.text(x+w/2, y+h/2, text, ha='center', va='center', 
                   fontsize=11, weight='bold')
        
        # Arrows
        arrows = [
            ((0.25, 0.85), (0.3, 0.85)),
            ((0.45, 0.85), (0.5, 0.85)),
            ((0.65, 0.85), (0.7, 0.85)),
            ((0.775, 0.8), (0.175, 0.6)),  # Down to RTL
            ((0.25, 0.55), (0.3, 0.55)),
            ((0.45, 0.55), (0.5, 0.55)),
            ((0.65, 0.55), (0.7, 0.55)),
            ((0.375, 0.5), (0.375, 0.3)),  # Down to synthesis
            ((0.575, 0.5), (0.575, 0.3))
        ]
        
        for start, end in arrows:
            arrow = patches.FancyArrowPatch(start, end,
                                          arrowstyle='->', mutation_scale=15,
                                          color='black', linewidth=1.5)
            ax.add_patch(arrow)
            
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_decision_trees(self, pdf):
        """Create decision trees"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Design Decision Trees', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # Protocol selection tree
        ax.text(0.5, 0.95, 'Protocol Selection Guide', fontsize=16, weight='bold', ha='center')
        
        # Root
        root = FancyBboxPatch((0.4, 0.85), 0.2, 0.06,
                            boxstyle="round,pad=0.02",
                            facecolor='lightgray', edgecolor='black')
        ax.add_patch(root)
        ax.text(0.5, 0.88, 'Bus Type?', ha='center', fontsize=12, weight='bold')
        
        # Branches
        protocols = [
            (0.15, 0.7, "AXI4", "High performance\nOut-of-order\nBurst up to 256"),
            (0.38, 0.7, "AXI3", "Legacy support\nWrite interleaving\nBurst up to 16"),
            (0.62, 0.7, "AHB", "Lower complexity\nPipelined\nSingle outstanding"),
            (0.85, 0.7, "APB", "Peripherals\nSimple interface\nNo burst")
        ]
        
        for x, y, prot, desc in protocols:
            # Protocol box
            box = FancyBboxPatch((x-0.08, y-0.03), 0.16, 0.06,
                               boxstyle="round,pad=0.02",
                               facecolor='lightblue', edgecolor='black')
            ax.add_patch(box)
            ax.text(x, y, prot, ha='center', fontsize=11, weight='bold')
            
            # Description
            ax.text(x, y-0.1, desc, ha='center', fontsize=9, style='italic')
            
            # Arrow from root
            arrow = patches.FancyArrowPatch((0.5, 0.85), (x, y+0.03),
                                          arrowstyle='->', mutation_scale=10,
                                          color='gray', linewidth=1)
            ax.add_patch(arrow)
            
        # Master count decision
        ax.text(0.5, 0.5, 'Master Count Decision', fontsize=16, weight='bold', ha='center')
        
        decision_box = FancyBboxPatch((0.35, 0.4), 0.3, 0.06,
                                    boxstyle="round,pad=0.02",
                                    facecolor='lightyellow', edgecolor='black')
        ax.add_patch(decision_box)
        ax.text(0.5, 0.43, 'Number of Masters?', ha='center', fontsize=12, weight='bold')
        
        # Options
        master_opts = [
            (0.25, 0.3, "1 Master", "Use AHB-Lite\nNo arbitration"),
            (0.5, 0.3, "2-8 Masters", "Standard config\nRound-robin arb"),
            (0.75, 0.3, ">8 Masters", "Advanced config\nQoS arbitration")
        ]
        
        for x, y, opt, desc in master_opts:
            box = FancyBboxPatch((x-0.08, y-0.03), 0.16, 0.06,
                               boxstyle="round,pad=0.02",
                               facecolor='lightgreen', edgecolor='black')
            ax.add_patch(box)
            ax.text(x, y, opt, ha='center', fontsize=10, weight='bold')
            ax.text(x, y-0.08, desc, ha='center', fontsize=8, style='italic')
            
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_best_practices(self, pdf):
        """Create best practices guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Best Practices', fontsize=20, weight='bold')
        
        # Categories
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        categories = [
            ("🎯 Design Planning", [
                "Start with clear requirements",
                "Document address map early",
                "Plan for future expansion"
            ]),
            ("🔧 Configuration", [
                "Use meaningful component names",
                "Set realistic latency values",
                "Enable only needed features"
            ]),
            ("✅ Validation", [
                "Always validate before generation",
                "Check address overlaps carefully",
                "Verify security settings"
            ]),
            ("🚀 Performance", [
                "Balance master priorities",
                "Consider QoS requirements",
                "Minimize connection complexity"
            ]),
            ("🐛 Debug", [
                "Use descriptive signal names",
                "Enable assertions in RTL",
                "Generate comprehensive testbench"
            ])
        ]
        
        y_pos = 0.9
        for title, practices in categories:
            # Category header
            header_box = FancyBboxPatch((0.05, y_pos-0.03), 0.9, 0.05,
                                      boxstyle="round,pad=0.02",
                                      facecolor='lightblue', edgecolor='black')
            ax.add_patch(header_box)
            ax.text(0.5, y_pos, title, ha='center', fontsize=14, weight='bold')
            y_pos -= 0.07
            
            # Practices
            for practice in practices:
                ax.text(0.1, y_pos, f"• {practice}", fontsize=11)
                y_pos -= 0.04
            y_pos -= 0.03
            
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_quick_reference(self, pdf):
        """Create quick reference card"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Quick Reference Card', fontsize=20, weight='bold')
        
        # Keyboard shortcuts
        ax1 = plt.subplot(2, 2, 1)
        ax1.set_title('Keyboard Shortcuts', fontsize=14)
        ax1.axis('off')
        
        shortcuts = [
            ("Ctrl+N", "New design"),
            ("Ctrl+O", "Open file"),
            ("Ctrl+S", "Save file"),
            ("Ctrl+G", "Generate RTL"),
            ("Ctrl+V", "Validate"),
            ("Delete", "Remove item")
        ]
        
        y_pos = 0.9
        for key, action in shortcuts:
            ax1.text(0.1, y_pos, key, fontsize=10, family='monospace',
                    bbox=dict(boxstyle='round,pad=0.2', facecolor='lightgray'))
            ax1.text(0.5, y_pos, action, fontsize=10)
            y_pos -= 0.15
            
        # Common parameters
        ax2 = plt.subplot(2, 2, 2)
        ax2.set_title('Common Parameters', fontsize=14)
        ax2.axis('off')
        
        params = [
            ("Data Width", "32, 64, 128, 256"),
            ("Addr Width", "32, 64"),
            ("ID Width", "4-16 typical"),
            ("Burst Len", "1-256 (AXI4)"),
            ("QoS", "0-15")
        ]
        
        y_pos = 0.9
        for param, values in params:
            ax2.text(0.1, y_pos, param + ":", fontsize=10, weight='bold')
            ax2.text(0.1, y_pos-0.08, values, fontsize=9, style='italic')
            y_pos -= 0.18
            
        # File locations
        ax3 = plt.subplot(2, 2, 3)
        ax3.set_title('Important Files', fontsize=14)
        ax3.axis('off')
        
        files = [
            ("Config:", "*.json"),
            ("RTL:", "output/rtl/*.v"),
            ("VIP:", "vip_output/"),
            ("Logs:", "logs/*.log")
        ]
        
        y_pos = 0.9
        for label, path in files:
            ax3.text(0.1, y_pos, label, fontsize=10, weight='bold')
            ax3.text(0.35, y_pos, path, fontsize=9, family='monospace')
            y_pos -= 0.2
            
        # Commands
        ax4 = plt.subplot(2, 2, 4)
        ax4.set_title('Command Reference', fontsize=14)
        ax4.axis('off')
        
        commands = [
            "./launch_gui.sh",
            "python3 src/bus_matrix_gui.py",
            "make -C ../.. cleanup",
            "pytest tests/"
        ]
        
        y_pos = 0.9
        for cmd in commands:
            ax4.text(0.1, y_pos, cmd, fontsize=9, family='monospace',
                    bbox=dict(boxstyle='round,pad=0.2', facecolor='lightyellow'))
            y_pos -= 0.2
            
        plt.tight_layout()
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    # Helper methods
    def _draw_bus_icon(self, ax, x, y, size):
        """Draw a simple bus icon"""
        # Masters
        for i in range(2):
            rect = Rectangle((x-size/2, y+i*0.3-0.15), 0.3, 0.25, 
                           facecolor='lightblue', edgecolor='black')
            ax.add_patch(rect)
            ax.text(x-size/2+0.15, y+i*0.3-0.025, 'M', ha='center', fontsize=10)
            
        # Bus
        bus_rect = Rectangle((x-0.15, y-0.3), 0.3, 0.9, 
                           facecolor='gray', edgecolor='black')
        ax.add_patch(bus_rect)
        
        # Slaves
        for i in range(3):
            rect = Rectangle((x+size/2-0.3, y+i*0.3-0.3), 0.3, 0.25, 
                           facecolor='lightgreen', edgecolor='black')
            ax.add_patch(rect)
            ax.text(x+size/2-0.15, y+i*0.3-0.175, 'S', ha='center', fontsize=10)
            
    def _draw_gui_mockup(self, ax):
        """Draw GUI mockup"""
        # Main window
        win = Rectangle((0.1, 0.1), 0.8, 0.8, facecolor='white', edgecolor='black')
        ax.add_patch(win)
        
        # Menu bar
        menu = Rectangle((0.1, 0.85), 0.8, 0.05, facecolor='lightgray', edgecolor='black')
        ax.add_patch(menu)
        ax.text(0.15, 0.875, 'File  Edit  View  Tools  Help', fontsize=10)
        
        # Toolbar
        toolbar = Rectangle((0.1, 0.8), 0.8, 0.05, facecolor='#f0f0f0', edgecolor='black')
        ax.add_patch(toolbar)
        
        # Canvas
        canvas = Rectangle((0.15, 0.2), 0.5, 0.55, facecolor='#fafafa', edgecolor='black')
        ax.add_patch(canvas)
        ax.text(0.4, 0.475, 'Design Canvas', ha='center', fontsize=12, style='italic')
        
        # Properties
        props = Rectangle((0.7, 0.2), 0.15, 0.55, facecolor='#f5f5f5', edgecolor='black')
        ax.add_patch(props)
        ax.text(0.775, 0.7, 'Properties', ha='center', fontsize=10)
        
        # Status bar
        status = Rectangle((0.1, 0.1), 0.8, 0.05, facecolor='lightgray', edgecolor='black')
        ax.add_patch(status)
        ax.text(0.15, 0.125, 'Ready', fontsize=9)
        
    def _draw_simple_bus_system(self, ax, x, y, size):
        """Draw simple bus system"""
        # Masters
        m1 = Rectangle((x-size, y+0.1), 0.1, 0.08, facecolor='lightblue', edgecolor='black')
        m2 = Rectangle((x-size, y-0.1), 0.1, 0.08, facecolor='lightblue', edgecolor='black')
        ax.add_patch(m1)
        ax.add_patch(m2)
        ax.text(x-size+0.05, y+0.14, 'M1', ha='center', fontsize=9)
        ax.text(x-size+0.05, y-0.06, 'M2', ha='center', fontsize=9)
        
        # Interconnect
        ic = Rectangle((x-0.05, y-0.15), 0.1, 0.3, facecolor='gray', edgecolor='black')
        ax.add_patch(ic)
        ax.text(x, y, 'IC', ha='center', fontsize=9, color='white')
        
        # Slaves
        s1 = Rectangle((x+size-0.1, y+0.15), 0.1, 0.08, facecolor='lightgreen', edgecolor='black')
        s2 = Rectangle((x+size-0.1, y), 0.1, 0.08, facecolor='lightgreen', edgecolor='black')
        s3 = Rectangle((x+size-0.1, y-0.15), 0.1, 0.08, facecolor='lightgreen', edgecolor='black')
        ax.add_patch(s1)
        ax.add_patch(s2)
        ax.add_patch(s3)
        ax.text(x+size-0.05, y+0.19, 'S1', ha='center', fontsize=9)
        ax.text(x+size-0.05, y+0.04, 'S2', ha='center', fontsize=9)
        ax.text(x+size-0.05, y-0.11, 'S3', ha='center', fontsize=9)
        
        # Connections
        ax.plot([x-size+0.1, x-0.05], [y+0.14, y+0.05], 'k-', linewidth=1)
        ax.plot([x-size+0.1, x-0.05], [y-0.06, y-0.05], 'k-', linewidth=1)
        ax.plot([x+0.05, x+size-0.1], [y+0.05, y+0.19], 'k-', linewidth=1)
        ax.plot([x+0.05, x+size-0.1], [y, y+0.04], 'k-', linewidth=1)
        ax.plot([x+0.05, x+size-0.1], [y-0.05, y-0.11], 'k-', linewidth=1)
        
    def _draw_drag_drop_demo(self, ax, x, y):
        """Draw drag and drop demonstration"""
        # Step 1
        ax.text(x, y, '1. Click on master port', fontsize=10)
        m1 = Circle((x+0.05, y-0.05), 0.02, facecolor='lightblue', edgecolor='black')
        ax.add_patch(m1)
        
        # Step 2
        ax.text(x+0.3, y, '2. Drag to slave port', fontsize=10)
        ax.plot([x+0.05, x+0.35], [y-0.05, y-0.05], 'k--', linewidth=1)
        
        # Step 3
        ax.text(x+0.6, y, '3. Connection created!', fontsize=10)
        ax.plot([x+0.55, x+0.65], [y-0.05, y-0.05], 'g-', linewidth=2)
        s1 = Circle((x+0.65, y-0.05), 0.02, facecolor='lightgreen', edgecolor='black')
        ax.add_patch(s1)
        
    def _draw_connection_matrix(self, ax, x, y):
        """Draw connection matrix"""
        # Matrix grid
        for i in range(3):
            for j in range(4):
                rect = Rectangle((x+i*0.08, y-j*0.05), 0.07, 0.04, 
                               facecolor='white', edgecolor='black')
                ax.add_patch(rect)
                
        # Labels
        ax.text(x-0.05, y+0.02, 'M/S', fontsize=9, weight='bold')
        for i in range(3):
            ax.text(x+i*0.08+0.035, y+0.02, f'S{i}', ha='center', fontsize=9)
        for j in range(3):
            ax.text(x-0.03, y-j*0.05-0.02, f'M{j}', ha='center', fontsize=9)
            
        # Example connections
        checks = [(0, 0), (0, 1), (1, 1), (1, 2), (2, 0), (2, 2)]
        for i, j in checks:
            ax.text(x+i*0.08+0.035, y-j*0.05-0.02, '✓', ha='center', 
                   fontsize=10, color='green', weight='bold')

def main():
    """Create the step-by-step guide"""
    print("Creating comprehensive step-by-step user guide...")
    guide = StepByStepGuide()
    guide.create()

if __name__ == "__main__":
    main()