#!/usr/bin/env python3
"""
Create an advanced user guide with comprehensive diagrams and tutorials
Ultrathink approach - exhaustive documentation with visual aids
"""

import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.patches import Rectangle, Circle, FancyBboxPatch, Polygon, Arc
import numpy as np
from datetime import datetime
import matplotlib.patches as mpatches

class AdvancedUserGuide:
    """Create ultra-comprehensive advanced user guide"""
    
    def __init__(self):
        self.filename = "advanced_userguide.pdf"
        
    def create(self):
        """Generate the advanced guide"""
        from matplotlib.backends.backend_pdf import PdfPages
        
        with PdfPages(self.filename) as pdf:
            # Part 1: Introduction
            self.create_title_page(pdf)
            self.create_about_guide(pdf)
            
            # Part 2: Architecture Deep Dive
            self.create_system_architecture(pdf)
            self.create_protocol_comparison(pdf)
            self.create_signal_details(pdf)
            
            # Part 3: Step-by-Step Tutorials
            self.create_basic_tutorial(pdf)
            self.create_advanced_tutorial(pdf)
            self.create_expert_tutorial(pdf)
            
            # Part 4: Configuration Reference
            self.create_parameter_reference(pdf)
            self.create_constraint_guide(pdf)
            self.create_optimization_guide(pdf)
            
            # Part 5: Integration Guide
            self.create_rtl_integration(pdf)
            self.create_vip_integration(pdf)
            self.create_fpga_guide(pdf)
            
            # Part 6: Troubleshooting
            self.create_error_reference(pdf)
            self.create_debug_guide(pdf)
            self.create_faq(pdf)
            
            # Part 7: Examples Gallery
            self.create_example_systems(pdf)
            self.create_use_cases(pdf)
            
            # Part 8: Appendices
            self.create_api_reference(pdf)
            self.create_command_reference(pdf)
            self.create_glossary(pdf)
            
        print(f"\nAdvanced user guide created: {self.filename}")
        import os
        size = os.path.getsize(self.filename) / 1024
        print(f"File size: {size:.1f} KB")
        
    def create_title_page(self, pdf):
        """Create professional title page"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        # Background design
        for i in range(20):
            y = i * 0.5
            alpha = 0.1 - (i * 0.005)
            if alpha > 0:
                rect = Rectangle((0, y), 10, 0.5, facecolor='blue', alpha=alpha)
                ax.add_patch(rect)
        
        # Main title
        ax.text(5, 7, 'AMBA Bus Matrix\nConfiguration Tool', 
                fontsize=36, weight='bold', ha='center', va='center',
                bbox=dict(boxstyle='round,pad=1.5', facecolor='white', 
                         edgecolor='navy', linewidth=3))
        
        # Subtitle
        ax.text(5, 5.5, 'Advanced User Guide', 
                fontsize=28, ha='center', va='center', style='italic',
                color='darkblue')
        
        # Version box
        version_box = FancyBboxPatch((2, 3.5), 6, 1.2,
                                    boxstyle="round,pad=0.1",
                                    facecolor='lightblue', 
                                    edgecolor='darkblue',
                                    linewidth=2)
        ax.add_patch(version_box)
        ax.text(5, 4.3, 'Version 1.0.0', fontsize=16, ha='center', weight='bold')
        ax.text(5, 3.9, 'Ultra-Comprehensive Edition', fontsize=14, ha='center')
        ax.text(5, 3.7, 'July 2025', fontsize=12, ha='center')
        
        # Feature badges
        badges = ['AXI4', 'AXI3', 'AHB', 'APB', 'UVM', 'SystemVerilog']
        x_start = 2
        for i, badge in enumerate(badges):
            x = x_start + (i % 3) * 2
            y = 2.5 - (i // 3) * 0.5
            badge_box = FancyBboxPatch((x-0.4, y-0.15), 0.8, 0.3,
                                      boxstyle="round,pad=0.05",
                                      facecolor='yellow', 
                                      edgecolor='orange')
            ax.add_patch(badge_box)
            ax.text(x, y, badge, ha='center', va='center', fontsize=10, weight='bold')
        
        ax.set_xlim(0, 10)
        ax.set_ylim(0, 10)
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_about_guide(self, pdf):
        """Create about this guide page"""
        fig = plt.figure(figsize=(8.5, 11))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.5, 0.95, 'About This Guide', fontsize=24, weight='bold',
                transform=ax.transAxes, ha='center')
        
        # Guide structure
        structure_box = FancyBboxPatch((0.05, 0.5), 0.9, 0.4,
                                      boxstyle="round,pad=0.02",
                                      facecolor='lightblue', 
                                      edgecolor='darkblue',
                                      transform=ax.transAxes)
        ax.add_patch(structure_box)
        
        sections = [
            "Part 1: Introduction - Overview and getting started",
            "Part 2: Architecture - Deep technical details",
            "Part 3: Tutorials - Step-by-step instructions",
            "Part 4: Configuration - Complete parameter reference",
            "Part 5: Integration - RTL and VIP integration",
            "Part 6: Troubleshooting - Solutions to common issues",
            "Part 7: Examples - Real-world use cases",
            "Part 8: Appendices - References and glossary"
        ]
        
        y_pos = 0.85
        for section in sections:
            ax.text(0.1, y_pos, section, fontsize=12, transform=ax.transAxes)
            y_pos -= 0.05
            
        # How to use
        ax.text(0.1, 0.4, 'How to Use This Guide:', fontsize=16, weight='bold',
                transform=ax.transAxes)
        
        usage_tips = [
            "• Beginners: Start with Part 1 and basic tutorial in Part 3",
            "• Intermediate: Focus on Parts 3-4 for configuration details",
            "• Advanced: Deep dive into Parts 2 and 5 for integration",
            "• Reference: Use Parts 6-8 for troubleshooting and lookups"
        ]
        
        y_pos = 0.35
        for tip in usage_tips:
            ax.text(0.1, y_pos, tip, fontsize=11, transform=ax.transAxes)
            y_pos -= 0.04
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_system_architecture(self, pdf):
        """Create detailed system architecture diagram"""
        fig = plt.figure(figsize=(11, 8.5))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.5, 0.95, 'System Architecture', fontsize=20, weight='bold',
                transform=ax.transAxes, ha='center')
        
        # Layer architecture
        layers = [
            (0.1, 0.7, 0.8, 0.15, 'GUI Layer', 'lightgreen', 
             ['Tkinter Interface', 'Visual Design', 'Property Editors']),
            (0.1, 0.5, 0.8, 0.15, 'Configuration Layer', 'lightblue',
             ['Bus Config', 'Master/Slave Config', 'Validation']),
            (0.1, 0.3, 0.8, 0.15, 'Generation Layer', 'lightyellow',
             ['RTL Generator', 'VIP Generator', 'Doc Generator']),
            (0.1, 0.1, 0.8, 0.15, 'Output Layer', 'lightcoral',
             ['Verilog RTL', 'UVM VIP', 'Reports'])
        ]
        
        for x, y, w, h, title, color, components in layers:
            # Main box
            box = FancyBboxPatch((x, y), w, h,
                               boxstyle="round,pad=0.02",
                               facecolor=color, edgecolor='black',
                               transform=ax.transAxes)
            ax.add_patch(box)
            ax.text(x+0.05, y+h-0.03, title, fontsize=14, weight='bold',
                   transform=ax.transAxes)
            
            # Components
            comp_x = x + 0.1
            for comp in components:
                comp_box = FancyBboxPatch((comp_x, y+0.03), 0.2, 0.08,
                                        boxstyle="round,pad=0.01",
                                        facecolor='white', 
                                        edgecolor='gray',
                                        transform=ax.transAxes)
                ax.add_patch(comp_box)
                ax.text(comp_x+0.1, y+0.07, comp, fontsize=10, 
                       ha='center', transform=ax.transAxes)
                comp_x += 0.25
                
        # Arrows between layers
        for i in range(len(layers)-1):
            arrow = patches.FancyArrowPatch((0.5, layers[i][1]), 
                                          (0.5, layers[i+1][1]+layers[i+1][3]),
                                          arrowstyle='->', mutation_scale=30,
                                          color='darkblue', linewidth=2,
                                          transform=ax.transAxes)
            ax.add_patch(arrow)
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_protocol_comparison(self, pdf):
        """Create protocol comparison chart"""
        fig = plt.figure(figsize=(11, 8.5))
        ax = fig.add_subplot(111)
        ax.axis('off')
        
        ax.text(0.5, 0.95, 'AMBA Protocol Comparison', fontsize=20, weight='bold',
                transform=ax.transAxes, ha='center')
        
        # Comparison table
        protocols = ['AXI4', 'AXI3', 'AHB', 'APB']
        features = [
            'Max Burst Length',
            'Outstanding Txn',
            'Out-of-Order',
            'Data Width',
            'Complexity',
            'Use Case'
        ]
        
        data = [
            ['256', '16', 'Multiple', 'Single'],
            ['Yes', 'Yes', 'Yes', 'No'],
            ['Yes', 'Yes', 'No', 'No'],
            ['32-1024', '32-1024', '32-1024', '8-32'],
            ['High', 'High', 'Medium', 'Low'],
            ['High Perf', 'Legacy', 'Mid Perf', 'Peripherals']
        ]
        
        # Draw table
        cell_width = 0.2
        cell_height = 0.08
        x_start = 0.1
        y_start = 0.8
        
        # Headers
        for i, prot in enumerate(protocols):
            x = x_start + (i+1) * cell_width
            header_box = Rectangle((x, y_start), cell_width, cell_height,
                                 facecolor='darkblue', edgecolor='black',
                                 transform=ax.transAxes)
            ax.add_patch(header_box)
            ax.text(x + cell_width/2, y_start + cell_height/2, prot,
                   ha='center', va='center', color='white', weight='bold',
                   fontsize=12, transform=ax.transAxes)
            
        # Feature labels and data
        for j, feature in enumerate(features):
            y = y_start - (j+1) * cell_height
            
            # Feature label
            label_box = Rectangle((x_start, y), cell_width, cell_height,
                                facecolor='lightgray', edgecolor='black',
                                transform=ax.transAxes)
            ax.add_patch(label_box)
            ax.text(x_start + cell_width/2, y + cell_height/2, feature,
                   ha='center', va='center', fontsize=10, weight='bold',
                   transform=ax.transAxes)
            
            # Data cells
            for i in range(len(protocols)):
                x = x_start + (i+1) * cell_width
                cell_box = Rectangle((x, y), cell_width, cell_height,
                                   facecolor='white', edgecolor='black',
                                   transform=ax.transAxes)
                ax.add_patch(cell_box)
                ax.text(x + cell_width/2, y + cell_height/2, data[j][i],
                       ha='center', va='center', fontsize=10,
                       transform=ax.transAxes)
                       
        # Protocol selection guide
        guide_y = 0.25
        ax.text(0.1, guide_y, 'Protocol Selection Guide:', 
               fontsize=14, weight='bold', transform=ax.transAxes)
        
        guides = [
            "• AXI4: Choose for new high-performance designs",
            "• AXI3: Use only for legacy compatibility",
            "• AHB: Good for medium complexity systems",
            "• APB: Perfect for low-speed peripherals"
        ]
        
        for i, guide in enumerate(guides):
            ax.text(0.15, guide_y - (i+1)*0.04, guide, fontsize=11,
                   transform=ax.transAxes)
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_signal_details(self, pdf):
        """Create detailed signal reference"""
        fig = plt.figure(figsize=(11, 8.5))
        
        # AXI4 signals
        ax1 = plt.subplot(2, 1, 1)
        ax1.set_title('AXI4 Signal Reference', fontsize=16, weight='bold')
        ax1.axis('off')
        
        # Channel diagram
        channels = [
            (0.1, 0.8, 'Write Address', 'lightblue', 
             ['AWID', 'AWADDR', 'AWLEN', 'AWSIZE', 'AWBURST']),
            (0.1, 0.6, 'Write Data', 'lightgreen',
             ['WDATA', 'WSTRB', 'WLAST']),
            (0.1, 0.4, 'Write Response', 'lightyellow',
             ['BID', 'BRESP']),
            (0.55, 0.8, 'Read Address', 'lightcoral',
             ['ARID', 'ARADDR', 'ARLEN', 'ARSIZE', 'ARBURST']),
            (0.55, 0.6, 'Read Data', 'lavender',
             ['RID', 'RDATA', 'RRESP', 'RLAST'])
        ]
        
        for x, y, name, color, signals in channels:
            # Channel box
            box = FancyBboxPatch((x, y-0.15), 0.35, 0.15,
                               boxstyle="round,pad=0.02",
                               facecolor=color, edgecolor='black')
            ax1.add_patch(box)
            ax1.text(x+0.175, y-0.02, name, ha='center', fontsize=12, weight='bold')
            
            # Signals
            sig_text = ', '.join(signals)
            ax1.text(x+0.175, y-0.1, sig_text, ha='center', fontsize=9,
                    style='italic', wrap=True)
                    
        # Handshake signals
        ax2 = plt.subplot(2, 1, 2)
        ax2.set_title('Handshake Protocol', fontsize=16, weight='bold')
        ax2.axis('off')
        
        # Timing diagram
        time_points = np.linspace(0.1, 0.9, 10)
        
        # VALID signal
        valid_y = 0.7
        ax2.plot([0.1, 0.3], [valid_y, valid_y], 'k-', linewidth=2)
        ax2.plot([0.3, 0.3], [valid_y, valid_y+0.1], 'k-', linewidth=2)
        ax2.plot([0.3, 0.7], [valid_y+0.1, valid_y+0.1], 'k-', linewidth=2)
        ax2.plot([0.7, 0.7], [valid_y+0.1, valid_y], 'k-', linewidth=2)
        ax2.plot([0.7, 0.9], [valid_y, valid_y], 'k-', linewidth=2)
        ax2.text(0.05, valid_y+0.05, 'VALID', fontsize=10, weight='bold')
        
        # READY signal
        ready_y = 0.5
        ax2.plot([0.1, 0.5], [ready_y, ready_y], 'k-', linewidth=2)
        ax2.plot([0.5, 0.5], [ready_y, ready_y+0.1], 'k-', linewidth=2)
        ax2.plot([0.5, 0.7], [ready_y+0.1, ready_y+0.1], 'k-', linewidth=2)
        ax2.plot([0.7, 0.7], [ready_y+0.1, ready_y], 'k-', linewidth=2)
        ax2.plot([0.7, 0.9], [ready_y, ready_y], 'k-', linewidth=2)
        ax2.text(0.05, ready_y+0.05, 'READY', fontsize=10, weight='bold')
        
        # Transfer indicator
        ax2.add_patch(Rectangle((0.5, 0.3), 0.2, 0.15, 
                              facecolor='lightgreen', alpha=0.5))
        ax2.text(0.6, 0.375, 'Transfer', ha='center', fontsize=10)
        
        # Rules
        ax2.text(0.1, 0.2, 'Handshake Rules:', fontsize=12, weight='bold')
        rules = [
            '• Transfer occurs when both VALID and READY are HIGH',
            '• VALID must remain stable once asserted',
            '• READY can be asserted before, with, or after VALID'
        ]
        
        y_pos = 0.15
        for rule in rules:
            ax2.text(0.15, y_pos, rule, fontsize=10)
            y_pos -= 0.05
            
        plt.tight_layout()
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_basic_tutorial(self, pdf):
        """Create basic tutorial for beginners"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Basic Tutorial: Your First Design', fontsize=20, weight='bold')
        
        # Overview
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        ax.text(0.1, 0.9, 'Goal: Create a simple 2×2 AXI4 system', 
               fontsize=14, style='italic')
        
        # Step boxes with detailed instructions
        steps = [
            {
                'title': 'Step 1: Launch the Tool',
                'y': 0.8,
                'color': 'lightblue',
                'instructions': [
                    '1. Open terminal',
                    '2. Navigate to: cd axi4_vip/gui',
                    '3. Run: ./launch_gui.sh',
                    '4. Main window appears'
                ]
            },
            {
                'title': 'Step 2: Add First Master',
                'y': 0.6,
                'color': 'lightgreen',
                'instructions': [
                    '1. Click "Add Master" button',
                    '2. Name: CPU_0',
                    '3. ID Width: 4',
                    '4. Click OK'
                ]
            },
            {
                'title': 'Step 3: Add Second Master',
                'y': 0.4,
                'color': 'lightgreen',
                'instructions': [
                    '1. Click "Add Master" again',
                    '2. Name: DMA_0',
                    '3. ID Width: 4',
                    '4. Click OK'
                ]
            },
            {
                'title': 'Step 4: Add Memory Slave',
                'y': 0.2,
                'color': 'lightyellow',
                'instructions': [
                    '1. Click "Add Slave"',
                    '2. Name: DDR_0',
                    '3. Base: 0x00000000',
                    '4. Size: 1GB'
                ]
            }
        ]
        
        for step in steps:
            # Step box
            box = FancyBboxPatch((0.05, step['y']-0.15), 0.9, 0.14,
                               boxstyle="round,pad=0.02",
                               facecolor=step['color'], 
                               edgecolor='black')
            ax.add_patch(box)
            ax.text(0.1, step['y']-0.02, step['title'], 
                   fontsize=12, weight='bold')
            
            # Instructions
            inst_x = 0.5
            for i, inst in enumerate(step['instructions']):
                ax.text(inst_x, step['y']-0.05-i*0.025, inst, fontsize=10)
                
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_advanced_tutorial(self, pdf):
        """Create advanced tutorial"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Advanced Tutorial: High-Performance System', 
                    fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        ax.text(0.1, 0.9, 'Goal: Build a complex multi-master system with QoS', 
               fontsize=14, style='italic')
        
        # System diagram
        self._draw_complex_system(ax, 0.5, 0.7, 0.3)
        
        # Configuration details
        config_box = FancyBboxPatch((0.05, 0.3), 0.9, 0.25,
                                  boxstyle="round,pad=0.02",
                                  facecolor='lightgray', 
                                  edgecolor='black')
        ax.add_patch(config_box)
        
        ax.text(0.1, 0.5, 'Advanced Configuration:', fontsize=14, weight='bold')
        
        configs = [
            '• Enable QoS for latency-critical masters',
            '• Configure weighted arbitration',
            '• Set up exclusive access monitors',
            '• Define security zones',
            '• Optimize address mapping'
        ]
        
        y_pos = 0.45
        for config in configs:
            ax.text(0.15, y_pos, config, fontsize=11)
            y_pos -= 0.04
            
        # Performance tips
        perf_box = FancyBboxPatch((0.05, 0.05), 0.9, 0.2,
                                boxstyle="round,pad=0.02",
                                facecolor='lightyellow', 
                                edgecolor='orange')
        ax.add_patch(perf_box)
        
        ax.text(0.1, 0.22, 'Performance Optimization:', fontsize=12, weight='bold')
        ax.text(0.1, 0.17, '• Balance master priorities based on bandwidth needs', 
               fontsize=10)
        ax.text(0.1, 0.13, '• Use appropriate burst sizes for each master', 
               fontsize=10)
        ax.text(0.1, 0.09, '• Minimize crossbar complexity where possible', 
               fontsize=10)
               
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_expert_tutorial(self, pdf):
        """Create expert-level tutorial"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Expert Tutorial: Custom Extensions', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # Advanced topics
        topics = [
            {
                'title': 'Custom Arbitration Schemes',
                'y': 0.85,
                'details': [
                    '- Implement deadline-based arbitration',
                    '- Add dynamic priority adjustment',
                    '- Create custom QoS algorithms'
                ]
            },
            {
                'title': 'Protocol Bridges',
                'y': 0.65,
                'details': [
                    '- AXI4 to AXI3 conversion',
                    '- Clock domain crossing',
                    '- Width conversion'
                ]
            },
            {
                'title': 'Security Extensions',
                'y': 0.45,
                'details': [
                    '- Custom security attributes',
                    '- Access control lists',
                    '- Encryption interfaces'
                ]
            },
            {
                'title': 'Debug Features',
                'y': 0.25,
                'details': [
                    '- Transaction trace',
                    '- Performance counters',
                    '- Protocol checkers'
                ]
            }
        ]
        
        for topic in topics:
            # Topic box
            box = FancyBboxPatch((0.05, topic['y']-0.15), 0.9, 0.14,
                               boxstyle="round,pad=0.02",
                               facecolor='lavender', 
                               edgecolor='purple')
            ax.add_patch(box)
            ax.text(0.1, topic['y']-0.02, topic['title'], 
                   fontsize=13, weight='bold')
            
            # Details
            y_detail = topic['y'] - 0.05
            for detail in topic['details']:
                ax.text(0.15, y_detail, detail, fontsize=10)
                y_detail -= 0.03
                
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_parameter_reference(self, pdf):
        """Create comprehensive parameter reference"""
        fig = plt.figure(figsize=(11, 8.5))
        fig.suptitle('Complete Parameter Reference', fontsize=20, weight='bold')
        
        # Create multiple parameter tables
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # Master parameters
        self._draw_parameter_table(ax, 0.05, 0.7, 'Master Parameters', [
            ['Parameter', 'Type', 'Range', 'Default', 'Description'],
            ['name', 'string', 'any', '-', 'Unique identifier'],
            ['id_width', 'int', '1-16', '4', 'Transaction ID width'],
            ['priority', 'int', '0-15', '0', 'Arbitration priority'],
            ['qos_enable', 'bool', '0/1', '1', 'QoS support'],
            ['exclusive', 'bool', '0/1', '1', 'Exclusive access'],
            ['user_width', 'int', '0-1024', '0', 'User signal width']
        ])
        
        # Slave parameters
        self._draw_parameter_table(ax, 0.05, 0.35, 'Slave Parameters', [
            ['Parameter', 'Type', 'Range', 'Default', 'Description'],
            ['name', 'string', 'any', '-', 'Unique identifier'],
            ['base_addr', 'hex', 'any', '-', 'Base address'],
            ['size', 'int', '>0', '-', 'Address range'],
            ['mem_type', 'enum', 'mem/per', 'mem', 'Memory type'],
            ['read_lat', 'int', '>=1', '1', 'Read latency'],
            ['write_lat', 'int', '>=1', '1', 'Write latency']
        ])
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_constraint_guide(self, pdf):
        """Create constraint and validation guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Design Constraints Guide', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # Constraint categories
        constraints = [
            {
                'title': 'Address Constraints',
                'y': 0.85,
                'rules': [
                    '• No overlapping slave address ranges',
                    '• Base addresses must be aligned to size',
                    '• 4KB boundary rules for AXI',
                    '• Power-of-2 sizes recommended'
                ]
            },
            {
                'title': 'Protocol Constraints',
                'y': 0.65,
                'rules': [
                    '• WRAP burst length: 2, 4, 8, or 16',
                    '• Exclusive access max 128 bytes',
                    '• Narrow transfers must be aligned',
                    '• Unaligned addresses use WSTRB'
                ]
            },
            {
                'title': 'Performance Constraints',
                'y': 0.45,
                'rules': [
                    '• Max outstanding limited by ID width',
                    '• Crossbar complexity grows O(M×N)',
                    '• QoS affects arbitration latency',
                    '• Wide buses increase area'
                ]
            },
            {
                'title': 'Security Constraints',
                'y': 0.25,
                'rules': [
                    '• Secure masters → secure slaves only',
                    '• Non-secure cannot access secure',
                    '• AxPROT must be consistent',
                    '• Region settings affect access'
                ]
            }
        ]
        
        for const in constraints:
            # Constraint box
            box = FancyBboxPatch((0.05, const['y']-0.15), 0.9, 0.14,
                               boxstyle="round,pad=0.02",
                               facecolor='#ffe6e6', 
                               edgecolor='red')
            ax.add_patch(box)
            ax.text(0.1, const['y']-0.02, const['title'], 
                   fontsize=13, weight='bold')
            
            # Rules
            y_rule = const['y'] - 0.05
            for rule in const['rules']:
                ax.text(0.12, y_rule, rule, fontsize=10)
                y_rule -= 0.025
                
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_optimization_guide(self, pdf):
        """Create optimization guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Performance Optimization Guide', fontsize=20, weight='bold')
        
        # Optimization strategies
        ax1 = plt.subplot(2, 1, 1)
        ax1.set_title('Optimization Strategies', fontsize=16)
        ax1.axis('off')
        
        strategies = [
            ('Reduce Crossbar', 'Limit connectivity where not needed', 'lightgreen'),
            ('Optimize Arbitration', 'Use appropriate arbitration scheme', 'lightblue'),
            ('Balance Load', 'Distribute traffic across slaves', 'lightyellow'),
            ('Pipeline Stages', 'Add registers for timing closure', 'lightcoral')
        ]
        
        x_pos = 0.1
        for title, desc, color in strategies:
            box = FancyBboxPatch((x_pos, 0.3), 0.18, 0.5,
                               boxstyle="round,pad=0.02",
                               facecolor=color, edgecolor='black')
            ax1.add_patch(box)
            ax1.text(x_pos+0.09, 0.7, title, ha='center', fontsize=11, 
                    weight='bold', wrap=True)
            ax1.text(x_pos+0.09, 0.5, desc, ha='center', fontsize=9,
                    wrap=True, style='italic')
            x_pos += 0.22
            
        # Metrics
        ax2 = plt.subplot(2, 1, 2)
        ax2.set_title('Key Performance Metrics', fontsize=16)
        ax2.axis('off')
        
        metrics = [
            'Bandwidth Utilization = (Actual / Theoretical) × 100%',
            'Average Latency = Σ(Transaction_Latency) / N',
            'Arbitration Overhead = Time_Waiting / Total_Time',
            'Crossbar Efficiency = Active_Paths / Total_Paths'
        ]
        
        y_pos = 0.8
        for metric in metrics:
            ax2.text(0.1, y_pos, metric, fontsize=11, family='monospace',
                    bbox=dict(boxstyle='round,pad=0.3', facecolor='lightgray'))
            y_pos -= 0.2
            
        plt.tight_layout()
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_rtl_integration(self, pdf):
        """Create RTL integration guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('RTL Integration Guide', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # Integration flow
        ax.text(0.5, 0.9, 'RTL Integration Flow', fontsize=16, weight='bold',
               ha='center')
        
        flow_steps = [
            (0.5, 0.8, 'Generated RTL', 'lightblue', 
             ['axi4_interconnect.v', 'Supporting modules']),
            (0.5, 0.65, 'Your Design', 'lightgreen',
             ['Top module', 'Custom logic']),
            (0.5, 0.5, 'Integration', 'lightyellow',
             ['Instantiate interconnect', 'Connect interfaces']),
            (0.5, 0.35, 'Verification', 'lightcoral',
             ['Simulation', 'Synthesis checks']),
            (0.5, 0.2, 'Implementation', 'lavender',
             ['FPGA/ASIC flow', 'Timing closure'])
        ]
        
        for x, y, title, color, items in flow_steps:
            # Step box
            box = FancyBboxPatch((x-0.15, y-0.05), 0.3, 0.1,
                               boxstyle="round,pad=0.02",
                               facecolor=color, edgecolor='black')
            ax.add_patch(box)
            ax.text(x, y+0.03, title, ha='center', fontsize=12, weight='bold')
            
            # Items
            item_text = ' | '.join(items)
            ax.text(x, y-0.02, item_text, ha='center', fontsize=9, style='italic')
            
        # Connection arrows
        for i in range(len(flow_steps)-1):
            arrow = patches.FancyArrowPatch((0.5, flow_steps[i][1]-0.05),
                                          (0.5, flow_steps[i+1][1]+0.05),
                                          arrowstyle='->', mutation_scale=20,
                                          color='black', linewidth=2)
            ax.add_patch(arrow)
            
        # Example instantiation
        code_box = FancyBboxPatch((0.05, 0.01), 0.9, 0.15,
                                boxstyle="round,pad=0.02",
                                facecolor='#f0f0f0', edgecolor='black')
        ax.add_patch(code_box)
        ax.text(0.1, 0.12, 'Example Instantiation:', fontsize=11, weight='bold')
        ax.text(0.1, 0.08, 'axi4_interconnect_m2s3 u_interconnect (', 
               fontsize=9, family='monospace')
        ax.text(0.1, 0.05, '    .clk(clk), .rst_n(rst_n), ...', 
               fontsize=9, family='monospace')
        ax.text(0.1, 0.02, ');', fontsize=9, family='monospace')
        
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_vip_integration(self, pdf):
        """Create VIP integration guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('VIP Integration Guide', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # VIP components
        ax.text(0.5, 0.9, 'UVM VIP Components', fontsize=16, weight='bold',
               ha='center')
        
        components = [
            (0.2, 0.75, 'Environment', 'lightblue', 
             ['Agents', 'Scoreboard', 'Coverage']),
            (0.5, 0.75, 'Sequences', 'lightgreen',
             ['Base seq', 'Random seq', 'Directed']),
            (0.8, 0.75, 'Tests', 'lightyellow',
             ['Base test', 'Stress test', 'Compliance'])
        ]
        
        for x, y, title, color, items in components:
            # Component box
            box = FancyBboxPatch((x-0.12, y-0.1), 0.24, 0.15,
                               boxstyle="round,pad=0.02",
                               facecolor=color, edgecolor='black')
            ax.add_patch(box)
            ax.text(x, y+0.03, title, ha='center', fontsize=12, weight='bold')
            
            # Items
            y_item = y - 0.02
            for item in items:
                ax.text(x, y_item, item, ha='center', fontsize=9)
                y_item -= 0.03
                
        # Usage example
        usage_box = FancyBboxPatch((0.05, 0.3), 0.9, 0.25,
                                 boxstyle="round,pad=0.02",
                                 facecolor='lightgray', edgecolor='black')
        ax.add_patch(usage_box)
        
        ax.text(0.1, 0.5, 'Running VIP Tests:', fontsize=12, weight='bold')
        
        commands = [
            '1. Compile: vcs -sverilog -ntb_opts uvm',
            '2. Run test: ./simv +UVM_TESTNAME=axi4_base_test',
            '3. View waves: dve -vpd dump.vpd',
            '4. Coverage: urg -dir simv.vdb'
        ]
        
        y_cmd = 0.45
        for cmd in commands:
            ax.text(0.15, y_cmd, cmd, fontsize=10, family='monospace')
            y_cmd -= 0.04
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_fpga_guide(self, pdf):
        """Create FPGA implementation guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('FPGA Implementation Guide', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # FPGA flow
        fpga_steps = [
            {
                'title': 'Synthesis',
                'y': 0.8,
                'details': [
                    '• Run synthesis with generated RTL',
                    '• Check for inferred latches',
                    '• Review resource utilization'
                ]
            },
            {
                'title': 'Constraints',
                'y': 0.6,
                'details': [
                    '• Define clock constraints',
                    '• Set I/O timing requirements',
                    '• Add false path constraints'
                ]
            },
            {
                'title': 'Implementation',
                'y': 0.4,
                'details': [
                    '• Place and route design',
                    '• Analyze timing reports',
                    '• Optimize critical paths'
                ]
            },
            {
                'title': 'Verification',
                'y': 0.2,
                'details': [
                    '• Post-route simulation',
                    '• Hardware testing',
                    '• Performance validation'
                ]
            }
        ]
        
        for step in fpga_steps:
            # Step box
            box = FancyBboxPatch((0.05, step['y']-0.15), 0.9, 0.14,
                               boxstyle="round,pad=0.02",
                               facecolor='#e6f2ff', edgecolor='blue')
            ax.add_patch(box)
            ax.text(0.1, step['y']-0.02, step['title'], 
                   fontsize=13, weight='bold')
            
            # Details
            y_detail = step['y'] - 0.05
            for detail in step['details']:
                ax.text(0.12, y_detail, detail, fontsize=10)
                y_detail -= 0.03
                
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_error_reference(self, pdf):
        """Create error reference guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Error Reference Guide', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # Common errors
        errors = [
            {
                'error': 'Address Overlap Error',
                'y': 0.85,
                'cause': 'Two slaves have overlapping address ranges',
                'solution': 'Adjust slave base addresses or sizes'
            },
            {
                'error': 'Port Width Mismatch',
                'y': 0.65,
                'cause': 'Incompatible data widths between components',
                'solution': 'Ensure all widths are compatible or add converters'
            },
            {
                'error': 'Invalid Burst Configuration',
                'y': 0.45,
                'cause': 'WRAP burst with invalid length',
                'solution': 'Use only 2, 4, 8, or 16 for WRAP bursts'
            },
            {
                'error': 'Security Violation',
                'y': 0.25,
                'cause': 'Non-secure master accessing secure slave',
                'solution': 'Update security settings or connection matrix'
            }
        ]
        
        for err in errors:
            # Error box
            box = FancyBboxPatch((0.05, err['y']-0.15), 0.9, 0.14,
                               boxstyle="round,pad=0.02",
                               facecolor='#ffe6e6', edgecolor='red')
            ax.add_patch(box)
            
            ax.text(0.1, err['y']-0.02, err['error'], 
                   fontsize=12, weight='bold', color='red')
            ax.text(0.1, err['y']-0.06, f"Cause: {err['cause']}", 
                   fontsize=10)
            ax.text(0.1, err['y']-0.1, f"Solution: {err['solution']}", 
                   fontsize=10, style='italic', color='green')
                   
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_debug_guide(self, pdf):
        """Create debug guide"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Debug Guide', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # Debug techniques
        techniques = [
            {
                'title': 'Waveform Analysis',
                'y': 0.8,
                'steps': [
                    '1. Enable transaction recording',
                    '2. Look for protocol violations',
                    '3. Check handshake timing',
                    '4. Verify response codes'
                ]
            },
            {
                'title': 'Log Analysis',
                'y': 0.55,
                'steps': [
                    '1. Enable UVM verbosity',
                    '2. Check error messages',
                    '3. Trace transaction flow',
                    '4. Monitor coverage gaps'
                ]
            },
            {
                'title': 'Assertion Debug',
                'y': 0.3,
                'steps': [
                    '1. Review assertion failures',
                    '2. Check timing assertions',
                    '3. Verify protocol assertions',
                    '4. Add custom assertions'
                ]
            }
        ]
        
        for tech in techniques:
            # Technique box
            box = FancyBboxPatch((0.05, tech['y']-0.2), 0.9, 0.18,
                               boxstyle="round,pad=0.02",
                               facecolor='lightcyan', edgecolor='darkblue')
            ax.add_patch(box)
            ax.text(0.1, tech['y']-0.02, tech['title'], 
                   fontsize=13, weight='bold')
            
            # Steps
            y_step = tech['y'] - 0.05
            for step in tech['steps']:
                ax.text(0.15, y_step, step, fontsize=10)
                y_step -= 0.03
                
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_faq(self, pdf):
        """Create FAQ section"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Frequently Asked Questions', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        faqs = [
            {
                'q': 'Q: How many masters/slaves can I have?',
                'a': 'A: Practically up to 16 masters and 32 slaves',
                'y': 0.85
            },
            {
                'q': 'Q: Can I mix protocols in one design?',
                'a': 'A: Yes, use protocol bridges (AXI-to-APB, etc.)',
                'y': 0.7
            },
            {
                'q': 'Q: How do I optimize for low latency?',
                'a': 'A: Use QoS, minimize arbitration stages, direct paths',
                'y': 0.55
            },
            {
                'q': 'Q: What simulators are supported?',
                'a': 'A: VCS, Questa, Xcelium, and Vivado Simulator',
                'y': 0.4
            },
            {
                'q': 'Q: Can I modify generated RTL?',
                'a': 'A: Yes, but consider using configuration options first',
                'y': 0.25
            }
        ]
        
        for faq in faqs:
            # Question
            ax.text(0.1, faq['y'], faq['q'], fontsize=12, weight='bold',
                   color='darkblue')
            # Answer
            ax.text(0.15, faq['y']-0.04, faq['a'], fontsize=11,
                   style='italic')
            # Separator
            ax.plot([0.1, 0.9], [faq['y']-0.08, faq['y']-0.08], 
                   'k--', alpha=0.3)
                   
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_example_systems(self, pdf):
        """Create example system gallery"""
        fig = plt.figure(figsize=(11, 8.5))
        fig.suptitle('Example System Designs', fontsize=20, weight='bold')
        
        # Create grid of example systems
        examples = [
            ('Simple SoC', 0.25, 0.7, self._draw_simple_soc),
            ('High Performance', 0.75, 0.7, self._draw_high_perf),
            ('IoT System', 0.25, 0.3, self._draw_iot_system),
            ('Automotive', 0.75, 0.3, self._draw_automotive)
        ]
        
        for name, x, y, draw_func in examples:
            ax = plt.axes([x-0.2, y-0.15, 0.4, 0.3])
            ax.set_title(name, fontsize=14, weight='bold')
            ax.axis('off')
            draw_func(ax)
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_use_cases(self, pdf):
        """Create use case descriptions"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Real-World Use Cases', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        use_cases = [
            {
                'title': 'Mobile SoC',
                'y': 0.8,
                'desc': 'Multi-core CPU with GPU, display, and peripherals',
                'config': 'AXI4, QoS enabled, power domains'
            },
            {
                'title': 'AI Accelerator',
                'y': 0.6,
                'desc': 'High-bandwidth ML processor with HBM interface',
                'config': '1024-bit data, multiple outstanding'
            },
            {
                'title': 'Automotive ECU',
                'y': 0.4,
                'desc': 'Safety-critical system with redundancy',
                'config': 'Lockstep cores, ECC, security zones'
            },
            {
                'title': 'Network Processor',
                'y': 0.2,
                'desc': 'Packet processing with multiple interfaces',
                'config': 'Low latency, QoS, traffic shaping'
            }
        ]
        
        for uc in use_cases:
            # Use case box
            box = FancyBboxPatch((0.05, uc['y']-0.15), 0.9, 0.13,
                               boxstyle="round,pad=0.02",
                               facecolor='#f0f8ff', edgecolor='blue')
            ax.add_patch(box)
            
            ax.text(0.1, uc['y']-0.02, uc['title'], 
                   fontsize=13, weight='bold')
            ax.text(0.1, uc['y']-0.06, uc['desc'], fontsize=11)
            ax.text(0.1, uc['y']-0.1, f"Config: {uc['config']}", 
                   fontsize=10, style='italic', color='green')
                   
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_api_reference(self, pdf):
        """Create API reference"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Python API Reference', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # API classes
        classes = [
            {
                'name': 'BusConfig',
                'y': 0.85,
                'methods': [
                    'add_master(name, **kwargs)',
                    'add_slave(name, base, size, **kwargs)',
                    'validate() -> bool',
                    'save(filename)'
                ]
            },
            {
                'name': 'AXIVerilogGenerator',
                'y': 0.55,
                'methods': [
                    '__init__(config)',
                    'generate() -> list[str]',
                    'write_files(output_dir)',
                    'get_file_list() -> dict'
                ]
            },
            {
                'name': 'VIPGenerator',
                'y': 0.25,
                'methods': [
                    '__init__(config)',
                    'generate_env()',
                    'generate_tests()',
                    'create_scripts(simulator)'
                ]
            }
        ]
        
        for cls in classes:
            # Class box
            box = FancyBboxPatch((0.05, cls['y']-0.2), 0.9, 0.18,
                               boxstyle="round,pad=0.02",
                               facecolor='#fffacd', edgecolor='black')
            ax.add_patch(box)
            ax.text(0.1, cls['y']-0.02, f"class {cls['name']}:", 
                   fontsize=12, weight='bold', family='monospace')
            
            # Methods
            y_method = cls['y'] - 0.05
            for method in cls['methods']:
                ax.text(0.15, y_method, method, fontsize=10, family='monospace')
                y_method -= 0.035
                
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_command_reference(self, pdf):
        """Create command reference"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Command Line Reference', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        # Command categories
        categories = [
            {
                'title': 'Launch Commands',
                'y': 0.85,
                'commands': [
                    './launch_gui.sh               # Default launch',
                    './launch_gui.sh --config file # Load config',
                    'python3 src/bus_matrix_gui.py # Direct launch'
                ]
            },
            {
                'title': 'Generation Commands',
                'y': 0.6,
                'commands': [
                    'python3 generate_rtl.py --config config.json',
                    'python3 generate_vip.py --config config.json',
                    'make -C ../.. MST=2 SLV=3    # Makefile'
                ]
            },
            {
                'title': 'Simulation Commands',
                'y': 0.35,
                'commands': [
                    'cd vip_output/sim && ./run.sh',
                    'vsim -do run.do              # Questa',
                    'vcs -f files.f && ./simv     # VCS'
                ]
            }
        ]
        
        for cat in categories:
            ax.text(0.1, cat['y'], cat['title'], fontsize=13, weight='bold')
            
            y_cmd = cat['y'] - 0.05
            for cmd in cat['commands']:
                ax.text(0.15, y_cmd, cmd, fontsize=10, family='monospace',
                       bbox=dict(boxstyle='round,pad=0.2', facecolor='#f0f0f0'))
                y_cmd -= 0.05
                
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    def create_glossary(self, pdf):
        """Create glossary"""
        fig = plt.figure(figsize=(8.5, 11))
        fig.suptitle('Glossary', fontsize=20, weight='bold')
        
        ax = plt.subplot(1, 1, 1)
        ax.axis('off')
        
        terms = [
            ('AMBA', 'Advanced Microcontroller Bus Architecture'),
            ('AXI', 'Advanced eXtensible Interface'),
            ('APB', 'Advanced Peripheral Bus'),
            ('AHB', 'Advanced High-performance Bus'),
            ('QoS', 'Quality of Service'),
            ('VIP', 'Verification Intellectual Property'),
            ('UVM', 'Universal Verification Methodology'),
            ('RTL', 'Register Transfer Level'),
            ('DUT', 'Design Under Test'),
            ('BFM', 'Bus Functional Model'),
            ('PCWM', 'Port Connection Width Mismatch'),
            ('ID', 'Transaction Identifier'),
            ('WSTRB', 'Write Strobe signals'),
            ('AxPROT', 'Protection type (Access control)'),
            ('AxLOCK', 'Lock type (Exclusive access)')
        ]
        
        y_pos = 0.9
        for term, definition in terms:
            ax.text(0.1, y_pos, f"{term}:", fontsize=11, weight='bold')
            ax.text(0.25, y_pos, definition, fontsize=10)
            y_pos -= 0.055
            
        pdf.savefig(fig, bbox_inches='tight')
        plt.close()
        
    # Helper drawing methods
    def _draw_complex_system(self, ax, x, y, size):
        """Draw a complex multi-master system"""
        # Masters
        masters = ['CPU0', 'CPU1', 'GPU', 'DMA']
        for i, m in enumerate(masters):
            rect = Rectangle((x-size, y+i*0.08-0.15), 0.08, 0.06,
                           facecolor='lightblue', edgecolor='black')
            ax.add_patch(rect)
            ax.text(x-size+0.04, y+i*0.08-0.12, m, ha='center', fontsize=8)
            
        # Interconnect
        ic = Rectangle((x-0.05, y-0.2), 0.1, 0.4,
                      facecolor='gray', edgecolor='black')
        ax.add_patch(ic)
        ax.text(x, y, 'AXI4\nIC', ha='center', va='center', 
               fontsize=9, color='white')
        
        # Slaves
        slaves = ['DDR', 'SRAM', 'ROM', 'APB']
        for i, s in enumerate(slaves):
            rect = Rectangle((x+size-0.08, y+i*0.08-0.15), 0.08, 0.06,
                           facecolor='lightgreen', edgecolor='black')
            ax.add_patch(rect)
            ax.text(x+size-0.04, y+i*0.08-0.12, s, ha='center', fontsize=8)
            
    def _draw_parameter_table(self, ax, x, y, title, data):
        """Draw a parameter table"""
        ax.text(x, y+0.05, title, fontsize=14, weight='bold')
        
        # Table
        rows = len(data)
        cols = len(data[0])
        cell_width = 0.18
        cell_height = 0.04
        
        for i, row in enumerate(data):
            for j, cell in enumerate(row):
                cell_x = x + j * cell_width
                cell_y = y - i * cell_height
                
                # Header row
                if i == 0:
                    color = 'lightgray'
                    weight = 'bold'
                else:
                    color = 'white'
                    weight = 'normal'
                    
                rect = Rectangle((cell_x, cell_y), cell_width, cell_height,
                               facecolor=color, edgecolor='black')
                ax.add_patch(rect)
                ax.text(cell_x + cell_width/2, cell_y + cell_height/2,
                       cell, ha='center', va='center', fontsize=9,
                       weight=weight)
                       
    def _draw_simple_soc(self, ax):
        """Draw simple SoC example"""
        # CPU
        cpu = Rectangle((0.2, 0.6), 0.15, 0.2, 
                       facecolor='lightblue', edgecolor='black')
        ax.add_patch(cpu)
        ax.text(0.275, 0.7, 'CPU', ha='center', fontsize=10)
        
        # Bus
        bus = Rectangle((0.45, 0.3), 0.1, 0.6,
                       facecolor='gray', edgecolor='black')
        ax.add_patch(bus)
        
        # Memory
        mem = Rectangle((0.65, 0.6), 0.15, 0.2,
                       facecolor='lightgreen', edgecolor='black')
        ax.add_patch(mem)
        ax.text(0.725, 0.7, 'MEM', ha='center', fontsize=10)
        
        # Peripheral
        per = Rectangle((0.65, 0.3), 0.15, 0.2,
                       facecolor='lightyellow', edgecolor='black')
        ax.add_patch(per)
        ax.text(0.725, 0.4, 'UART', ha='center', fontsize=10)
        
    def _draw_high_perf(self, ax):
        """Draw high performance system"""
        # Multiple CPUs
        for i in range(4):
            cpu = Circle((0.2, 0.8-i*0.15), 0.05, 
                        facecolor='lightblue', edgecolor='black')
            ax.add_patch(cpu)
            ax.text(0.2, 0.8-i*0.15, f'C{i}', ha='center', fontsize=8)
            
        # Crossbar
        xbar = Rectangle((0.4, 0.2), 0.2, 0.7,
                        facecolor='darkgray', edgecolor='black')
        ax.add_patch(xbar)
        ax.text(0.5, 0.55, 'XBAR', ha='center', color='white', fontsize=10)
        
        # Memories
        for i in range(2):
            mem = Rectangle((0.7, 0.6-i*0.3), 0.1, 0.2,
                          facecolor='lightgreen', edgecolor='black')
            ax.add_patch(mem)
            ax.text(0.75, 0.7-i*0.3, f'DDR{i}', ha='center', fontsize=8)
            
    def _draw_iot_system(self, ax):
        """Draw IoT system example"""
        # Low power CPU
        cpu = Rectangle((0.3, 0.5), 0.1, 0.15,
                       facecolor='lightcyan', edgecolor='black')
        ax.add_patch(cpu)
        ax.text(0.35, 0.575, 'MCU', ha='center', fontsize=9)
        
        # APB bus
        bus = Rectangle((0.45, 0.3), 0.08, 0.5,
                       facecolor='lightgray', edgecolor='black')
        ax.add_patch(bus)
        ax.text(0.49, 0.55, 'APB', ha='center', fontsize=8)
        
        # Peripherals
        periphs = ['SPI', 'I2C', 'GPIO', 'TMR']
        for i, p in enumerate(periphs):
            per = Rectangle((0.6, 0.7-i*0.12), 0.08, 0.1,
                          facecolor='lightyellow', edgecolor='black')
            ax.add_patch(per)
            ax.text(0.64, 0.75-i*0.12, p, ha='center', fontsize=7)
            
    def _draw_automotive(self, ax):
        """Draw automotive system"""
        # Safety core
        safe = Rectangle((0.2, 0.6), 0.12, 0.2,
                        facecolor='lightcoral', edgecolor='red', linewidth=2)
        ax.add_patch(safe)
        ax.text(0.26, 0.7, 'Safety\nCore', ha='center', fontsize=8)
        
        # Application cores
        for i in range(2):
            app = Rectangle((0.2, 0.3-i*0.15), 0.12, 0.12,
                          facecolor='lightblue', edgecolor='black')
            ax.add_patch(app)
            ax.text(0.26, 0.36-i*0.15, f'App{i}', ha='center', fontsize=8)
            
        # NoC
        noc = Polygon([(0.4, 0.2), (0.4, 0.8), (0.7, 0.8), (0.7, 0.2)],
                     facecolor='gray', edgecolor='black', alpha=0.7)
        ax.add_patch(noc)
        ax.text(0.55, 0.5, 'NoC', ha='center', fontsize=10, color='white')
        
        # CAN/Ethernet
        can = Rectangle((0.75, 0.6), 0.1, 0.15,
                       facecolor='lightgreen', edgecolor='black')
        ax.add_patch(can)
        ax.text(0.8, 0.675, 'CAN', ha='center', fontsize=8)

def main():
    """Create the advanced user guide"""
    print("Creating advanced user guide with comprehensive content...")
    guide = AdvancedUserGuide()
    guide.create()

if __name__ == "__main__":
    main()