#!/usr/bin/env python3
"""
Create PDF User Guide for AMBA Bus Matrix Configuration Tool
Uses reportlab for PDF generation, falls back to text-based PDF if not available
"""

import os
import sys
from datetime import datetime

try:
    from reportlab.lib.pagesizes import letter, A4
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib.units import inch
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, PageBreak
    from reportlab.platypus import Table, TableStyle, Image, Preformatted
    from reportlab.lib import colors
    from reportlab.lib.enums import TA_JUSTIFY, TA_CENTER, TA_LEFT
    from reportlab.pdfgen import canvas
    from reportlab.platypus.tableofcontents import TableOfContents
    REPORTLAB_AVAILABLE = True
except ImportError:
    REPORTLAB_AVAILABLE = False
    print("Warning: reportlab not available. Creating simple PDF instead.")

# Try PyPDF2 as fallback
try:
    from fpdf import FPDF
    FPDF_AVAILABLE = True
except ImportError:
    FPDF_AVAILABLE = False

class UserGuidePDF:
    """Generate comprehensive PDF user guide"""
    
    def __init__(self):
        self.filename = "userguide.pdf"
        self.title = "AMBA Bus Matrix Configuration Tool"
        self.subtitle = "User Guide and Reference Manual"
        self.version = "1.0.0"
        self.date = datetime.now().strftime("%B %Y")
        
    def create_with_reportlab(self):
        """Create PDF using reportlab"""
        doc = SimpleDocTemplate(
            self.filename,
            pagesize=letter,
            rightMargin=72,
            leftMargin=72,
            topMargin=72,
            bottomMargin=18,
        )
        
        # Container for the 'Flowable' objects
        elements = []
        
        # Define styles
        styles = getSampleStyleSheet()
        styles.add(ParagraphStyle(
            name='CoverTitle',
            parent=styles['Title'],
            fontSize=36,
            textColor=colors.HexColor('#1a1a1a'),
            spaceAfter=12,
            alignment=TA_CENTER
        ))
        styles.add(ParagraphStyle(
            name='CoverSubtitle',
            parent=styles['Title'],
            fontSize=24,
            textColor=colors.HexColor('#4a4a4a'),
            spaceAfter=36,
            alignment=TA_CENTER
        ))
        styles.add(ParagraphStyle(
            name='ChapterTitle',
            parent=styles['Heading1'],
            fontSize=24,
            textColor=colors.HexColor('#2c3e50'),
            spaceAfter=24,
            keepWithNext=True
        ))
        styles.add(ParagraphStyle(
            name='SectionTitle',
            parent=styles['Heading2'],
            fontSize=18,
            textColor=colors.HexColor('#34495e'),
            spaceAfter=12,
            keepWithNext=True
        ))
        
        # Cover Page
        elements.append(Spacer(1, 2*inch))
        elements.append(Paragraph(self.title, styles['CoverTitle']))
        elements.append(Paragraph(self.subtitle, styles['CoverSubtitle']))
        elements.append(Spacer(1, 1*inch))
        elements.append(Paragraph(f"Version {self.version}", styles['Normal']))
        elements.append(Paragraph(self.date, styles['Normal']))
        elements.append(PageBreak())
        
        # Table of Contents
        elements.append(Paragraph("Table of Contents", styles['ChapterTitle']))
        elements.append(Spacer(1, 0.5*inch))
        
        toc_data = [
            ["1. Introduction", "3"],
            ["2. Getting Started", "5"],
            ["3. GUI Overview", "8"],
            ["4. Creating Bus Designs", "12"],
            ["5. RTL Generation", "18"],
            ["6. VIP Generation", "24"],
            ["7. Configuration Reference", "30"],
            ["8. Advanced Features", "36"],
            ["9. Troubleshooting", "42"],
            ["10. API Reference", "48"],
            ["Appendix A: AXI Protocol Overview", "54"],
            ["Appendix B: Example Configurations", "60"],
        ]
        
        toc_table = Table(toc_data, colWidths=[4*inch, 1*inch])
        toc_table.setStyle(TableStyle([
            ('ALIGN', (0, 0), (-1, -1), 'LEFT'),
            ('FONTNAME', (0, 0), (-1, -1), 'Helvetica'),
            ('FONTSIZE', (0, 0), (-1, -1), 12),
            ('BOTTOMPADDING', (0, 0), (-1, -1), 12),
        ]))
        elements.append(toc_table)
        elements.append(PageBreak())
        
        # Chapter 1: Introduction
        elements.append(Paragraph("1. Introduction", styles['ChapterTitle']))
        elements.append(Paragraph(
            """The AMBA Bus Matrix Configuration Tool is a comprehensive solution for designing 
            and implementing ARM AMBA-based System-on-Chip (SoC) interconnects. This tool provides 
            both a graphical user interface for visual design and a powerful backend for generating 
            synthesizable RTL and verification environments.""",
            styles['BodyText']
        ))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("1.1 Key Features", styles['SectionTitle']))
        features = [
            "Visual bus matrix design with drag-and-drop interface",
            "Support for AXI4, AXI3, AHB, and APB protocols",
            "Automatic RTL generation with parameterizable configurations",
            "Complete UVM-based verification environment generation",
            "Built-in address overlap detection and validation",
            "Security and QoS configuration support",
            "Integration with industry-standard EDA tools"
        ]
        for feature in features:
            elements.append(Paragraph(f"• {feature}", styles['BodyText']))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("1.2 System Requirements", styles['SectionTitle']))
        elements.append(Paragraph(
            """• Python 3.6 or higher
• Tkinter GUI library (usually included with Python)
• SystemVerilog simulator (VCS, Questa, or Xcelium)
• UVM 1.2 library
• 4GB RAM minimum, 8GB recommended
• 1GB free disk space""",
            styles['BodyText']
        ))
        elements.append(PageBreak())
        
        # Chapter 2: Getting Started
        elements.append(Paragraph("2. Getting Started", styles['ChapterTitle']))
        elements.append(Paragraph("2.1 Installation", styles['SectionTitle']))
        
        # Add code block style
        code_style = ParagraphStyle(
            'Code',
            parent=styles['Code'],
            fontName='Courier',
            fontSize=10,
            leftIndent=20,
            backColor=colors.HexColor('#f5f5f5')
        )
        
        elements.append(Paragraph("Clone the repository:", styles['BodyText']))
        elements.append(Preformatted(
            """cd /your/project/directory
git clone <repository_url>
cd axi4_vip/gui""",
            styles['Code']
        ))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("Install dependencies:", styles['BodyText']))
        elements.append(Preformatted(
            "pip install -r requirements.txt",
            styles['Code']
        ))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("2.2 Quick Start", styles['SectionTitle']))
        elements.append(Paragraph("Launch the GUI:", styles['BodyText']))
        elements.append(Preformatted("./launch_gui.sh", styles['Code']))
        elements.append(Spacer(1, 0.1*inch))
        
        elements.append(Paragraph(
            """The GUI will open with a blank canvas. Follow these steps to create your first design:
            
1. Select the bus protocol (AXI4 is default)
2. Click 'Add Master' to add bus masters
3. Click 'Add Slave' to add bus slaves  
4. Draw connections between masters and slaves
5. Configure addresses and parameters
6. Click 'Generate RTL' to create Verilog files
7. Click 'Generate VIP' to create verification environment""",
            styles['BodyText']
        ))
        elements.append(PageBreak())
        
        # Chapter 3: GUI Overview
        elements.append(Paragraph("3. GUI Overview", styles['ChapterTitle']))
        elements.append(Paragraph("3.1 Main Window Layout", styles['SectionTitle']))
        elements.append(Paragraph(
            """The main window consists of several key areas:
            
• Menu Bar: File operations, tools, and help
• Toolbar: Quick access to common functions
• Canvas: Main design area with grid
• Properties Panel: Configure selected components
• Status Bar: Current status and validation messages""",
            styles['BodyText']
        ))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("3.2 Canvas Operations", styles['SectionTitle']))
        elements.append(Table([
            ["Operation", "Action"],
            ["Pan", "Middle-click and drag"],
            ["Zoom", "Scroll wheel or Ctrl +/-"],
            ["Select", "Left-click on component"],
            ["Multi-select", "Ctrl+click or drag box"],
            ["Connect", "Drag from master to slave"],
            ["Delete", "Select and press Delete"],
            ["Properties", "Double-click component"],
        ], colWidths=[2*inch, 3*inch]))
        elements.append(PageBreak())
        
        # Chapter 4: Creating Bus Designs
        elements.append(Paragraph("4. Creating Bus Designs", styles['ChapterTitle']))
        elements.append(Paragraph("4.1 Adding Masters", styles['SectionTitle']))
        elements.append(Paragraph(
            """Masters represent components that initiate transactions. Common examples include:
• CPU cores
• DMA engines  
• GPU processors
• PCIe endpoints
• Video codecs

To add a master:
1. Click 'Add Master' button
2. Configure in the properties panel:
   - Name: Descriptive identifier
   - ID Width: Transaction ID bits (affects outstanding transactions)
   - Priority: Arbitration priority (higher wins)
   - QoS Support: Enable quality of service
   - Exclusive Support: Enable exclusive access""",
            styles['BodyText']
        ))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("4.2 Adding Slaves", styles['SectionTitle']))
        elements.append(Paragraph(
            """Slaves respond to transactions. Examples include:
• Memory controllers (DDR, SRAM)
• Peripheral registers
• Configuration spaces
• Bridge interfaces

To add a slave:
1. Click 'Add Slave' button  
2. Configure in the properties panel:
   - Name: Descriptive identifier
   - Base Address: Starting address (must be aligned)
   - Size: Address range in KB
   - Memory Type: Memory or Peripheral
   - Latency: Read/write cycle counts
   - Security: Access restrictions""",
            styles['BodyText']
        ))
        elements.append(PageBreak())
        
        # Chapter 5: RTL Generation
        elements.append(Paragraph("5. RTL Generation", styles['ChapterTitle']))
        elements.append(Paragraph("5.1 Generated Files", styles['SectionTitle']))
        elements.append(Paragraph(
            """The RTL generator creates the following Verilog modules:""",
            styles['BodyText']
        ))
        
        rtl_files = [
            ["Filename", "Description"],
            ["axi4_interconnect_mNsM.v", "Top-level interconnect module"],
            ["axi4_address_decoder.v", "Address decoding and routing logic"],
            ["axi4_arbiter.v", "Multi-master arbitration"],
            ["axi4_router.v", "Transaction routing logic"],
            ["tb_axi4_interconnect.v", "Basic testbench"],
        ]
        rtl_table = Table(rtl_files, colWidths=[2.5*inch, 3*inch])
        rtl_table.setStyle(TableStyle([
            ('GRID', (0, 0), (-1, -1), 1, colors.grey),
            ('BACKGROUND', (0, 0), (-1, 0), colors.lightgrey),
            ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
        ]))
        elements.append(rtl_table)
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("5.2 Module Parameters", styles['SectionTitle']))
        elements.append(Preformatted(
            """module axi4_interconnect_m2s3 #(
    parameter DATA_WIDTH = 128,
    parameter ADDR_WIDTH = 40,
    parameter ID_WIDTH   = 4,
    parameter USER_WIDTH = 1
)(
    input wire aclk,
    input wire aresetn,
    // Master and slave interfaces...
);""",
            styles['Code']
        ))
        elements.append(PageBreak())
        
        # Chapter 6: VIP Generation
        elements.append(Paragraph("6. VIP Generation", styles['ChapterTitle']))
        elements.append(Paragraph("6.1 Verification Environment Structure", styles['SectionTitle']))
        elements.append(Preformatted(
            """vip_output/
├── env/              # UVM environment classes
│   ├── axi_env.sv
│   ├── axi_agent.sv
│   └── axi_scoreboard.sv
├── tests/            # Test library
│   ├── axi_base_test.sv
│   ├── axi_basic_test.sv
│   └── axi_stress_test.sv
├── sequences/        # Sequence library
│   ├── axi_base_sequence.sv
│   ├── axi_burst_sequence.sv
│   └── axi_random_sequence.sv
├── tb/              # Testbench top files
│   ├── hvl_top.sv
│   └── hdl_top.sv
└── sim/             # Simulation scripts
    ├── Makefile
    └── run_test.sh""",
            styles['Code']
        ))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("6.2 Running Simulations", styles['SectionTitle']))
        elements.append(Paragraph("Basic simulation flow:", styles['BodyText']))
        elements.append(Preformatted(
            """cd vip_output/sim
make compile              # Compile design and testbench
make run TEST=axi_basic_test  # Run specific test
make run_all             # Run regression""",
            styles['Code']
        ))
        elements.append(PageBreak())
        
        # Chapter 7: Configuration Reference
        elements.append(Paragraph("7. Configuration Reference", styles['ChapterTitle']))
        elements.append(Paragraph("7.1 Master Configuration", styles['SectionTitle']))
        
        master_params = [
            ["Parameter", "Type", "Default", "Description"],
            ["name", "string", "-", "Master identifier"],
            ["id_width", "int", "4", "Transaction ID width"],
            ["user_width", "int", "0", "User signal width"],
            ["priority", "int", "0", "Arbitration priority"],
            ["qos_support", "bool", "true", "QoS enable"],
            ["exclusive_support", "bool", "true", "Exclusive access"],
            ["default_prot", "int", "0b010", "Default AxPROT"],
            ["default_cache", "int", "0b0011", "Default AxCACHE"],
        ]
        
        master_table = Table(master_params, colWidths=[1.2*inch, 0.8*inch, 0.8*inch, 2.7*inch])
        master_table.setStyle(TableStyle([
            ('GRID', (0, 0), (-1, -1), 1, colors.grey),
            ('BACKGROUND', (0, 0), (-1, 0), colors.lightgrey),
            ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
            ('FONTSIZE', (0, 0), (-1, -1), 9),
        ]))
        elements.append(master_table)
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("7.2 Slave Configuration", styles['SectionTitle']))
        
        slave_params = [
            ["Parameter", "Type", "Default", "Description"],
            ["name", "string", "-", "Slave identifier"],
            ["base_address", "hex", "-", "Base address"],
            ["size", "int", "-", "Size in KB"],
            ["memory_type", "enum", "Memory", "Memory or Peripheral"],
            ["read_latency", "int", "1", "Read cycles"],
            ["write_latency", "int", "1", "Write cycles"],
            ["num_regions", "int", "1", "Protection regions"],
            ["secure_only", "bool", "false", "Secure access only"],
        ]
        
        slave_table = Table(slave_params, colWidths=[1.2*inch, 0.8*inch, 0.8*inch, 2.7*inch])
        slave_table.setStyle(TableStyle([
            ('GRID', (0, 0), (-1, -1), 1, colors.grey),
            ('BACKGROUND', (0, 0), (-1, 0), colors.lightgrey),
            ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
            ('FONTSIZE', (0, 0), (-1, -1), 9),
        ]))
        elements.append(slave_table)
        elements.append(PageBreak())
        
        # Chapter 8: Advanced Features
        elements.append(Paragraph("8. Advanced Features", styles['ChapterTitle']))
        elements.append(Paragraph("8.1 Security Configuration", styles['SectionTitle']))
        elements.append(Paragraph(
            """The tool supports ARM TrustZone security extensions:
            
• Secure/Non-secure master designation
• Per-slave security requirements
• AxPROT[1] signal handling
• Security violation detection and reporting

Configure security in the Access Control Matrix.""",
            styles['BodyText']
        ))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("8.2 QoS and Priority", styles['SectionTitle']))
        elements.append(Paragraph(
            """Quality of Service features:
            
• 4-bit QoS values per transaction
• Priority-based arbitration
• Weighted round-robin support
• Latency-sensitive routing
• Bandwidth allocation""",
            styles['BodyText']
        ))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("8.3 Performance Optimization", styles['SectionTitle']))
        elements.append(Paragraph(
            """The generated RTL includes several optimizations:
            
• Registered outputs for timing closure
• Parameterizable pipeline stages
• Efficient arbitration logic
• Minimal combinatorial paths
• Clock domain crossing support""",
            styles['BodyText']
        ))
        elements.append(PageBreak())
        
        # Chapter 9: Troubleshooting
        elements.append(Paragraph("9. Troubleshooting", styles['ChapterTitle']))
        elements.append(Paragraph("9.1 Common Issues", styles['SectionTitle']))
        
        issues = [
            ["Issue", "Solution"],
            ["GUI won't launch", "Check Python version and tkinter installation"],
            ["Import errors", "Verify all dependencies: pip install -r requirements.txt"],
            ["Address overlap", "Use address map viewer, check alignment"],
            ["RTL syntax errors", "Update to latest version, check generated files"],
            ["VIP compile errors", "Set UVM_HOME, check simulator version"],
            ["Width mismatches", "Regenerate with latest fixes, check ID_WIDTH"],
        ]
        
        issues_table = Table(issues, colWidths=[2*inch, 3.5*inch])
        issues_table.setStyle(TableStyle([
            ('GRID', (0, 0), (-1, -1), 1, colors.grey),
            ('BACKGROUND', (0, 0), (-1, 0), colors.lightgrey),
            ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
            ('VALIGN', (0, 0), (-1, -1), 'TOP'),
        ]))
        elements.append(issues_table)
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("9.2 Debug Mode", styles['SectionTitle']))
        elements.append(Paragraph("Enable debug output:", styles['BodyText']))
        elements.append(Preformatted(
            """export AXI_VIP_DEBUG=1
./launch_gui.sh --debug""",
            styles['Code']
        ))
        elements.append(PageBreak())
        
        # Chapter 10: API Reference
        elements.append(Paragraph("10. API Reference", styles['ChapterTitle']))
        elements.append(Paragraph("10.1 Command Line Interface", styles['SectionTitle']))
        elements.append(Preformatted(
            """python3 src/bus_matrix_gui.py [options]

Options:
  --template FILE     Load template configuration
  --config FILE       Load saved configuration
  --output DIR        Set output directory
  --batch             Run in batch mode (no GUI)
  --generate-rtl      Generate RTL only
  --generate-vip      Generate VIP only
  --validate          Validate configuration only
  --debug             Enable debug output
  --version           Show version information
  --help              Show this help message""",
            styles['Code']
        ))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("10.2 Python API", styles['SectionTitle']))
        elements.append(Paragraph("Example script:", styles['BodyText']))
        elements.append(Preformatted(
            """from bus_config import BusConfig, Master, Slave
from axi_verilog_generator import AXIVerilogGenerator

# Create configuration
config = BusConfig()
config.data_width = 128
config.addr_width = 40

# Add master
master = Master("CPU")
master.id_width = 4
config.masters.append(master)

# Add slave  
slave = Slave("Memory", 0x0, 1048576)
config.slaves.append(slave)

# Generate RTL
gen = AXIVerilogGenerator(config)
gen.generate()""",
            styles['Code']
        ))
        elements.append(PageBreak())
        
        # Appendix A
        elements.append(Paragraph("Appendix A: AXI Protocol Overview", styles['ChapterTitle']))
        elements.append(Paragraph(
            """The AMBA AXI protocol is a high-performance, high-frequency protocol that supports:
            
• Separate read and write channels
• Multiple outstanding transactions
• Out-of-order transaction completion
• Burst transactions with only start address issued
• Byte-lane strobes for partial writes
• QoS signaling
• Security extensions""",
            styles['BodyText']
        ))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("AXI Channels:", styles['SectionTitle']))
        channels = [
            ["Channel", "Direction", "Signals"],
            ["Write Address", "Master→Slave", "AWID, AWADDR, AWLEN, AWSIZE, AWBURST, AWLOCK, AWCACHE, AWPROT, AWQOS, AWVALID, AWREADY"],
            ["Write Data", "Master→Slave", "WDATA, WSTRB, WLAST, WVALID, WREADY"],
            ["Write Response", "Slave→Master", "BID, BRESP, BVALID, BREADY"],
            ["Read Address", "Master→Slave", "ARID, ARADDR, ARLEN, ARSIZE, ARBURST, ARLOCK, ARCACHE, ARPROT, ARQOS, ARVALID, ARREADY"],
            ["Read Data", "Slave→Master", "RID, RDATA, RRESP, RLAST, RVALID, RREADY"],
        ]
        
        channels_table = Table(channels, colWidths=[1.2*inch, 1.2*inch, 3.1*inch])
        channels_table.setStyle(TableStyle([
            ('GRID', (0, 0), (-1, -1), 1, colors.grey),
            ('BACKGROUND', (0, 0), (-1, 0), colors.lightgrey),
            ('FONTNAME', (0, 0), (-1, 0), 'Helvetica-Bold'),
            ('FONTSIZE', (0, 0), (-1, -1), 8),
            ('VALIGN', (0, 0), (-1, -1), 'TOP'),
        ]))
        elements.append(channels_table)
        elements.append(PageBreak())
        
        # Appendix B
        elements.append(Paragraph("Appendix B: Example Configurations", styles['ChapterTitle']))
        elements.append(Paragraph("B.1 Simple System (2 Masters, 3 Slaves)", styles['SectionTitle']))
        elements.append(Preformatted(
            """{
  "bus_type": "AXI4",
  "data_width": 64,
  "addr_width": 32,
  "masters": [
    {"name": "CPU", "id_width": 4, "priority": 1},
    {"name": "DMA", "id_width": 4, "priority": 0}
  ],
  "slaves": [
    {"name": "RAM", "base_address": "0x00000000", "size": 1048576},
    {"name": "ROM", "base_address": "0x10000000", "size": 65536},
    {"name": "UART", "base_address": "0x20000000", "size": 4}
  ]
}""",
            styles['Code']
        ))
        elements.append(Spacer(1, 0.2*inch))
        
        elements.append(Paragraph("B.2 High-Performance Computing System", styles['SectionTitle']))
        elements.append(Paragraph(
            """This example shows a complex SoC with multiple CPU clusters, GPU, and various memories:
• 8 masters with different priorities and QoS requirements
• 8 slaves including DDR controllers, caches, and peripherals
• Security zones and access control
• Optimized for high bandwidth and low latency""",
            styles['BodyText']
        ))
        
        # Build PDF
        doc.build(elements)
        print(f"Created {self.filename} using reportlab")
        
    def create_with_fpdf(self):
        """Create PDF using FPDF as fallback"""
        pdf = FPDF()
        pdf.set_auto_page_break(auto=True, margin=15)
        
        # Cover page
        pdf.add_page()
        pdf.set_font("Arial", 'B', 32)
        pdf.cell(0, 40, self.title, 0, 1, 'C')
        pdf.set_font("Arial", 'B', 20)
        pdf.cell(0, 20, self.subtitle, 0, 1, 'C')
        pdf.ln(20)
        pdf.set_font("Arial", '', 14)
        pdf.cell(0, 10, f"Version {self.version}", 0, 1, 'C')
        pdf.cell(0, 10, self.date, 0, 1, 'C')
        
        # Table of Contents
        pdf.add_page()
        pdf.set_font("Arial", 'B', 24)
        pdf.cell(0, 20, "Table of Contents", 0, 1)
        pdf.set_font("Arial", '', 12)
        
        toc_items = [
            "1. Introduction",
            "2. Getting Started", 
            "3. GUI Overview",
            "4. Creating Bus Designs",
            "5. RTL Generation",
            "6. VIP Generation",
            "7. Configuration Reference",
            "8. Advanced Features",
            "9. Troubleshooting",
            "10. API Reference"
        ]
        
        for item in toc_items:
            pdf.cell(0, 8, item, 0, 1)
        
        # Chapter 1
        pdf.add_page()
        pdf.set_font("Arial", 'B', 20)
        pdf.cell(0, 15, "1. Introduction", 0, 1)
        pdf.set_font("Arial", '', 11)
        pdf.multi_cell(0, 5, 
            """The AMBA Bus Matrix Configuration Tool is a comprehensive solution for designing 
and implementing ARM AMBA-based System-on-Chip (SoC) interconnects. This tool provides 
both a graphical user interface for visual design and a powerful backend for generating 
synthesizable RTL and verification environments.""")
        
        # Save PDF
        pdf.output(self.filename)
        print(f"Created {self.filename} using FPDF")
        
    def create_simple_pdf(self):
        """Create a simple text-based PDF without external libraries"""
        content = f"""%PDF-1.4
1 0 obj
<< /Type /Catalog /Pages 2 0 R >>
endobj
2 0 obj
<< /Type /Pages /Kids [3 0 R] /Count 1 >>
endobj
3 0 obj
<< /Type /Page /Parent 2 0 R /Resources 4 0 R /MediaBox [0 0 612 792]
/Contents 5 0 R >>
endobj
4 0 obj
<< /Font << /F1 << /Type /Font /Subtype /Type1 /BaseFont /Helvetica >> >> >>
endobj
5 0 obj
<< /Length 500 >>
stream
BT
/F1 24 Tf
100 700 Td
({self.title}) Tj
0 -30 Td
/F1 16 Tf
({self.subtitle}) Tj
0 -50 Td
/F1 12 Tf
(Version {self.version} - {self.date}) Tj
0 -50 Td
(This is a simplified PDF. For full documentation, please install reportlab:) Tj
0 -20 Td
(pip install reportlab) Tj
0 -40 Td
(Then run: python3 create_userguide_pdf.py) Tj
0 -40 Td
(Or see README.md for complete documentation.) Tj
ET
endstream
endobj
xref
0 6
0000000000 65535 f 
0000000009 00000 n 
0000000058 00000 n 
0000000115 00000 n 
0000000214 00000 n 
0000000312 00000 n 
trailer
<< /Size 6 /Root 1 0 R >>
startxref
865
%%EOF"""
        
        with open(self.filename, 'w') as f:
            f.write(content)
        print(f"Created simplified {self.filename}")
        print("For full PDF documentation, install reportlab: pip install reportlab")
        
    def create(self):
        """Create PDF using available method"""
        if REPORTLAB_AVAILABLE:
            self.create_with_reportlab()
        elif FPDF_AVAILABLE:
            self.create_with_fpdf()
        else:
            self.create_simple_pdf()
            
def main():
    """Create the user guide PDF"""
    print("Creating AMBA Bus Matrix Configuration Tool User Guide PDF...")
    
    guide = UserGuidePDF()
    guide.create()
    
    print(f"\nUser guide created: {guide.filename}")
    print(f"File size: {os.path.getsize(guide.filename) / 1024:.1f} KB")
    
    if not REPORTLAB_AVAILABLE:
        print("\nNote: For a complete PDF with formatting, install reportlab:")
        print("  pip install reportlab")
        print("  python3 create_userguide_pdf.py")

if __name__ == "__main__":
    main()