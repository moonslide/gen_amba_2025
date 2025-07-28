#!/usr/bin/env python3
"""
Create an HTML user guide that can be easily converted to PDF
"""

import os
from datetime import datetime

class HTMLUserGuide:
    """Generate comprehensive HTML user guide"""
    
    def __init__(self):
        self.filename = "userguide.html"
        self.title = "AMBA Bus Matrix Configuration Tool"
        self.version = "1.0.0"
        self.date = datetime.now().strftime("%B %Y")
        
    def create(self):
        """Create the HTML guide"""
        
        html_content = f"""<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{self.title} - User Guide</title>
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, Arial, sans-serif;
            line-height: 1.6;
            color: #333;
            max-width: 900px;
            margin: 0 auto;
            padding: 20px;
            background: #f5f5f5;
        }}
        .container {{
            background: white;
            padding: 40px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        h1 {{
            color: #2c3e50;
            border-bottom: 3px solid #3498db;
            padding-bottom: 10px;
        }}
        h2 {{
            color: #34495e;
            margin-top: 30px;
            border-bottom: 1px solid #ecf0f1;
            padding-bottom: 5px;
        }}
        h3 {{
            color: #7f8c8d;
            margin-top: 20px;
        }}
        code {{
            background: #f8f9fa;
            padding: 2px 6px;
            border-radius: 3px;
            font-family: 'Courier New', Courier, monospace;
            font-size: 0.9em;
        }}
        pre {{
            background: #2c3e50;
            color: #ecf0f1;
            padding: 15px;
            border-radius: 5px;
            overflow-x: auto;
            line-height: 1.4;
        }}
        pre code {{
            background: none;
            color: #ecf0f1;
            padding: 0;
        }}
        .toc {{
            background: #ecf0f1;
            padding: 20px;
            border-radius: 5px;
            margin: 20px 0;
        }}
        .toc h2 {{
            margin-top: 0;
            border: none;
        }}
        .toc ul {{
            list-style: none;
            padding-left: 20px;
        }}
        .toc a {{
            color: #3498db;
            text-decoration: none;
        }}
        .toc a:hover {{
            text-decoration: underline;
        }}
        .feature-box {{
            background: #e8f6f3;
            border-left: 4px solid #27ae60;
            padding: 15px;
            margin: 20px 0;
        }}
        .warning-box {{
            background: #fef5e7;
            border-left: 4px solid #f39c12;
            padding: 15px;
            margin: 20px 0;
        }}
        .info-box {{
            background: #ebf5fb;
            border-left: 4px solid #3498db;
            padding: 15px;
            margin: 20px 0;
        }}
        table {{
            border-collapse: collapse;
            width: 100%;
            margin: 20px 0;
        }}
        th, td {{
            border: 1px solid #ddd;
            padding: 12px;
            text-align: left;
        }}
        th {{
            background: #34495e;
            color: white;
        }}
        tr:nth-child(even) {{
            background: #f8f9fa;
        }}
        .button {{
            display: inline-block;
            padding: 10px 20px;
            background: #3498db;
            color: white;
            text-decoration: none;
            border-radius: 5px;
            margin: 10px 5px;
        }}
        .button:hover {{
            background: #2980b9;
        }}
        @media print {{
            body {{
                background: white;
            }}
            .container {{
                box-shadow: none;
                padding: 0;
            }}
            .no-print {{
                display: none;
            }}
        }}
    </style>
</head>
<body>
    <div class="container">
        <h1>{self.title}</h1>
        <p><strong>Version {self.version}</strong> | {self.date}</p>
        
        <div class="toc">
            <h2>Table of Contents</h2>
            <ul>
                <li><a href="#overview">1. Overview</a></li>
                <li><a href="#getting-started">2. Getting Started</a>
                    <ul>
                        <li><a href="#installation">2.1 Installation</a></li>
                        <li><a href="#quick-start">2.2 Quick Start</a></li>
                    </ul>
                </li>
                <li><a href="#gui-usage">3. GUI Usage</a>
                    <ul>
                        <li><a href="#interface">3.1 Interface Overview</a></li>
                        <li><a href="#creating-designs">3.2 Creating Designs</a></li>
                    </ul>
                </li>
                <li><a href="#configuration">4. Configuration</a>
                    <ul>
                        <li><a href="#masters">4.1 Master Configuration</a></li>
                        <li><a href="#slaves">4.2 Slave Configuration</a></li>
                    </ul>
                </li>
                <li><a href="#generation">5. Code Generation</a>
                    <ul>
                        <li><a href="#rtl-gen">5.1 RTL Generation</a></li>
                        <li><a href="#vip-gen">5.2 VIP Generation</a></li>
                    </ul>
                </li>
                <li><a href="#advanced">6. Advanced Features</a></li>
                <li><a href="#troubleshooting">7. Troubleshooting</a></li>
                <li><a href="#examples">8. Examples</a></li>
            </ul>
        </div>
        
        <h2 id="overview">1. Overview</h2>
        <p>The AMBA Bus Matrix Configuration Tool is a comprehensive solution for designing and implementing ARM AMBA-based System-on-Chip (SoC) interconnects. It provides both a graphical user interface for visual design and powerful code generation capabilities.</p>
        
        <div class="feature-box">
            <h3>Key Features</h3>
            <ul>
                <li>Visual drag-and-drop bus matrix design</li>
                <li>Support for AXI4, AXI3, AHB, and APB protocols</li>
                <li>Automatic RTL generation with parameterizable configurations</li>
                <li>Complete UVM-based verification environment generation</li>
                <li>Built-in validation and address overlap detection</li>
                <li>Security and QoS configuration support</li>
            </ul>
        </div>
        
        <h2 id="getting-started">2. Getting Started</h2>
        
        <h3 id="installation">2.1 Installation</h3>
        <p>Follow these steps to install the tool:</p>
        
        <pre><code># Clone the repository
cd /your/project/directory
git clone &lt;repository_url&gt;
cd axi4_vip/gui

# Install dependencies
pip install -r requirements.txt</code></pre>
        
        <div class="info-box">
            <strong>System Requirements:</strong>
            <ul>
                <li>Python 3.6 or higher</li>
                <li>Tkinter GUI library (usually included with Python)</li>
                <li>SystemVerilog simulator (VCS, Questa, or Xcelium)</li>
                <li>UVM 1.2 library</li>
            </ul>
        </div>
        
        <h3 id="quick-start">2.2 Quick Start</h3>
        <p>Launch the GUI and create your first design:</p>
        
        <pre><code># Launch the GUI
./launch_gui.sh

# Or with Python directly
python3 src/bus_matrix_gui.py</code></pre>
        
        <h2 id="gui-usage">3. GUI Usage</h2>
        
        <h3 id="interface">3.1 Interface Overview</h3>
        <p>The main window consists of several key areas:</p>
        
        <table>
            <tr>
                <th>Component</th>
                <th>Description</th>
            </tr>
            <tr>
                <td>Menu Bar</td>
                <td>File operations, tools, and help</td>
            </tr>
            <tr>
                <td>Toolbar</td>
                <td>Quick access buttons for common operations</td>
            </tr>
            <tr>
                <td>Canvas</td>
                <td>Main design area with grid for component placement</td>
            </tr>
            <tr>
                <td>Properties Panel</td>
                <td>Configure selected components</td>
            </tr>
            <tr>
                <td>Status Bar</td>
                <td>Current status and validation messages</td>
            </tr>
        </table>
        
        <h3 id="creating-designs">3.2 Creating Designs</h3>
        <p>Follow these steps to create a bus matrix:</p>
        
        <ol>
            <li><strong>Add Masters:</strong> Click "Add Master" and configure properties</li>
            <li><strong>Add Slaves:</strong> Click "Add Slave" and set address ranges</li>
            <li><strong>Connect:</strong> Drag from masters to slaves to create connections</li>
            <li><strong>Validate:</strong> Use Tools → Validate to check configuration</li>
            <li><strong>Generate:</strong> Click "Generate RTL" and "Generate VIP"</li>
        </ol>
        
        <h2 id="configuration">4. Configuration</h2>
        
        <h3 id="masters">4.1 Master Configuration</h3>
        <p>Masters initiate transactions on the bus. Common examples include CPUs, DMAs, and GPUs.</p>
        
        <table>
            <tr>
                <th>Parameter</th>
                <th>Description</th>
                <th>Default</th>
            </tr>
            <tr>
                <td>Name</td>
                <td>Unique identifier for the master</td>
                <td>-</td>
            </tr>
            <tr>
                <td>ID Width</td>
                <td>Transaction ID bits (affects outstanding capability)</td>
                <td>4</td>
            </tr>
            <tr>
                <td>Priority</td>
                <td>Arbitration priority (higher wins)</td>
                <td>0</td>
            </tr>
            <tr>
                <td>QoS Support</td>
                <td>Enable quality of service signaling</td>
                <td>Yes</td>
            </tr>
            <tr>
                <td>Exclusive Support</td>
                <td>Enable exclusive access transactions</td>
                <td>Yes</td>
            </tr>
        </table>
        
        <h3 id="slaves">4.2 Slave Configuration</h3>
        <p>Slaves respond to transactions. Examples include memories and peripherals.</p>
        
        <table>
            <tr>
                <th>Parameter</th>
                <th>Description</th>
                <th>Default</th>
            </tr>
            <tr>
                <td>Name</td>
                <td>Unique identifier for the slave</td>
                <td>-</td>
            </tr>
            <tr>
                <td>Base Address</td>
                <td>Starting address (must be aligned)</td>
                <td>-</td>
            </tr>
            <tr>
                <td>Size</td>
                <td>Address range in KB</td>
                <td>-</td>
            </tr>
            <tr>
                <td>Memory Type</td>
                <td>Memory or Peripheral</td>
                <td>Memory</td>
            </tr>
            <tr>
                <td>Read Latency</td>
                <td>Read response cycles</td>
                <td>1</td>
            </tr>
            <tr>
                <td>Write Latency</td>
                <td>Write response cycles</td>
                <td>1</td>
            </tr>
        </table>
        
        <h2 id="generation">5. Code Generation</h2>
        
        <h3 id="rtl-gen">5.1 RTL Generation</h3>
        <p>The tool generates synthesizable Verilog RTL for the configured bus matrix.</p>
        
        <div class="info-box">
            <strong>Generated RTL Files:</strong>
            <ul>
                <li><code>axi4_interconnect_mNsM.v</code> - Top-level interconnect</li>
                <li><code>axi4_address_decoder.v</code> - Address decoding logic</li>
                <li><code>axi4_arbiter.v</code> - Arbitration logic</li>
                <li><code>axi4_router.v</code> - Transaction routing</li>
                <li><code>tb_axi4_interconnect.v</code> - Basic testbench</li>
            </ul>
        </div>
        
        <h3 id="vip-gen">5.2 VIP Generation</h3>
        <p>Complete UVM verification environment with:</p>
        
        <pre><code>vip_output/
├── env/           # UVM environment classes
├── tests/         # Test library
├── sequences/     # Sequence library
├── tb/           # Testbench files
└── sim/          # Simulation scripts</code></pre>
        
        <h2 id="advanced">6. Advanced Features</h2>
        
        <h3>Security Configuration</h3>
        <p>Configure TrustZone security with:</p>
        <ul>
            <li>Secure/non-secure master designation</li>
            <li>Per-slave security requirements</li>
            <li>Access control matrices</li>
        </ul>
        
        <h3>Quality of Service</h3>
        <p>Implement QoS with:</p>
        <ul>
            <li>4-bit QoS values per transaction</li>
            <li>Priority-based arbitration</li>
            <li>Weighted round-robin support</li>
        </ul>
        
        <h2 id="troubleshooting">7. Troubleshooting</h2>
        
        <div class="warning-box">
            <h3>Common Issues</h3>
            
            <p><strong>Port Width Mismatch Warnings</strong></p>
            <pre><code>Lint-[PCWM-L] Port connection width mismatch</code></pre>
            <p><em>Solution:</em> Regenerate RTL with the latest tool version.</p>
            
            <p><strong>GUI Won't Launch</strong></p>
            <pre><code>ImportError: No module named 'tkinter'</code></pre>
            <p><em>Solution:</em> Install tkinter: <code>apt-get install python3-tk</code></p>
            
            <p><strong>Address Overlap Error</strong></p>
            <p><em>Solution:</em> Check slave address ranges don't overlap. Use the address map viewer.</p>
        </div>
        
        <h2 id="examples">8. Examples</h2>
        
        <h3>Simple 2×3 System</h3>
        <pre><code>python3 examples/create_simple_system.py</code></pre>
        
        <h3>High-Performance System</h3>
        <pre><code>python3 examples/performance_analysis.py</code></pre>
        
        <h3>Security-Aware System</h3>
        <pre><code>python3 examples/create_secure_system.py</code></pre>
        
        <div class="info-box no-print">
            <h3>Additional Resources</h3>
            <p>
                <a href="README.md" class="button">View README</a>
                <a href="examples/" class="button">Browse Examples</a>
                <a href="https://github.com/your-repo" class="button">GitHub Repository</a>
            </p>
        </div>
        
        <hr style="margin-top: 50px;">
        <p style="text-align: center; color: #7f8c8d;">
            AMBA Bus Matrix Configuration Tool v{self.version}<br>
            {self.date}
        </p>
    </div>
</body>
</html>"""
        
        with open(self.filename, 'w') as f:
            f.write(html_content)
        
        print(f"Created {self.filename}")
        print("\nTo convert to PDF:")
        print("1. Open userguide.html in a web browser")
        print("2. Print to PDF (Ctrl+P)")
        print("3. Or use: wkhtmltopdf userguide.html userguide.pdf")
        
def main():
    """Create the HTML user guide"""
    guide = HTMLUserGuide()
    guide.create()
    
    # Also create a simple PDF using the basic method
    print("\nCreating basic PDF...")
    os.system("python3 create_userguide_pdf.py")

if __name__ == "__main__":
    main()