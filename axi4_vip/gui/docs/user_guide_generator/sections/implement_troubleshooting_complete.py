#!/usr/bin/env python3
"""
Implement COMPLETE Troubleshooting section (pages 78-84) with full detailed content
NO PLACEHOLDERS - every page fully implemented with real information
7 pages of comprehensive troubleshooting content
"""

def create_complete_troubleshooting_section(pdf_generator, pdf):
    """Complete Troubleshooting section - 7 pages of detailed content"""
    
    # Page 78: Troubleshooting Overview and Common Issues
    troubleshooting_overview = """
This section provides comprehensive troubleshooting guidance for common issues
encountered when using the AMBA Bus Matrix Configuration Tool. Issues are
categorized by symptom with step-by-step resolution procedures.

TROUBLESHOOTING CATEGORIES:

Installation and Setup Issues:
• Python environment and dependency problems
• GUI framework installation failures
• Missing system libraries and packages
• Platform-specific compatibility issues
• License and permission problems

GUI Application Issues:
• Application launch failures
• Interface rendering problems
• Performance and responsiveness issues
• Data corruption and file I/O errors
• Memory usage and resource leaks

Design Configuration Issues:
• Address map conflicts and overlaps
• Invalid parameter combinations
• Connectivity and routing problems
• Protocol compliance violations
• Resource constraint violations

RTL Generation Issues:
• Generation process failures
• Invalid or malformed output files
• Synthesis and timing closure problems
• Functional verification failures
• Integration and compatibility issues

VIP Generation Issues:
• UVM environment compilation errors
• Testbench runtime failures
• Coverage collection problems
• Assertion and checker failures
• Performance and scalability issues

System Integration Issues:
• Tool integration problems
• Version compatibility conflicts
• File format incompatibilities
• Workflow automation failures
• Multi-user and revision control issues

DIAGNOSTIC METHODOLOGY:

Problem Identification:
1. Gather symptom information
2. Reproduce the issue consistently
3. Check system requirements and prerequisites
4. Review error messages and log files
5. Identify recent changes or updates

Root Cause Analysis:
1. Isolate variables and dependencies
2. Test with minimal configurations
3. Check for known issues and workarounds
4. Validate input data and parameters
5. Examine system resource utilization

Resolution and Verification:
1. Apply appropriate corrective actions
2. Verify resolution with test cases
3. Document solution for future reference
4. Implement preventive measures
5. Update procedures and guidelines

COMMON ISSUE CATEGORIES:

Critical Issues (System Preventing):
• Application won't launch
• Complete generation failures
• Data loss or corruption
• License or authentication failures

Major Issues (Workflow Blocking): 
• Partial generation failures
• Invalid output quality
• Performance degradation
• Integration compatibility problems

Minor Issues (Usability):
• GUI display anomalies
• Warning messages
• Suboptimal performance
• Documentation discrepancies

GETTING HELP:

Self-Service Resources:
• This troubleshooting guide
• Online documentation and FAQ
• Example configurations and templates
• Video tutorials and guides

Support Channels:
• GitHub issue tracker for bug reports
• Community forums for questions
• Direct email support for licensed users
• Professional services for custom needs

Information to Include in Support Requests:
• Tool version and build information
• Operating system and environment details
• Complete error messages and logs
• Minimal configuration reproducing the issue
• Steps taken to resolve the problem
"""
    pdf_generator.create_text_page(pdf, "7. Troubleshooting", "Overview", troubleshooting_overview)
    
    # Page 79: Installation and Environment Issues
    installation_issues = """
7.1 Installation and Environment Issues

PYTHON ENVIRONMENT ISSUES:

Issue: "Python command not found"
Symptoms:
• Terminal shows "python: command not found"
• "python3: command not found"
• Application fails to launch

Root Cause: Python not installed or not in system PATH
Resolution Steps:
1. Install Python 3.6 or higher:
   
   Ubuntu/Debian:
   sudo apt update
   sudo apt install python3 python3-pip
   
   CentOS/RHEL:
   sudo yum install python3 python3-pip
   
   macOS:
   brew install python3
   
   Windows:
   Download from python.org and run installer
   ✓ Check "Add Python to PATH"

2. Verify installation:
   python3 --version
   pip3 --version

3. Update PATH if necessary:
   export PATH="/usr/local/bin/python3:$PATH"

Issue: "ImportError: No module named tkinter"
Symptoms:
• GUI application fails to start
• Error mentions tkinter, _tkinter, or Tk

Root Cause: Tkinter GUI library not installed
Resolution Steps:
1. Install tkinter package:
   
   Ubuntu/Debian:
   sudo apt install python3-tk
   
   CentOS/RHEL:
   sudo yum install tkinter
   # or
   sudo dnf install python3-tkinter
   
   macOS (with Homebrew):
   # Usually included with Python
   # If issues persist:
   brew install python-tk
   
   Windows:
   # Usually included with Python
   # If missing, reinstall Python with "tcl/tk and IDLE" option

2. Test tkinter installation:
   python3 -c "import tkinter; print('Tkinter OK')"

Issue: "ModuleNotFoundError: No module named 'matplotlib'"
Symptoms:
• PDF generation fails
• Import errors for visualization modules

Resolution Steps:
1. Install required Python packages:
   pip3 install matplotlib
   pip3 install numpy
   pip3 install pillow

2. For comprehensive installation:
   pip3 install -r requirements.txt

3. If pip fails with permissions:
   pip3 install --user matplotlib numpy pillow

DEPENDENCY AND LIBRARY ISSUES:

Issue: "ImportError: libpng.so.16: cannot open shared object file"
Symptoms:
• Application crashes on startup
• Graphics-related library errors

Root Cause: Missing system graphics libraries
Resolution Steps:
1. Install required system libraries:
   
   Ubuntu/Debian:
   sudo apt install libpng-dev libjpeg-dev libfreetype6-dev
   
   CentOS/RHEL:
   sudo yum install libpng-devel libjpeg-devel freetype-devel

2. Update library cache:
   sudo ldconfig

Issue: "Permission denied" when running scripts
Symptoms:
• "./launch_gui.sh: Permission denied"
• Cannot execute shell scripts

Resolution Steps:
1. Make scripts executable:
   chmod +x launch_gui.sh
   chmod +x *.sh

2. Check directory permissions:
   ls -la launch_gui.sh
   # Should show: -rwxr-xr-x

3. If in wrong directory:
   cd /path/to/axi4_vip/gui
   ./launch_gui.sh

PLATFORM-SPECIFIC ISSUES:

Windows-Specific Issues:
Issue: "python is not recognized as internal or external command"
Resolution:
1. Add Python to system PATH:
   • Control Panel → System → Advanced → Environment Variables
   • Add Python installation directory to PATH
   • Typical path: C:\\Python39\\Scripts;C:\\Python39\\

2. Use Python Launcher:
   py -3 src/bus_matrix_gui.py

Issue: Antivirus blocking execution
Resolution:
1. Add tool directory to antivirus exclusions
2. Temporarily disable real-time protection during installation
3. Use Windows Defender exclusions if applicable

macOS-Specific Issues:
Issue: "Application is not signed by identified developer"
Resolution:
1. Allow unsigned applications:
   System Preferences → Security & Privacy → General
   → "Allow apps downloaded from: App Store and identified developers"

2. For specific application:
   Right-click application → Open
   → Click "Open" in security dialog

Issue: Homebrew permission issues
Resolution:
1. Fix Homebrew permissions:
   sudo chown -R $(whoami) /usr/local/var/homebrew
   
2. Update Homebrew:
   brew update
   brew doctor

Linux-Specific Issues:
Issue: Display issues with remote X11
Resolution:
1. Enable X11 forwarding:
   ssh -X username@hostname
   
2. Set DISPLAY variable:
   export DISPLAY=:0.0
   
3. Install X11 libraries:
   sudo apt install libx11-dev libxtst6

Issue: Missing development headers
Resolution:
1. Install build essentials:
   sudo apt install build-essential
   sudo apt install python3-dev

ENVIRONMENT VALIDATION:

System Compatibility Check:
#!/bin/bash
echo "=== System Compatibility Check ==="

# Check Python version
echo "Python version:"
python3 --version
if [ $? -ne 0 ]; then
    echo "ERROR: Python 3 not found"
    exit 1
fi

# Check required modules
echo "Checking Python modules..."
python3 -c "import tkinter; print('✓ tkinter')" 2>/dev/null || echo "✗ tkinter MISSING"
python3 -c "import matplotlib; print('✓ matplotlib')" 2>/dev/null || echo "✗ matplotlib MISSING"
python3 -c "import numpy; print('✓ numpy')" 2>/dev/null || echo "✗ numpy MISSING"

# Check disk space
echo "Disk space check:"
df -h . | tail -1 | awk '{print "Available: " $4}'

# Check memory
echo "Memory check:"
free -h | grep "Mem:" | awk '{print "Available: " $7}'

echo "=== Check Complete ==="

Quick Environment Setup Script:
#!/bin/bash
# quick_setup.sh - Automated environment setup

set -e

echo "Setting up AMBA Bus Matrix Tool environment..."

# Detect OS
if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    # Linux
    sudo apt update
    sudo apt install -y python3 python3-pip python3-tk
    sudo apt install -y libpng-dev libjpeg-dev libfreetype6-dev
elif [[ "$OSTYPE" == "darwin"* ]]; then
    # macOS  
    brew install python3
    brew install python-tk
else
    echo "Unsupported OS: $OSTYPE"
    exit 1
fi

# Install Python packages
pip3 install --user matplotlib numpy pillow

# Make scripts executable
chmod +x *.sh

# Test installation
python3 -c "import tkinter, matplotlib; print('✅ Environment ready!')"

echo "✅ Setup complete! Run './launch_gui.sh' to start."
"""
    pdf_generator.create_text_page(pdf, "7.1 Installation Issues", None, installation_issues, code_style=True)
    
    # Page 80: GUI Application Issues
    gui_issues = """
7.2 GUI Application Issues

APPLICATION LAUNCH ISSUES:

Issue: GUI window doesn't appear
Symptoms:
• Application starts but no window visible
• Process running but no interface
• Blank or black window

Diagnostic Steps:
1. Check if process is running:
   ps aux | grep bus_matrix_gui
   
2. Check display configuration:
   echo $DISPLAY
   xhost +  # For X11 systems

3. Check window manager compatibility:
   wmctrl -l  # List windows
   
Resolution Steps:
1. Force window to foreground:
   python3 src/bus_matrix_gui.py --force-foreground
   
2. Reset window manager state:
   rm ~/.config/bus_matrix_tool/window_state.conf
   
3. Try different GUI backend:
   export TK_BACKEND=default
   python3 src/bus_matrix_gui.py

Issue: "TclError: no display name and no $DISPLAY environment variable"
Symptoms:
• Error occurs on Linux systems
• Application fails immediately on startup
• Remote terminal access issues

Root Cause: X11 display not properly configured
Resolution Steps:
1. For local display:
   export DISPLAY=:0
   
2. For SSH with X11 forwarding:
   ssh -X username@hostname
   # or
   ssh -Y username@hostname  # Trusted X11 forwarding
   
3. For VNC or virtual display:
   export DISPLAY=:1  # Match VNC display number
   
4. Test X11 functionality:
   xeyes  # Simple X11 test application
   xclock # Another test

INTERFACE RENDERING ISSUES:

Issue: Blurry or pixelated GUI elements
Symptoms:
• Text appears fuzzy or unclear
• Icons and buttons look pixelated
• Scaling issues on high-DPI displays

Root Cause: DPI scaling configuration
Resolution Steps:
1. Configure DPI scaling:
   export GDK_SCALE=1.5  # For 150% scaling
   export GDK_DPI_SCALE=1.0
   
2. For tkinter-specific scaling:
   python3 src/bus_matrix_gui.py --dpi-scale 1.5
   
3. System display settings:
   # GNOME
   gsettings set org.gnome.desktop.interface scaling-factor 2
   
   # KDE
   # System Settings → Display → Scale Display

Issue: GUI elements overlapping or misaligned
Symptoms:
• Buttons extending beyond panels
• Text overlapping with other elements
• Layout appears corrupted

Diagnostic Steps:
1. Check window size:
   xwininfo  # Click on application window
   
2. Check font configuration:
   fc-list | grep -i sans
   
Resolution Steps:
1. Reset window geometry:
   rm ~/.config/bus_matrix_tool/geometry.conf
   
2. Force minimum window size:
   python3 src/bus_matrix_gui.py --min-size 1280x720
   
3. Update font cache:
   fc-cache -f -v

PERFORMANCE AND RESPONSIVENESS ISSUES:

Issue: GUI becomes unresponsive during operations
Symptoms:
• Application freezes during RTL generation
• Cannot cancel long-running operations
• Interface stops updating

Root Cause: Blocking operations on main thread
Diagnostic Steps:
1. Check CPU usage:
   top -p $(pgrep -f bus_matrix_gui)
   
2. Check memory usage:
   ps -p $(pgrep -f bus_matrix_gui) -o pid,vsz,rss,%mem
   
Resolution Steps:
1. Enable progress reporting:
   python3 src/bus_matrix_gui.py --enable-progress
   
2. Reduce operation scope:
   # Generate smaller configurations first
   # Increase complexity gradually
   
3. Use batch mode for large designs:
   python3 src/bus_matrix_gui.py --batch --config large_design.json

Issue: High memory usage
Symptoms:
• System becomes slow when tool is running
• Out of memory errors
• Application crashes unexpectedly

Diagnostic Steps:
1. Monitor memory usage:
   watch -n 1 'ps -p $(pgrep -f bus_matrix_gui) -o pid,vsz,rss,%mem'
   
2. Check for memory leaks:
   valgrind --tool=memcheck python3 src/bus_matrix_gui.py
   
Resolution Steps:
1. Limit concurrent operations:
   # Close unused project tabs
   # Generate one configuration at a time
   
2. Increase system swap:
   sudo swapon --show
   sudo fallocate -l 4G /swapfile
   sudo chmod 600 /swapfile
   sudo mkswap /swapfile
   sudo swapon /swapfile
   
3. Use 64-bit Python if available:
   python3 --version
   # Ensure using 64-bit Python

DATA AND FILE I/O ISSUES:

Issue: "Permission denied" when saving files
Symptoms:
• Cannot save project configurations
• Error writing output files
• Export operations fail

Root Cause: Insufficient file permissions
Resolution Steps:
1. Check directory permissions:
   ls -la
   mkdir -p ~/bus_matrix_projects
   chmod 755 ~/bus_matrix_projects
   
2. Change ownership if necessary:
   sudo chown $USER:$USER ~/bus_matrix_projects
   
3. Use alternate output directory:
   python3 src/bus_matrix_gui.py --output-dir /tmp/bus_matrix_output

Issue: Configuration file corruption
Symptoms:
• Project won't load
• Error messages about invalid JSON/XML
• Partial or missing configuration data

Diagnostic Steps:
1. Validate file format:
   python3 -m json.tool project.json  # For JSON files
   xmllint project.xml  # For XML files
   
2. Check file size and modification time:
   ls -la project.json
   
Resolution Steps:
1. Restore from backup:
   ls project.json.backup*
   cp project.json.backup.20231201_143000 project.json
   
2. Recover from auto-save:
   ls ~/.config/bus_matrix_tool/autosave/
   
3. Reconstruct from error messages:
   python3 src/bus_matrix_gui.py --repair-config project.json

LOGGING AND DEBUGGING:

Enable Debug Logging:
python3 src/bus_matrix_gui.py --log-level DEBUG --log-file debug.log

Common Debug Commands:
# Enable verbose output
python3 src/bus_matrix_gui.py --verbose

# Start with clean configuration
python3 src/bus_matrix_gui.py --reset-config

# Test mode with mock data
python3 src/bus_matrix_gui.py --test-mode

# Profile performance
python3 -m cProfile -o profile.stats src/bus_matrix_gui.py

Log File Analysis:
# Check for common error patterns
grep -E "(ERROR|FATAL|Exception)" ~/.config/bus_matrix_tool/application.log

# Monitor real-time logging
tail -f ~/.config/bus_matrix_tool/application.log

# Analyze performance bottlenecks
grep "PERF:" ~/.config/bus_matrix_tool/application.log

GUI Diagnostic Tool:
#!/usr/bin/env python3
# GUI diagnostic and repair tool
import tkinter as tk
import os
import sys

def run_diagnostics():
    results = []
    
    # Test tkinter
    try:
        root = tk.Tk()
        root.withdraw()  # Hide window
        results.append("✓ Tkinter working")
        root.destroy()
    except Exception as e:
        results.append(f"✗ Tkinter error: {e}")
    
    return results

if __name__ == "__main__":
    print("GUI Diagnostic Tool")
    print("=" * 20)
    
    for result in run_diagnostics():
        print(result)
"""
    pdf_generator.create_text_page(pdf, "7.2 GUI Application Issues", None, gui_issues, code_style=True)
    
    # Page 81: Design Configuration Issues
    design_config_issues = """
7.3 Design Configuration Issues

ADDRESS MAP CONFLICTS:

Issue: "Address overlap detected between slaves"
Symptoms:
• Red error indicators in GUI
• Address Map Viewer shows conflicts
• Validation fails before generation

Example Error Message:
"Slave 'peripheral_block' address range 0x40000000-0x4FFFFFFF overlaps 
with slave 'ddr_memory' address range 0x00000000-0x7FFFFFFF"

Root Cause Analysis:
1. Check slave address configurations:
   • DDR Memory: Base=0x00000000, Size=0x80000000 (2GB)
   • Peripheral: Base=0x40000000, Size=0x10000000 (256MB)
   • Overlap: 0x40000000-0x4FFFFFFF

Diagnostic Steps:
1. Open Address Map Viewer:
   Tools → Address Map Viewer
   
2. Examine address ranges:
   for slave in configuration['slaves']:
       base = int(slave['address_config']['base_address'], 16)
       size = int(slave['address_config']['size'], 16)
       end = base + size - 1
       print(f"{slave['name']}: 0x{base:08X}-0x{end:08X}")

Resolution Steps:
1. Non-overlapping layout:
   # Correct configuration
   DDR Memory:    0x00000000-0x3FFFFFFF (1GB)
   Peripherals:   0x40000000-0x4FFFFFFF (256MB)
   SRAM:          0x50000000-0x5FFFFFFF (256MB)
   
2. Address alignment validation:
   # Base address must be aligned to size
   base_address % size == 0
   
3. Use Address Space Calculator:
   python3 utils/address_calculator.py --layout check_layout.json

Issue: "Invalid address alignment"
Symptoms:
• Warning indicators for specific slaves
• Suboptimal performance warnings
• AXI compliance violations

Root Cause: Address not aligned to transfer size
Example:
• Base Address: 0x40000001 (not aligned)
• Transfer Size: 128 bytes
• Required Alignment: 128 bytes (0x80)

Resolution Steps:
1. Calculate proper alignment:
   aligned_base = (base_address // alignment) * alignment
   
2. Common alignment requirements:
   • 32-bit transfers: 4-byte alignment
   • 64-bit transfers: 8-byte alignment  
   • 128-bit transfers: 16-byte alignment
   • AXI burst transfers: 4KB alignment recommended
   
3. Use alignment calculator:
   python3 utils/alignment_helper.py --addr 0x40000001 --size 128

CONNECTIVITY AND ROUTING ISSUES:

Issue: "Master has no valid slave connections"
Symptoms:
• Red connection indicators
• Master appears isolated in connection matrix
• Generation fails with connectivity error

Diagnostic Steps:
1. Check Connection Matrix:
   View → Connection Matrix
   Look for empty rows (masters with no connections)
   
2. Verify address ranges:
   # Ensure master's target addresses fall within slave ranges
   master_access_range = [0x00000000, 0x7FFFFFFF]
   slave_ranges = get_slave_address_ranges()
   
Resolution Steps:
1. Add required connections:
   # In GUI: Drag from master output to slave input
   # In JSON: Add to connection matrix
   
2. Verify addressing:
   # Master must be able to reach intended slaves
   # Check that master's address range overlaps slave ranges
   
3. Add default slave connection:
   # Ensure all masters connect to default slave for unmapped addresses

Issue: "Circular dependency in interconnect topology"
Symptoms:
• Complex routing error messages
• Generation hangs or fails
• Unusual connection patterns

Root Cause: Bridged configurations with loops
Example:
Master → AXI2APB Bridge → APB Slave → APB2AXI Bridge → AXI Slave

Diagnostic Steps:
1. Trace signal paths:
   python3 utils/topology_analyzer.py --config design.json
   
2. Check for bridge connections:
   # Look for bridges connecting back to source protocol
   
Resolution Steps:
1. Eliminate cycles:
   # Remove redundant bridge connections
   # Use hierarchical topology instead
   
2. Redesign with clear hierarchy:
   AXI Domain: Masters → AXI Interconnect → Memory
   APB Domain: AXI2APB Bridge → APB Slaves

PROTOCOL COMPLIANCE ISSUES:

Issue: "Invalid burst configuration for AXI3"
Symptoms:
• Protocol compliance warnings
• Generation succeeds but RTL has issues
• Verification failures

Root Cause: Protocol-specific limitations
AXI3 Limitations:
• Maximum 16 transfers per burst (vs 256 for AXI4)
• Write interleaving required
• WID signal present

Diagnostic Steps:
1. Check protocol version:
   if config['global']['protocol'] == 'AXI3':
       check_axi3_compliance()
       
2. Validate burst parameters:
   max_burst_length = 16 if protocol == 'AXI3' else 256
   
Resolution Steps:
1. Adjust burst length limits:
   # For AXI3, ensure max_burst_length <= 16
   
2. Enable write interleaving:
   "protocol_features": {
       "write_interleave": true,
       "wid_support": true
   }

Issue: "QoS configuration invalid for selected protocol"
Symptoms:
• QoS-related warnings
• Advanced features disabled
• Suboptimal arbitration

Root Cause: Protocol doesn't support QoS
• AXI3: No QoS support
• AHB: No QoS support  
• APB: No QoS support
• AXI4: Full QoS support

Resolution Steps:
1. Disable QoS for non-supporting protocols:
   if protocol != 'AXI4':
       config['advanced_features']['qos']['enabled'] = false
       
2. Use alternative arbitration:
   # For non-AXI4: Use round-robin or priority arbitration

RESOURCE CONSTRAINT VIOLATIONS:

Issue: "Configuration exceeds target device capacity"
Symptoms:
• Resource utilization warnings
• Area estimates too high
• Implementation may not fit

Example Resource Report:
Estimated Resources:
• Logic Cells: 45,000 (Target: 40,000) ❌
• Memory Bits: 2,048,000 (Target: 1,500,000) ❌  
• DSP Blocks: 0 (Target: 100) ✓
• I/O Pins: 512 (Target: 400) ❌

Diagnostic Steps:
1. Generate resource estimate:
   python3 src/bus_matrix_gui.py --estimate-resources config.json
   
2. Analyze resource usage by component:
   Component Resource Breakdown:
   • Address Decoders: 15,000 logic cells
   • Arbiters: 12,000 logic cells
   • Data Path: 18,000 logic cells
   
Resolution Steps:
1. Reduce complexity:
   • Decrease number of masters/slaves
   • Reduce data width (512 → 256 → 128)
   • Minimize pipeline depth
   • Disable unused features
   
2. Optimize for area:
   "interconnect": {
       "performance": {
           "optimization_target": "area"
       }
   }
   
3. Use hierarchical design:
   # Split large interconnect into multiple smaller ones

CONFIGURATION VALIDATION SCRIPT:

# Example Python script for configuration validation
#!/usr/bin/env python3
import json
import sys

def validate_address_map(config):
    # Validate address map for overlaps and alignment
    slaves = config.get('slaves', [])
    ranges = []
    
    for slave in slaves:
        addr_config = slave.get('address_config', {})
        base = int(addr_config.get('base_address', '0'), 16)
        size = int(addr_config.get('size', '0'), 16)
        end = base + size - 1
        
        # Check alignment
        if base % size != 0:
            print(f"WARNING: Base address not aligned")
        
        # Check for overlaps
        for existing_range in ranges:
            if not (end < existing_range[0] or base > existing_range[1]):
                print(f"ERROR: Address overlap detected")
                return False
        
        ranges.append((base, end))
    
    return True

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 validate_config.py <config_file>")
        sys.exit(1)
    
    with open(sys.argv[1], 'r') as f:
        config = json.load(f)
    
    print("Validating configuration...")
    
    valid = validate_address_map(config)
    
    if valid:
        print("✅ Configuration validation passed")
    else:
        print("❌ Configuration validation failed")
        sys.exit(1)

# Usage: python3 validate_config.py design.json
"""
    pdf_generator.create_text_page(pdf, "7.3 Design Configuration Issues", None, design_config_issues, code_style=True)
    
    # Page 82: RTL Generation Issues
    rtl_generation_issues = """
7.4 RTL Generation Issues

GENERATION PROCESS FAILURES:

Issue: RTL generation starts but never completes
Symptoms:
• Progress bar stops at specific percentage
• Process appears hung
• No error messages displayed
• Output directory remains empty or partial

Diagnostic Steps:
1. Check process status:
   ps aux | grep bus_matrix_gui
   ps aux | grep python
   
2. Monitor resource usage:
   top -p $(pgrep -f bus_matrix_gui)
   
3. Check temporary files:
   ls -la /tmp/bus_matrix_*
   
4. Enable verbose logging:
   python3 src/bus_matrix_gui.py --log-level DEBUG --log-file generation.log

Common Causes and Resolutions:
1. Insufficient memory:
   • Reduce design complexity
   • Close other applications
   • Add more RAM or swap space
   
2. Disk space exhaustion:
   df -h .
   # Clean up space or change output directory
   
3. Infinite loop in generation logic:
   • Kill process: kill -9 $(pgrep -f bus_matrix_gui)
   • Restart with simpler configuration
   • Report bug with configuration file

Issue: "Internal generation error: template not found"
Symptoms:
• Generation fails immediately
• Error mentions missing templates
• Specific RTL modules not generated

Root Cause: Missing or corrupted template files
Diagnostic Steps:
1. Check template directory:
   ls -la templates/
   ls -la templates/rtl/
   
2. Verify template integrity:
   find templates/ -name "*.template" -size 0  # Find empty templates
   
Resolution Steps:
1. Restore templates from backup:
   git checkout templates/  # If using git
   
2. Reinstall tool:
   # Download fresh copy
   # Verify checksum if available
   
3. Custom template path:
   python3 src/bus_matrix_gui.py --template-path /path/to/templates

Issue: "Generation succeeded but output files are invalid"
Symptoms:
• Files generated but contain errors
• Verilog syntax errors
• Missing module declarations
• Incorrect parameter values

Diagnostic Steps:
1. Check file sizes:
   ls -la output_rtl/rtl/
   # Files should be reasonable size (not 0 bytes)
   
2. Quick syntax check:
   iverilog -t null output_rtl/rtl/*.v
   
3. Check for placeholders:
   grep -r "TEMPLATE_" output_rtl/
   grep -r "TODO" output_rtl/
   
Resolution Steps:
1. Regenerate with validation:
   python3 src/bus_matrix_gui.py --validate-output --config design.json
   
2. Check configuration parameters:
   # Verify all required parameters are set
   # No undefined or null values

SYNTHESIS AND TIMING ISSUES:

Issue: Generated RTL fails synthesis
Symptoms:
• Synthesis tool reports errors
• Unsupported constructs
• Undefined modules or signals

Common Synthesis Errors:
1. "Module 'axi4_fifo' not found"
   Resolution:
   • Check that all generated files are included
   • Verify file list completeness
   • Add missing utility modules
   
2. "Unsupported SystemVerilog construct"
   Resolution:
   • Use Verilog-2001 generation mode:
     python3 src/bus_matrix_gui.py --target-language verilog
   
3. "Parameter WIDTH is not constant"
   Resolution:
   • Check parameter definitions
   • Verify localparam usage
   • May need tool-specific workarounds

Issue: Timing closure failures
Symptoms:
• Setup timing violations
• Hold timing violations
• Clock skew issues

Diagnostic Steps:
1. Check critical paths:
   # In synthesis tool, analyze timing
   report_timing -max_paths 10
   
2. Identify bottlenecks:
   # Look for long combinational paths
   # Check for high-fanout nets
   
Resolution Steps:
1. Increase pipeline depth:
   "interconnect": {
       "pipeline": {
           "address_stages": 3,  # Increase from 2
           "data_stages": 2      # Increase from 1
       }
   }
   
2. Enable register slicing:
   "interconnect": {
       "pipeline": {
           "register_slicing": true
       }
   }
   
3. Optimize for timing:
   "interconnect": {
       "performance": {
           "optimization_target": "speed"
       }
   }

FUNCTIONAL VERIFICATION FAILURES:

Issue: Generated testbench compilation errors
Symptoms:
• UVM compilation failures
• Missing package dependencies
• Syntax errors in testbench

Common Compilation Errors:
1. "Package uvm_pkg not found"
   Resolution:
   export UVM_HOME=/path/to/uvm-1.2
   vcs -ntb_opts uvm-1.2 +incdir+$UVM_HOME/src $UVM_HOME/src/uvm.sv
   
2. "Interface not found"
   Resolution:
   # Ensure interface files are compiled first
   # Check compilation order in Makefile
   
3. "Undefined macro"
   Resolution:
   # Check that all required defines are included
   +define+UVM_NO_DPI +define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR

Issue: Simulation runtime failures
Symptoms:
• Simulation crashes
• Protocol violations detected
• Incorrect behavior observed

Diagnostic Steps:
1. Run basic connectivity test:
   make simulate TEST=axi4_sanity_test WAVES=on
   
2. Check for assertion failures:
   grep "ASSERTION" simulation.log
   grep "UVM_ERROR" simulation.log
   
3. Analyze waveforms:
   gtkwave simulation.vcd
   # Look for protocol violations, timing issues
   
Resolution Steps:
1. Enable protocol checking:
   +define+ENABLE_PROTOCOL_ASSERTIONS
   
2. Reduce test complexity:
   # Start with single transactions
   # Gradually increase complexity
   
3. Check interconnect configuration:
   # Verify address maps match testbench expectations
   # Check ID width consistency

INTEGRATION AND COMPATIBILITY ISSUES:

Issue: Generated RTL incompatible with existing design
Symptoms:
• Interface mismatches
• Clock domain issues
• Reset scheme conflicts

Diagnostic Steps:
1. Compare interfaces:
   # Check signal names and widths
   # Verify protocol compliance
   
2. Check clock requirements:
   # Single clock vs. multi-clock
   # Clock relationships
   
Resolution Steps:
1. Generate wrapper interfaces:
   python3 src/bus_matrix_gui.py --generate-wrappers --config design.json
   
2. Customize signal names:
   "generation_options": {
       "signal_prefix": "my_axi_",
       "clock_name": "custom_clk",
       "reset_name": "custom_rst_n"
   }

Issue: Performance doesn't meet requirements
Symptoms:
• Lower bandwidth than expected
• Higher latency than specified
• Throughput bottlenecks

Diagnostic Steps:
1. Generate performance report:
   python3 utils/performance_analyzer.py --config design.json
   
2. Run performance tests:
   make simulate TEST=axi4_performance_test
   
Resolution Steps:
1. Optimize configuration:
   # Increase outstanding transaction limits
   # Reduce pipeline depth for latency
   # Increase data width for bandwidth
   
2. Adjust arbitration:
   "interconnect": {
       "arbitration": {
           "algorithm": "qos_aware"  # For real-time requirements
       }
   }

RTL VALIDATION SCRIPT:

#!/usr/bin/env python3
# RTL output validation script
import os
import subprocess
import glob

def check_verilog_syntax(rtl_dir):
    # Check Verilog syntax using iverilog
    verilog_files = []
    for root, dirs, files in os.walk(rtl_dir):
        for file in files:
            if file.endswith('.v') or file.endswith('.sv'):
                verilog_files.append(os.path.join(root, file))
    
    if not verilog_files:
        print("❌ No Verilog files found")
        return False
    
    try:
        # Check syntax without generating output
        result = subprocess.run(['iverilog', '-t', 'null'] + verilog_files, 
                              capture_output=True, text=True)
        
        if result.returncode == 0:
            print(f"✅ Syntax check passed for {len(verilog_files)} files")
            return True
        else:
            print(f"❌ Syntax errors found")
            return False
            
    except FileNotFoundError:
        print("⚠ iverilog not found - skipping syntax check")
        return True

def main():
    rtl_dir = "output_rtl"
    if not os.path.exists(rtl_dir):
        print(f"❌ RTL directory {rtl_dir} not found")
        return
    
    print("Validating RTL output...")
    valid = check_verilog_syntax(rtl_dir)
    
    if valid:
        print("✅ RTL validation passed")
    else:
        print("❌ RTL validation failed")

# Usage: python3 validate_rtl.py
"""
    pdf_generator.create_text_page(pdf, "7.4 RTL Generation Issues", None, rtl_generation_issues, code_style=True)
    
    # Continue with remaining troubleshooting pages (83-84)...
    for page_num in range(83, 85):
        title_map = {
            83: "7.5 VIP Generation Issues",
            84: "7.6 System Integration Issues"
        }
        
        if page_num == 83:
            content = """
VIP GENERATION AND COMPILATION ISSUES:

Issue: UVM environment compilation fails
Symptoms:
• "Package uvm_pkg not found"
• SystemVerilog compilation errors
• Missing interface definitions

Root Cause: UVM library not properly configured
Resolution Steps:
1. Set UVM environment:
   export UVM_HOME=/tools/uvm-1.2
   export UVM_VERSION=1.2

2. Check UVM installation:
   ls $UVM_HOME/src/uvm.sv
   ls $UVM_HOME/src/uvm_pkg.sv

3. Compile with proper UVM flags:
   vcs -ntb_opts uvm-1.2 +incdir+$UVM_HOME/src $UVM_HOME/src/uvm.sv

Issue: "Class 'axi4_transaction' not found"
Symptoms:
• UVM class hierarchy errors
• Factory registration failures
• Compilation errors in generated tests

Resolution Steps:
1. Check package compilation order:
   // Compile base packages first
   axi4_pkg.sv
   axi4_test_pkg.sv
   
2. Verify factory registration:
   `uvm_component_utils(axi4_master_agent)
   `uvm_object_utils(axi4_transaction)

TESTBENCH RUNTIME ISSUES:

Issue: Simulation hangs during test execution
Symptoms:
• Test starts but never completes
• No UVM phase transitions
• Timeout without error messages

Diagnostic Steps:
1. Enable UVM phase tracing:
   +UVM_PHASE_TRACE

2. Check objection handling:
   +UVM_OBJECTION_TRACE

3. Monitor simulation activity:
   # Check if clocks are running
   # Verify reset is released

Resolution Steps:
1. Add simulation timeout:
   initial begin
     #100ms;
     `uvm_fatal("TIMEOUT", "Simulation timeout")
   end

2. Check phase implementation:
   // Ensure raise/drop objection pairs match
   phase.raise_objection(this);
   // ... test code ...
   phase.drop_objection(this);

Issue: Protocol violations detected
Symptoms:  
• UVM_ERROR messages about protocol compliance
• Assertion failures
• Incorrect transaction behavior

Common Protocol Violations:
1. VALID/READY handshake violations
2. Address/data relationship errors
3. Burst boundary crossing
4. ID-based ordering violations

Resolution:
1. Enable protocol assertions:
   +define+ENABLE_AXI4_ASSERTIONS

2. Check sequence constraints:
   constraint addr_align_c {
     addr % (1 << size) == 0;
   }

3. Review generated sequences for compliance
"""
        elif page_num == 84:
            content = """
TOOL INTEGRATION ISSUES:

Issue: Version compatibility between tools
Symptoms:
• Generated RTL doesn't work with target tool
• Synthesis warnings about unsupported features
• Simulation compatibility issues

Resolution Steps:
1. Check tool version compatibility:
   Tool        | Supported Versions
   VCS         | 2020.03 - 2023.09
   Questa      | 2021.1 - 2023.4
   Vivado      | 2020.2 - 2023.2
   Quartus     | 20.1 - 23.3

2. Use tool-specific options:
   --target-tool vivado
   --target-tool questa
   --target-tool vcs

Issue: File format incompatibilities
Symptoms:
• Cannot import/export configurations
• Integration scripts fail
• Version control issues

Resolution:
1. Use standard formats:
   # Export to industry standard formats
   python3 src/bus_matrix_gui.py --export-ip-xact config.json
   python3 src/bus_matrix_gui.py --export-json config.bmcfg

2. Enable format conversion:
   # Convert between formats
   python3 utils/format_converter.py --input config.xml --output config.json

PERFORMANCE AND SCALABILITY ISSUES:

Issue: Tool becomes slow with large designs
Symptoms:
• GUI responsiveness degrades
• Long generation times
• Memory usage grows excessively

Resolution:
1. Use batch mode for large designs:
   python3 src/bus_matrix_gui.py --batch --config large_design.json

2. Enable incremental generation:
   --incremental-rtl
   --cache-intermediates

3. Optimize configuration:
   # Reduce unnecessary features
   # Use hierarchical designs
   # Split into multiple interconnects

MULTI-USER AND REVISION CONTROL:

Issue: Configuration conflicts in team environment
Symptoms:
• Merge conflicts in configuration files
• Inconsistent generation results
• Version synchronization issues

Resolution:
1. Use configuration management:
   git add *.json *.bmcfg
   git commit -m "Update bus configuration"

2. Enable configuration comparison:
   python3 utils/config_diff.py config_v1.json config_v2.json

3. Use configuration templates:
   # Base template for team
   # Project-specific customizations
   python3 src/bus_matrix_gui.py --template base_config.json
"""
        else:
            content = f"""
This page contains detailed information about {title_map[page_num].split('.')[1].strip()}.

Content includes:
• Comprehensive troubleshooting procedures
• Step-by-step resolution guidance
• Common error patterns and solutions
• Diagnostic tools and techniques
• Prevention strategies and best practices

This section provides complete coverage of issues that may arise during
the use of the AMBA Bus Matrix Configuration Tool, ensuring users can
quickly identify and resolve problems.
"""
        
        pdf_generator.create_text_page(pdf, title_map[page_num], None, content, code_style=(page_num in [83, 84]))

# This function can be integrated into the main PDF generator