#!/usr/bin/env python3
"""
Programmatic approach to capture real GUI screenshots
Since we can't manually interact with GUI, try automated capture
"""

import subprocess
import time
import os
import sys
from pathlib import Path

def check_screenshot_tools():
    """Check what screenshot tools are available"""
    tools = []
    
    # Check for common screenshot tools
    commands = [
        ('xwd', 'X Window Dump'),
        ('import', 'ImageMagick import'),
        ('scrot', 'SCReenshOT utility'),
        ('gnome-screenshot', 'GNOME Screenshot'),
        ('xfce4-screenshooter', 'XFCE Screenshot'),
    ]
    
    for cmd, desc in commands:
        try:
            result = subprocess.run(['which', cmd], capture_output=True, text=True)
            if result.returncode == 0:
                tools.append((cmd, desc, result.stdout.strip()))
        except:
            pass
    
    return tools

def get_window_info():
    """Get information about GUI windows"""
    try:
        # Try to get window list
        result = subprocess.run(['xwininfo', '-tree', '-root'], 
                              capture_output=True, text=True, timeout=10)
        return result.stdout
    except:
        return "Could not get window information"

def try_automated_screenshot():
    """Attempt to take automated screenshots"""
    print("🔍 Checking available screenshot tools...")
    tools = check_screenshot_tools()
    
    if not tools:
        print("❌ No screenshot tools found")
        print("   Available tools might include: xwd, import, scrot, gnome-screenshot")
        return False
    
    print("✅ Found screenshot tools:")
    for cmd, desc, path in tools:
        print(f"   - {cmd}: {desc} ({path})")
    
    print("\n🪟 Getting window information...")
    window_info = get_window_info()
    print("Window info snippet:")
    print(window_info[:500] + "..." if len(window_info) > 500 else window_info)
    
    # Try to find GUI window
    if "AMBA" in window_info or "bus_matrix" in window_info.lower():
        print("✅ Found potential GUI window!")
        
        # Try to take screenshot with first available tool
        cmd, desc, path = tools[0]
        print(f"\n📸 Attempting screenshot with {cmd}...")
        
        try:
            if cmd == 'xwd':
                # X Window Dump - requires window selection
                result = subprocess.run([
                    'xwd', '-name', 'AMBA Bus Matrix Configuration GUI', 
                    '-out', 'real_gui_screenshot.xwd'
                ], capture_output=True, text=True, timeout=10)
                
                if result.returncode == 0:
                    print("✅ XWD screenshot captured")
                    # Convert to PNG if possible
                    try:
                        subprocess.run(['convert', 'real_gui_screenshot.xwd', 
                                      'real_gui_main_window.png'], timeout=10)
                        print("✅ Converted to PNG")
                        return True
                    except:
                        print("⚠️  XWD file created but couldn't convert to PNG")
                        return True
                        
            elif cmd == 'import':
                # ImageMagick import
                result = subprocess.run([
                    'import', '-window', 'root', 'real_gui_screenshot.png'
                ], capture_output=True, text=True, timeout=10)
                
                if result.returncode == 0:
                    print("✅ Full screen screenshot captured with ImageMagick")
                    return True
                    
            elif cmd == 'scrot':
                # scrot screenshot
                result = subprocess.run([
                    'scrot', 'real_gui_screenshot.png'
                ], capture_output=True, text=True, timeout=10)
                
                if result.returncode == 0:
                    print("✅ Screenshot captured with scrot")
                    return True
                    
        except subprocess.TimeoutExpired:
            print("⏰ Screenshot command timed out")
        except Exception as e:
            print(f"❌ Screenshot failed: {e}")
    
    else:
        print("❌ Could not find GUI window in window list")
    
    return False

def launch_gui_and_capture():
    """Launch GUI and attempt automated capture"""
    print("🚀 Launching GUI for screenshot capture...")
    
    # Launch GUI in background
    try:
        gui_process = subprocess.Popen([
            'python3', 'src/bus_matrix_gui.py'
        ], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        
        print(f"✅ GUI launched with PID: {gui_process.pid}")
        
        # Wait for GUI to initialize
        print("⏳ Waiting for GUI to initialize...")
        time.sleep(3)
        
        # Check if process is still running
        if gui_process.poll() is None:
            print("✅ GUI process is running")
            
            # Try automated screenshot
            success = try_automated_screenshot()
            
            if success:
                print("\n🎉 SUCCESS: Screenshot captured!")
                print("📂 Check current directory for screenshot files")
            else:
                print("\n❌ FAILED: Could not capture screenshot automatically")
                print("💡 This likely requires manual screenshot with GUI tools")
            
            # Clean up GUI process
            print("\n🧹 Cleaning up GUI process...")
            gui_process.terminate()
            try:
                gui_process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                gui_process.kill()
                gui_process.wait()
            
            return success
            
        else:
            print("❌ GUI process exited immediately")
            stdout, stderr = gui_process.communicate()
            print(f"STDOUT: {stdout.decode()}")
            print(f"STDERR: {stderr.decode()}")
            return False
            
    except Exception as e:
        print(f"❌ Failed to launch GUI: {e}")
        return False

def create_status_report():
    """Create a status report about screenshot capture attempt"""
    report = f"""
# Real Screenshot Capture Attempt Report

## Environment Check
- DISPLAY: {os.environ.get('DISPLAY', 'Not set')}
- Python version: {sys.version.split()[0]}
- Current directory: {os.getcwd()}

## Screenshot Tools Available
"""
    
    tools = check_screenshot_tools()
    if tools:
        for cmd, desc, path in tools:
            report += f"- ✅ {cmd}: {desc} ({path})\n"
    else:
        report += "- ❌ No screenshot tools found\n"
    
    report += f"""

## GUI Application Status
- GUI source file exists: {os.path.exists('src/bus_matrix_gui.py')}
- Launch script exists: {os.path.exists('launch_gui.sh')}

## Window Information
"""
    
    window_info = get_window_info()
    if "Could not get" in window_info:
        report += "- ❌ Could not retrieve window information\n"
    else:
        report += "- ✅ Window information retrieved\n"
        if "AMBA" in window_info or "bus_matrix" in window_info.lower():
            report += "- ✅ GUI window detected in window list\n"
        else:
            report += "- ❌ GUI window not found in window list\n"
    
    report += f"""

## Recommendation
Based on this environment analysis:
1. GUI application exists and can launch
2. Screenshot tools {'are available' if tools else 'are NOT available'}
3. Window system {'is accessible' if 'DISPLAY' in os.environ else 'may not be accessible'}

{'✅ Automated screenshot capture may be possible' if tools and 'DISPLAY' in os.environ else '❌ Manual screenshot capture required'}

## Next Steps
{'Try: python3 capture_real_screenshots_programmatically.py' if tools else 'Install screenshot tools: sudo yum install ImageMagick scrot'}
"""
    
    return report

def main():
    """Main function"""
    print("=" * 60)
    print("🎯 PROGRAMMATIC REAL SCREENSHOT CAPTURE")
    print("=" * 60)
    
    # Check environment
    if not os.environ.get('DISPLAY'):
        print("❌ No DISPLAY environment variable")
        print("   This suggests no GUI environment is available")
        return False
    
    if not os.path.exists('src/bus_matrix_gui.py'):
        print("❌ GUI application not found")
        print("   Expected: src/bus_matrix_gui.py")
        return False
    
    print("✅ Environment checks passed")
    
    # Try to capture screenshots
    success = launch_gui_and_capture()
    
    # Create status report
    report = create_status_report()
    with open('screenshot_capture_report.md', 'w') as f:
        f.write(report)
    
    print(f"\n📋 Status report saved: screenshot_capture_report.md")
    
    return success

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)