#!/usr/bin/env python3
"""
Capture real GUI screenshots using gnome-screenshot
This will launch the GUI and attempt to capture actual screenshots
"""

import subprocess
import time
import os
import signal
import sys

class RealScreenshotCapture:
    """Capture real screenshots from the running GUI"""
    
    def __init__(self):
        self.gui_process = None
        self.screenshots_captured = []
        
    def launch_gui(self):
        """Launch the GUI application"""
        print("🚀 Launching AMBA Bus Matrix Configuration GUI...")
        
        try:
            self.gui_process = subprocess.Popen([
                'python3', 'src/bus_matrix_gui.py'
            ], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            
            print(f"✅ GUI launched with PID: {self.gui_process.pid}")
            
            # Wait for GUI to initialize
            print("⏳ Waiting for GUI to initialize...")
            time.sleep(5)
            
            # Check if process is still running
            if self.gui_process.poll() is None:
                print("✅ GUI process is running and ready")
                return True
            else:
                print("❌ GUI process exited immediately")
                stdout, stderr = self.gui_process.communicate()
                print(f"STDOUT: {stdout.decode()}")
                print(f"STDERR: {stderr.decode()}")
                return False
                
        except Exception as e:
            print(f"❌ Failed to launch GUI: {e}")
            return False
    
    def capture_screenshot(self, filename, description, delay=2):
        """Capture a screenshot with gnome-screenshot"""
        print(f"\n📸 Capturing: {description}")
        print(f"   Filename: {filename}")
        print(f"   Delay: {delay} seconds")
        
        try:
            # Use gnome-screenshot to capture full screen
            result = subprocess.run([
                'gnome-screenshot',
                '--file', filename,
                '--delay', str(delay)
            ], capture_output=True, text=True, timeout=30)
            
            if result.returncode == 0:
                if os.path.exists(filename):
                    file_size = os.path.getsize(filename)
                    print(f"✅ Screenshot captured successfully ({file_size} bytes)")
                    self.screenshots_captured.append((filename, description, file_size))
                    return True
                else:
                    print("❌ Screenshot command succeeded but file not found")
            else:
                print(f"❌ Screenshot failed: {result.stderr}")
                
        except subprocess.TimeoutExpired:
            print("⏰ Screenshot capture timed out")
        except Exception as e:
            print(f"❌ Screenshot error: {e}")
            
        return False
    
    def capture_window_screenshot(self, filename, description, delay=2):
        """Capture a window screenshot"""
        print(f"\n🪟 Capturing window: {description}")
        print(f"   Filename: {filename}")
        print(f"   Delay: {delay} seconds")
        
        try:
            # Use gnome-screenshot to capture active window
            result = subprocess.run([
                'gnome-screenshot',
                '--window',
                '--file', filename,
                '--delay', str(delay)
            ], capture_output=True, text=True, timeout=30)
            
            if result.returncode == 0:
                if os.path.exists(filename):
                    file_size = os.path.getsize(filename)
                    print(f"✅ Window screenshot captured ({file_size} bytes)")
                    self.screenshots_captured.append((filename, description, file_size))
                    return True
                else:
                    print("❌ Window screenshot command succeeded but file not found")
            else:
                print(f"❌ Window screenshot failed: {result.stderr}")
                
        except subprocess.TimeoutExpired:
            print("⏰ Window screenshot capture timed out")
        except Exception as e:
            print(f"❌ Window screenshot error: {e}")
            
        return False
    
    def cleanup_gui(self):
        """Clean up the GUI process"""
        if self.gui_process and self.gui_process.poll() is None:
            print("\n🧹 Cleaning up GUI process...")
            try:
                self.gui_process.terminate()
                self.gui_process.wait(timeout=5)
                print("✅ GUI process terminated cleanly")
            except subprocess.TimeoutExpired:
                print("⚠️  GUI process didn't terminate, killing...")
                self.gui_process.kill()
                self.gui_process.wait()
                print("✅ GUI process killed")
            except Exception as e:
                print(f"⚠️  Error cleaning up GUI: {e}")
    
    def capture_all_screenshots(self):
        """Capture all required screenshots"""
        print("=" * 60)
        print("🎯 REAL GUI SCREENSHOT CAPTURE SESSION")
        print("=" * 60)
        
        # Launch GUI
        if not self.launch_gui():
            return False
        
        try:
            # Screenshot 1: Main window after launch
            success1 = self.capture_screenshot(
                'real_gui_main_window.png',
                'Main GUI window after launch',
                delay=3
            )
            
            # Give user time to interact if needed
            print("\n⏳ Pausing to allow GUI interaction...")
            time.sleep(2)
            
            # Screenshot 2: Full screen with any dialogs
            success2 = self.capture_screenshot(
                'real_gui_fullscreen.png', 
                'Full screen view of GUI',
                delay=2
            )
            
            # Screenshot 3: Window-specific capture
            success3 = self.capture_window_screenshot(
                'real_gui_window_focus.png',
                'Focused GUI window',
                delay=2
            )
            
            # Additional captures with different delays
            print("\n🔄 Taking additional captures...")
            
            success4 = self.capture_screenshot(
                'real_gui_state2.png',
                'GUI state after initialization',
                delay=1
            )
            
            success5 = self.capture_screenshot(
                'real_gui_final.png',
                'Final GUI state',
                delay=1
            )
            
            return any([success1, success2, success3, success4, success5])
            
        finally:
            self.cleanup_gui()
    
    def generate_report(self):
        """Generate a report of captured screenshots"""
        report = f"""# Real GUI Screenshot Capture Report

## Session Summary
- GUI Launch: {'✅ Successful' if self.gui_process else '❌ Failed'}
- Screenshots Attempted: 5
- Screenshots Captured: {len(self.screenshots_captured)}

## Captured Screenshots
"""
        
        if self.screenshots_captured:
            for filename, description, size in self.screenshots_captured:
                report += f"- ✅ **{filename}**: {description} ({size:,} bytes)\n"
        else:
            report += "- ❌ No screenshots were successfully captured\n"
            
        report += f"""

## Environment Details
- DISPLAY: {os.environ.get('DISPLAY', 'Not set')}
- Screenshot tool: gnome-screenshot
- Current directory: {os.getcwd()}
- GUI source: src/bus_matrix_gui.py

## Next Steps
"""
        
        if self.screenshots_captured:
            report += """1. ✅ Real screenshots captured successfully
2. Review captured images for quality
3. Replace mockup images in PDFs with real screenshots
4. Regenerate documentation with authentic images
5. Update visual guides with real GUI demonstrations"""
        else:
            report += """1. ❌ Screenshot capture failed
2. Check GUI environment and display settings
3. Verify gnome-screenshot works manually
4. Consider alternative screenshot methods
5. Document limitation in user guides"""
        
        return report

def main():
    """Main function"""
    # Check prerequisites
    if not os.environ.get('DISPLAY'):
        print("❌ No DISPLAY environment variable set")
        print("   Cannot capture screenshots without GUI display")
        return False
    
    if not os.path.exists('src/bus_matrix_gui.py'):
        print("❌ GUI application not found: src/bus_matrix_gui.py")
        return False
    
    # Check for gnome-screenshot
    try:
        subprocess.run(['gnome-screenshot', '--version'], 
                      capture_output=True, timeout=5)
    except:
        print("❌ gnome-screenshot not available")
        print("   Install with: sudo yum install gnome-screenshot")
        return False
    
    print("✅ Prerequisites check passed")
    
    # Create capture instance and run
    capturer = RealScreenshotCapture()
    
    try:
        success = capturer.capture_all_screenshots()
        
        # Generate and save report
        report = capturer.generate_report()
        with open('real_screenshot_report.md', 'w') as f:
            f.write(report)
        
        print(f"\n📋 Report saved: real_screenshot_report.md")
        
        if success:
            print("\n🎉 SUCCESS: Real screenshots captured!")
            print("📂 Check the following files:")
            for filename, description, size in capturer.screenshots_captured:
                print(f"   - {filename}: {description}")
        else:
            print("\n❌ FAILED: No screenshots were captured")
            print("💡 Check the report for troubleshooting steps")
        
        return success
        
    except KeyboardInterrupt:
        print("\n⚠️  Capture interrupted by user")
        capturer.cleanup_gui()
        return False
    except Exception as e:
        print(f"\n❌ Unexpected error: {e}")
        capturer.cleanup_gui()
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)