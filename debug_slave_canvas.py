#!/usr/bin/env python3

"""
DEBUG SLAVE CANVAS ISSUE
Comprehensive debugging for slave not appearing on canvas

This script adds extensive debugging to understand why slaves
aren't appearing on the canvas after configuration.
"""

import os
import sys
import tkinter as tk

# Add src directory to path
current_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(current_dir, 'axi4_vip', 'gui', 'src')
sys.path.insert(0, src_dir)

from bus_config import Slave, BusConfig
from bus_matrix_gui import BusMatrixGUI, BusMatrixCanvas

def monkey_patch_add_slave():
    """Add extra debugging to canvas add_slave method"""
    
    original_add_slave = BusMatrixCanvas.add_slave
    
    def debug_add_slave(self, config, x=450, y=50):
        print("\n" + "="*60)
        print("🔍 DEBUG: Canvas add_slave called")
        print(f"  Config: {config.name}")
        print(f"  Position: x={x}, y={y}")
        print(f"  Canvas zoom level: {self.zoom_level}")
        print(f"  Canvas slaves before: {len(self.slaves)}")
        print(f"  Canvas bounds: {self.winfo_width()}x{self.winfo_height()}")
        print(f"  Canvas scroll region: {self.cget('scrollregion')}")
        
        # Check if canvas is visible
        print(f"  Canvas visible: {self.winfo_viewable()}")
        print(f"  Canvas mapped: {self.winfo_ismapped()}")
        
        # Call original method
        result = original_add_slave(self, config, x, y)
        
        print(f"  Canvas slaves after: {len(self.slaves)}")
        print(f"  Created slave ID: {result}")
        
        # Check the created items
        if self.slaves:
            last_slave = self.slaves[-1]
            print(f"  Last slave data: {last_slave}")
            
            # Check if the rectangle is visible
            coords = self.coords(last_slave['id'])
            print(f"  Rectangle coords: {coords}")
            
            # Check if it's within the visible area
            visible_x1 = self.canvasx(0)
            visible_y1 = self.canvasy(0) 
            visible_x2 = self.canvasx(self.winfo_width())
            visible_y2 = self.canvasy(self.winfo_height())
            print(f"  Visible area: ({visible_x1}, {visible_y1}) to ({visible_x2}, {visible_y2})")
            
            if coords:
                x1, y1, x2, y2 = coords
                is_visible = (x1 <= visible_x2 and x2 >= visible_x1 and 
                             y1 <= visible_y2 and y2 >= visible_y1)
                print(f"  Is visible in current view: {is_visible}")
                
                if not is_visible:
                    print("  ⚠️  WARNING: Slave is outside visible area!")
                    print(f"  Try scrolling to: x={x1}, y={y1}")
        
        # Check all canvas items
        all_items = self.find_all()
        print(f"  Total canvas items: {len(all_items)}")
        
        print("="*60 + "\n")
        
        return result
    
    BusMatrixCanvas.add_slave = debug_add_slave

def monkey_patch_gui_add_slave():
    """Add debugging to GUI add_slave method"""
    
    original_method = BusMatrixGUI.add_slave
    
    def debug_gui_add_slave(self):
        print("\n🎯 DEBUG: GUI add_slave called")
        print(f"  Current slaves in config: {len(self.current_config.slaves)}")
        print(f"  Current slaves on canvas: {len(self.canvas.slaves)}")
        
        # Call original method
        original_method(self)
        
        print(f"  After - slaves in config: {len(self.current_config.slaves)}")
        print(f"  After - slaves on canvas: {len(self.canvas.slaves)}")
        
        # Force canvas update
        print("  Forcing canvas update...")
        self.canvas.update_idletasks()
        
        # Check if we need to scroll to see the slave
        if self.canvas.slaves:
            last_slave = self.canvas.slaves[-1]
            coords = self.canvas.coords(last_slave['id'])
            if coords:
                x1, y1, x2, y2 = coords
                print(f"  Last slave position: ({x1}, {y1})")
                # Try to scroll to make it visible
                self.canvas.xview_moveto(0)  # Scroll to left
                self.canvas.yview_moveto(0.7)  # Scroll down (slaves are at y=500+)
                print("  Scrolled canvas to show slave area")
    
    BusMatrixGUI.add_slave = debug_gui_add_slave

def run_debug_gui():
    """Run GUI with debugging patches"""
    
    print("🚀 Starting GUI with slave canvas debugging")
    print("="*60)
    
    # Apply monkey patches
    monkey_patch_add_slave()
    monkey_patch_gui_add_slave()
    
    # Create and run GUI
    root = tk.Tk()
    gui = BusMatrixGUI(root)
    
    # Add a test callback to check canvas state
    def check_canvas_state():
        print("\n📊 Canvas State Check:")
        print(f"  Canvas size: {gui.canvas.winfo_width()}x{gui.canvas.winfo_height()}")
        print(f"  Scroll region: {gui.canvas.cget('scrollregion')}")
        print(f"  Slaves on canvas: {len(gui.canvas.slaves)}")
        print(f"  Masters on canvas: {len(gui.canvas.masters)}")
        print(f"  All canvas items: {len(gui.canvas.find_all())}")
        
        # Try to make slaves visible
        if gui.canvas.slaves:
            print("  Scrolling to slave area...")
            gui.canvas.yview_moveto(0.5)  # Scroll to middle/bottom
            gui.update_canvas_scroll_region()
    
    # Add menu option to check state
    debug_menu = tk.Menu(gui.menubar, tearoff=0)
    debug_menu.add_command(label="Check Canvas State", command=check_canvas_state)
    debug_menu.add_separator()
    debug_menu.add_command(label="Scroll to Top", command=lambda: gui.canvas.yview_moveto(0))
    debug_menu.add_command(label="Scroll to Middle", command=lambda: gui.canvas.yview_moveto(0.5))
    debug_menu.add_command(label="Scroll to Bottom", command=lambda: gui.canvas.yview_moveto(1.0))
    debug_menu.add_separator()
    debug_menu.add_command(label="Update Scroll Region", command=gui.update_canvas_scroll_region)
    gui.menubar.add_cascade(label="Debug", menu=debug_menu)
    
    print("\n📋 Debug Instructions:")
    print("1. Try adding a slave using the 'Add Slave' button")
    print("2. Watch the console for detailed debug output")
    print("3. Use Debug menu to check canvas state")
    print("4. Try scrolling down - slaves are positioned at y=500+")
    print("5. The canvas scroll region might need adjustment")
    
    root.mainloop()

if __name__ == "__main__":
    run_debug_gui()