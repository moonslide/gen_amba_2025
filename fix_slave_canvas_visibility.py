#!/usr/bin/env python3

"""
FIX SLAVE CANVAS VISIBILITY
Fix for slaves not appearing on canvas - likely scroll region issue

Based on git history analysis, the issue is likely that:
1. Slaves are positioned at y=500+ which might be outside initial view
2. Canvas scroll region might not be updated after adding slaves
3. Zoom level might affect visibility
"""

import os
import sys

# Add src directory to path
current_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(current_dir, 'axi4_vip', 'gui', 'src')
backup_dir = os.path.join(current_dir, 'backup')

# Create backup directory
os.makedirs(backup_dir, exist_ok=True)

# Backup the original file
import shutil
original_file = os.path.join(src_dir, 'bus_matrix_gui.py')
backup_file = os.path.join(backup_dir, 'bus_matrix_gui_backup.py')
shutil.copy2(original_file, backup_file)
print(f"✅ Backed up original to: {backup_file}")

# Read the original file
with open(original_file, 'r') as f:
    content = f.read()

# Fix 1: Update the canvas initialization to have a better default scroll region
print("\n🔧 Fix 1: Updating canvas initialization...")
old_canvas_init = """        # Canvas with larger virtual size for top-bottom layout with improved routing
        self.canvas = BusMatrixCanvas(canvas_frame, width=1000, height=700,
                                     scrollregion=(0, 0, 1600, 1000))"""

new_canvas_init = """        # Canvas with larger virtual size for top-bottom layout with improved routing
        self.canvas = BusMatrixCanvas(canvas_frame, width=1000, height=700,
                                     scrollregion=(0, 0, 1600, 1200))  # Increased height for slaves at y=500+"""

if old_canvas_init in content:
    content = content.replace(old_canvas_init, new_canvas_init)
    print("✅ Updated canvas initialization with larger scroll region")
else:
    print("⚠️  Canvas initialization pattern not found")

# Fix 2: Add automatic scroll region update after adding slaves
print("\n🔧 Fix 2: Adding automatic scroll and view adjustment...")
old_add_slave_end = """                self.canvas.add_slave(config, x=int(x_pos), y=int(y_pos))
                self.canvas.draw_interconnect()
                self.canvas.raise_all_blocks()  # Ensure blocks are above lines
                self.update_canvas_scroll_region()
                
                print("DEBUG: Slave added successfully to canvas")
                self.update_status(f"Added slave: {config.name}")"""

new_add_slave_end = """                self.canvas.add_slave(config, x=int(x_pos), y=int(y_pos))
                self.canvas.draw_interconnect()
                self.canvas.raise_all_blocks()  # Ensure blocks are above lines
                self.update_canvas_scroll_region()
                
                # Auto-scroll to show the newly added slave
                self.canvas.update_idletasks()  # Force canvas update
                if len(self.canvas.slaves) == 1:
                    # First slave - scroll to show slave area
                    self.canvas.yview_moveto(0.4)  # Scroll to show slaves area
                else:
                    # Ensure the new slave is visible
                    bbox = self.canvas.bbox("all")
                    if bbox:
                        self.canvas.config(scrollregion=bbox)
                
                print("DEBUG: Slave added successfully to canvas")
                self.update_status(f"Added slave: {config.name}")"""

if old_add_slave_end in content:
    content = content.replace(old_add_slave_end, new_add_slave_end)
    print("✅ Added automatic scroll adjustment after adding slaves")
else:
    print("⚠️  Add slave ending pattern not found")

# Fix 3: Enhance update_canvas_scroll_region to include padding
print("\n🔧 Fix 3: Enhancing scroll region update...")
old_scroll_update = """    def update_canvas_scroll_region(self):
        \"\"\"Update canvas scroll region based on actual content\"\"\"
        # Get bounding box of all items
        bbox = self.canvas.bbox("all")
        if bbox:
            # Add some padding
            x1, y1, x2, y2 = bbox
            self.canvas.config(scrollregion=(x1-50, y1-50, x2+50, y2+50))"""

new_scroll_update = """    def update_canvas_scroll_region(self):
        \"\"\"Update canvas scroll region based on actual content\"\"\"
        # Force canvas update first
        self.canvas.update_idletasks()
        
        # Get bounding box of all items
        bbox = self.canvas.bbox("all")
        if bbox:
            # Add generous padding for better visibility
            x1, y1, x2, y2 = bbox
            # Ensure minimum size for proper scrolling
            x2 = max(x2, 1600)
            y2 = max(y2, 1200)
            self.canvas.config(scrollregion=(x1-100, y1-100, x2+100, y2+100))
            print(f"DEBUG: Updated scroll region to: ({x1-100}, {y1-100}, {x2+100}, {y2+100})")
        else:
            # Set default scroll region if no items
            self.canvas.config(scrollregion=(0, 0, 1600, 1200))
            print("DEBUG: Set default scroll region (no items found)")"""

if old_scroll_update in content:
    content = content.replace(old_scroll_update, new_scroll_update)
    print("✅ Enhanced scroll region update with better padding")
else:
    print("⚠️  Scroll region update pattern not found")

# Fix 4: Ensure refresh_ui properly shows slaves
print("\n🔧 Fix 4: Ensuring refresh_ui shows slaves properly...")
old_refresh_slaves = """            # Add slaves at bottom in horizontal layout
            for i, slave in enumerate(self.current_config.slaves):
                self.slave_listbox.insert(tk.END, 
                                        f"{slave.name} (0x{slave.base_address:08X})")
                col = i % 4  # 4 columns for horizontal layout
                row = i // 4
                x_pos = (50 + col * 200) * zoom  # Wider spacing for 150px wide blocks
                y_pos = (500 + row * 120) * zoom  # Slaves at bottom with taller spacing
                self.canvas.add_slave(slave, x=int(x_pos), y=int(y_pos))"""

new_refresh_slaves = """            # Add slaves at bottom in horizontal layout
            for i, slave in enumerate(self.current_config.slaves):
                self.slave_listbox.insert(tk.END, 
                                        f"{slave.name} (0x{slave.base_address:08X})")
                col = i % 4  # 4 columns for horizontal layout
                row = i // 4
                x_pos = (50 + col * 200) * zoom  # Wider spacing for 150px wide blocks
                y_pos = (400 + row * 120) * zoom  # Moved up from 500 to 400 for better visibility
                self.canvas.add_slave(slave, x=int(x_pos), y=int(y_pos))"""

if old_refresh_slaves in content:
    content = content.replace(old_refresh_slaves, new_refresh_slaves)
    print("✅ Updated slave Y position from 500 to 400 for better visibility")
else:
    print("⚠️  Refresh UI slave pattern not found")

# Fix 5: Update add_slave Y position to match
print("\n🔧 Fix 5: Updating add_slave Y position...")
old_slave_pos = """                y_pos = (500 + row * 120) * zoom  # Slaves at bottom with 120px row spacing (taller blocks)"""
new_slave_pos = """                y_pos = (400 + row * 120) * zoom  # Slaves at 400 for better visibility"""

if old_slave_pos in content:
    content = content.replace(old_slave_pos, new_slave_pos)
    print("✅ Updated add_slave Y position to 400")
else:
    print("⚠️  Add slave position pattern not found")

# Write the fixed content
with open(original_file, 'w') as f:
    f.write(content)

print("\n✅ All fixes applied successfully!")
print("\n📋 Changes made:")
print("1. Increased canvas scroll region height to 1200")
print("2. Added automatic scrolling after adding slaves")
print("3. Enhanced scroll region update with better padding")
print("4. Moved slave Y position from 500 to 400 for better visibility")
print("5. Added debug output to track scroll region changes")

print("\n🔧 Next steps:")
print("1. Run the GUI: python3 axi4_vip/gui/src/bus_matrix_gui.py")
print("2. Add a slave - it should now appear and be visible")
print("3. The canvas will auto-scroll to show the slave area")
print("4. Check console for DEBUG messages about scroll region")

print("\n💡 If slaves still don't appear:")
print("1. Run: python3 debug_slave_canvas.py")
print("2. Use the Debug menu to check canvas state")
print("3. Share the debug output")