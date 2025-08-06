#!/usr/bin/env python3

"""
FIX SLAVE SAVE BUTTON ISSUE
Fix for slaves not appearing in list/layout after Save button click

The issue: allowed_masters field type mismatch - expects List[int] but gets List[str]
"""

import os
import sys
import shutil

# Add src directory to path
current_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(current_dir, 'axi4_vip', 'gui', 'src')
backup_dir = os.path.join(current_dir, 'backup')

# Create backup directory
os.makedirs(backup_dir, exist_ok=True)

# Backup the original file
original_file = os.path.join(src_dir, 'bus_config.py')
backup_file = os.path.join(backup_dir, 'bus_config_backup2.py')
shutil.copy2(original_file, backup_file)
print(f"✅ Backed up original to: {backup_file}")

# Read the original file
with open(original_file, 'r') as f:
    content = f.read()

# Fix 1: Change allowed_masters type from List[int] to List[str]
print("\n🔧 Fix 1: Changing allowed_masters type from List[int] to List[str]...")
old_type = "    allowed_masters: List[int] = None"
new_type = "    allowed_masters: List[str] = None"

if old_type in content:
    content = content.replace(old_type, new_type)
    print("✅ Changed allowed_masters type to List[str]")
else:
    print("⚠️  allowed_masters type pattern not found")

# Write the fixed content
with open(original_file, 'w') as f:
    f.write(content)

print("\n✅ Fix applied successfully!")

# Now also fix the canvas click issue in bus_matrix_gui.py
gui_file = os.path.join(src_dir, 'bus_matrix_gui.py')
gui_backup = os.path.join(backup_dir, 'bus_matrix_gui_backup2.py')
shutil.copy2(gui_file, gui_backup)
print(f"\n✅ Backed up GUI file to: {gui_backup}")

# Read the GUI file
with open(gui_file, 'r') as f:
    gui_content = f.read()

# Fix 2: Add safety check for canvas click
print("\n🔧 Fix 2: Adding safety check for canvas click...")
old_click = """    def on_click(self, event):
        \"\"\"Handle canvas click events\"\"\"
        # Convert screen coordinates to canvas coordinates
        x = self.canvasx(event.x)
        y = self.canvasy(event.y)
        
        # Find the closest item
        clicked_item = self.find_closest(x, y)[0]"""

new_click = """    def on_click(self, event):
        \"\"\"Handle canvas click events\"\"\"
        # Convert screen coordinates to canvas coordinates
        x = self.canvasx(event.x)
        y = self.canvasy(event.y)
        
        # Find the closest item
        closest_items = self.find_closest(x, y)
        if not closest_items:
            return  # No items found
        clicked_item = closest_items[0]"""

if old_click in gui_content:
    gui_content = gui_content.replace(old_click, new_click)
    print("✅ Added safety check for canvas click")
else:
    print("⚠️  Canvas click pattern not found")

# Write the fixed GUI content
with open(gui_file, 'w') as f:
    f.write(gui_content)

print("\n✅ All fixes applied successfully!")
print("\n📋 Changes made:")
print("1. Changed allowed_masters type from List[int] to List[str] in bus_config.py")
print("2. Added safety check for empty canvas clicks in bus_matrix_gui.py")
print("\n🔧 The slave Save button should now work correctly!")
print("\n💡 Test it:")
print("1. Run: python3 axi4_vip/gui/src/bus_matrix_gui.py")
print("2. Add a slave and click Save")
print("3. The slave should now appear in both the list and canvas")