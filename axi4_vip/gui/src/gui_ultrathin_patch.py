#!/usr/bin/env python3
"""
GUI UltraThin Patch
Patches the bus_matrix_gui.py to use deferred VIP imports
"""

import os
import sys

def patch_gui_file():
    """Patch the GUI file to use ultrathin imports"""
    gui_file = os.path.join(os.path.dirname(__file__), "bus_matrix_gui.py")
    
    if not os.path.exists(gui_file):
        print(f"Error: GUI file not found at {gui_file}")
        return False
        
    # Read the current content
    with open(gui_file, 'r') as f:
        content = f.read()
    
    # Check if already patched
    if 'vip_gui_integration_ultrathin' in content:
        print("GUI already patched for ultrathin mode")
        return True
    
    # Create backup
    backup_file = gui_file + '.backup'
    if not os.path.exists(backup_file):
        with open(backup_file, 'w') as f:
            f.write(content)
        print(f"Created backup at {backup_file}")
    
    # Replace the import statement
    original_import = "from vip_gui_integration import VIPControlPanel"
    
    # New import with environment check
    new_import = """# UltraThin patch for fast startup and complete 12-step execution
                if os.environ.get('VIP_DEFER_IMPORTS', 'false').lower() == 'true':
                    # Use final version for proper 12-step execution
                    if os.environ.get('VIP_USE_FINAL', 'true').lower() == 'true':
                        from vip_gui_integration_ultrathin_final import VIPControlPanelUltraThin as VIPControlPanel
                    else:
                        from vip_gui_integration_ultrathin import VIPControlPanelUltraThin as VIPControlPanel
                else:
                    from vip_gui_integration import VIPControlPanel"""
    
    # Replace the import
    content = content.replace(original_import, new_import)
    
    # Write the patched content
    with open(gui_file, 'w') as f:
        f.write(content)
    
    print("Successfully patched GUI for ultrathin mode")
    return True

def unpatch_gui_file():
    """Restore original GUI file from backup"""
    gui_file = os.path.join(os.path.dirname(__file__), "bus_matrix_gui.py")
    backup_file = gui_file + '.backup'
    
    if not os.path.exists(backup_file):
        print("No backup file found")
        return False
        
    # Restore from backup
    with open(backup_file, 'r') as f:
        content = f.read()
        
    with open(gui_file, 'w') as f:
        f.write(content)
        
    print("Restored GUI from backup")
    return True

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--unpatch":
        unpatch_gui_file()
    else:
        patch_gui_file()