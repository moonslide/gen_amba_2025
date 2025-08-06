#!/usr/bin/env python3
"""
Fix for the 8/12 progress issue in VIP generation
This patch prevents the premature SUCCESS marking at step 8
"""

import sys
import os

def patch_vip_integration():
    """Patch vip_gui_integration.py to fix the 8/12 issue"""
    
    filepath = os.path.join(os.path.dirname(__file__), "vip_gui_integration.py")
    
    with open(filepath, 'r') as f:
        content = f.read()
    
    patches_applied = 0
    
    # Patch 1: Remove premature completion message
    old_line1 = '                self.update_progress("VIP generation completed successfully!")'
    new_line1 = '                # PATCHED: Removed premature completion message\n                # self.update_progress("VIP generation completed successfully!")'
    
    if old_line1 in content and new_line1 not in content:
        content = content.replace(old_line1, new_line1)
        patches_applied += 1
        print("[PATCH 1] Removed premature 'VIP generation completed successfully!' message")
    elif new_line1 in content:
        print("[PATCH 1] Already applied")
    
    # Patch 2: Remove RTL integration completed message that causes step 7
    old_line2 = '            if not self.update_progress("RTL integration environment completed"):\n                return None'
    new_line2 = '            # PATCHED: Removed RTL integration completed message that causes step 7\n            # if not self.update_progress("RTL integration environment completed"):\n            #     return None'
    
    if old_line2 in content and new_line2 not in content:
        content = content.replace(old_line2, new_line2)
        patches_applied += 1
        print("[PATCH 2] Removed 'RTL integration environment completed' message at step 7")
    elif new_line2 in content:
        print("[PATCH 2] Already applied")
    
    if patches_applied > 0:
        # Write the patched content
        with open(filepath, 'w') as f:
            f.write(content)
        
        print(f"\n[SUCCESS] Applied {patches_applied} patches to vip_gui_integration.py")
        print("The VIP generation will now properly execute all 12 steps")
        return True
    else:
        print("[INFO] All patches already applied to vip_gui_integration.py")
        return True

def unpatch_vip_integration():
    """Remove the patch from vip_gui_integration.py"""
    
    filepath = os.path.join(os.path.dirname(__file__), "vip_gui_integration.py")
    
    with open(filepath, 'r') as f:
        content = f.read()
    
    patches_removed = 0
    
    # Unpatch 1: Restore completion message
    patched_lines1 = '                # PATCHED: Removed premature completion message\n                # self.update_progress("VIP generation completed successfully!")'
    original_line1 = '                self.update_progress("VIP generation completed successfully!")'
    
    if patched_lines1 in content:
        content = content.replace(patched_lines1, original_line1)
        patches_removed += 1
        print("[UNPATCH 1] Restored 'VIP generation completed successfully!' message")
    
    # Unpatch 2: Restore RTL integration completed message
    patched_lines2 = '            # PATCHED: Removed RTL integration completed message that causes step 7\n            # if not self.update_progress("RTL integration environment completed"):\n            #     return None'
    original_line2 = '            if not self.update_progress("RTL integration environment completed"):\n                return None'
    
    if patched_lines2 in content:
        content = content.replace(patched_lines2, original_line2)
        patches_removed += 1
        print("[UNPATCH 2] Restored 'RTL integration environment completed' message")
    
    if patches_removed > 0:
        with open(filepath, 'w') as f:
            f.write(content)
        
        print(f"\n[SUCCESS] Removed {patches_removed} patches from vip_gui_integration.py")
        return True
    else:
        print("[INFO] vip_gui_integration.py has no patches to remove")
        return True

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--unpatch":
        unpatch_vip_integration()
    else:
        patch_vip_integration()