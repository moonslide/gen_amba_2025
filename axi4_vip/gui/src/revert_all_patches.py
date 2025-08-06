#!/usr/bin/env python3
"""
Revert all patches to restore VIP button functionality
"""

import os
import sys

def revert_vip_integration_patches():
    """Revert patches to vip_gui_integration.py"""
    
    filepath = "/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_gui_integration.py"
    
    with open(filepath, 'r') as f:
        content = f.read()
    
    reverts_applied = 0
    
    # Revert patch 1: Remove premature completion message patch
    patched_lines1 = '                # PATCHED: Removed premature completion message\n                # self.update_progress("VIP generation completed successfully!")'
    original_line1 = '                self.update_progress("VIP generation completed successfully!")'
    
    if patched_lines1 in content:
        content = content.replace(patched_lines1, original_line1)
        reverts_applied += 1
        print("[REVERT 1] Restored 'VIP generation completed successfully!' message")
    
    # Revert patch 2: Remove RTL integration completed message patch
    patched_lines2 = '            # PATCHED: Removed RTL integration completed message that causes step 7\n            # if not self.update_progress("RTL integration environment completed"):\n            #     return None'
    original_line2 = '            if not self.update_progress("RTL integration environment completed"):\n                return None'
    
    if patched_lines2 in content:
        content = content.replace(patched_lines2, original_line2)
        reverts_applied += 1
        print("[REVERT 2] Restored 'RTL integration environment completed' message")
    
    # Revert patch 3: Remove complexity detection patch
    # Find and remove the entire complexity detection block
    patch_start = content.find('        # ULTRATHIN PATCH: Auto-detect complex configurations')
    if patch_start != -1:
        # Find the end of the patch (before the original try block)
        patch_end = content.find('        # Continue with original flow', patch_start)
        if patch_end != -1:
            patch_end = content.find('\n        \n', patch_end) + 1
            if patch_end > patch_start:
                # Remove the entire patch block
                content = content[:patch_start] + content[patch_end:]
                reverts_applied += 1
                print("[REVERT 3] Removed complexity detection patch")
    
    if reverts_applied > 0:
        with open(filepath, 'w') as f:
            f.write(content)
        print(f"\n[SUCCESS] Applied {reverts_applied} reverts to vip_gui_integration.py")
        return True
    else:
        print("[INFO] No patches found to revert in vip_gui_integration.py")
        return True

def revert_bus_matrix_gui_patches():
    """Revert patches to bus_matrix_gui.py"""
    
    filepath = "/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/bus_matrix_gui.py"
    
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Find and remove the template complexity detection
    patch_start = content.find('            # Check for complex configurations that need ultrathin mode')
    if patch_start != -1:
        # Find the end of the patch (before the original dataclass conversion)
        patch_end = content.find('            # Convert to dataclasses with default values for missing fields', patch_start)
        if patch_end != -1:
            # Remove the entire patch block
            content = content[:patch_start] + content[patch_end:]
            
            with open(filepath, 'w') as f:
                f.write(content)
            
            print("[REVERT 4] Removed template complexity detection from bus_matrix_gui.py")
            return True
    
    print("[INFO] No template patches found to revert in bus_matrix_gui.py")
    return True

def clear_environment_variables():
    """Clear ultrathin environment variables"""
    
    vars_cleared = 0
    ultrathin_vars = ['VIP_DEFER_IMPORTS', 'VIP_USE_FINAL', 'VIP_FAST_GEN', 'VIP_LAZY_LOAD', 'VIP_SKIP_COMPONENT_INIT']
    
    for var in ultrathin_vars:
        if var in os.environ:
            del os.environ[var]
            vars_cleared += 1
    
    if vars_cleared > 0:
        print(f"[REVERT 5] Cleared {vars_cleared} ultrathin environment variables")
    else:
        print("[INFO] No ultrathin environment variables to clear")
    
    return vars_cleared > 0

def main():
    print("=== Reverting All VIP Patches ===\n")
    print("This will restore the original VIP functionality and bring back the VIP button.\n")
    
    success = True
    
    # Revert all patches
    print("[STEP 1] Reverting vip_gui_integration.py patches...")
    success &= revert_vip_integration_patches()
    
    print("\n[STEP 2] Reverting bus_matrix_gui.py patches...")
    success &= revert_bus_matrix_gui_patches()
    
    print("\n[STEP 3] Clearing environment variables...")  
    clear_environment_variables()
    
    if success:
        print("\n" + "="*50)
        print("✅ ALL PATCHES REVERTED SUCCESSFULLY")
        print("="*50)
        print("\nThe VIP functionality has been restored to original state:")
        print("• VIP button should now be visible in the GUI")
        print("• Original VIP generation flow restored")
        print("• All ultrathin patches removed")
        print("• Environment variables cleared")
        
        print("\nNext steps:")
        print("1. Restart the GUI application")
        print("2. VIP panel and buttons should be visible again")
        print("3. VIP generation will work with original behavior")
        
        print("\nNote: Complex templates will now use original behavior")
        print("(may stop at 6/12 again, but VIP functionality restored)")
        
    else:
        print("\n❌ SOME REVERTS FAILED")
        print("Manual cleanup may be required")
        return False
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)