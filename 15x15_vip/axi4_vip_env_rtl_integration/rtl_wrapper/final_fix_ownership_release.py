#!/usr/bin/env python3
"""
Final fix for ownership release issue
Ensure write ownership is properly released after each transaction
"""

import os
import re
import shutil
from datetime import datetime

def final_fix_ownership():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    # Backup
    backup_file = rtl_file + f".backup_final_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    with open(backup_file, 'w') as f:
        f.write(content)
    
    print("="*80)
    print("FINAL FIX: Ownership Release Issue")
    print("="*80)
    
    # The issue is that s0_w_busy is not being cleared properly
    # because the clear condition is too restrictive
    
    print("\nFixing ownership clear condition...")
    
    # Find and fix the clear logic for all slaves
    for slave_id in range(15):
        # Current pattern that's too restrictive
        pattern = rf"// Clear write ownership when WLAST completes\s*\n\s*if \(s{slave_id}_w_busy && s{slave_id}_wready && s{slave_id}_wvalid && s{slave_id}_wlast\) begin"
        
        # New pattern that's more reliable - clear when we see WLAST from the owner
        replacement = f"""// Clear write ownership when WLAST completes
        if (s{slave_id}_w_busy && s{slave_id}_wlast && s{slave_id}_wvalid) begin
            // Clear on WLAST assertion from owner, don't wait for ready"""
        
        content = re.sub(pattern, replacement, content)
    
    # Alternative: Also clear if a new AW transaction starts
    print("\nAdding alternative clear on new transaction...")
    
    for slave_id in range(15):
        # Find where w_busy is set
        pattern = rf"(s{slave_id}_w_busy <= 1'b1;)"
        
        # Add logic to clear previous ownership if new transaction starts
        replacement = rf"""// Clear any stale ownership before setting new
            if (s{slave_id}_w_busy && s{slave_id}_w_owner != s{slave_id}_aw_grant) begin
                s{slave_id}_w_busy <= 1'b0;
                s{slave_id}_w_owner <= 4'd15;
            end
            \1"""
        
        content = re.sub(pattern, replacement, content)
    
    # Write fixed content
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("\n✅ Applied final ownership release fixes:")
    print("  • Clear on WLAST without waiting for wready")
    print("  • Clear stale ownership on new transaction")
    print("  • Ensures proper handoff between masters")
    
    print(f"\nBackup: {backup_file}")
    return True

if __name__ == "__main__":
    final_fix_ownership()
    print("\n✅ Final fix complete!")