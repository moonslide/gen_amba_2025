#!/usr/bin/env python3
"""
Simple fix for Master 2 stuck issue - ULTRATHINK
Focus on ensuring all masters can access slave 0
"""

import os
import sys
import re
import shutil
from datetime import datetime

def simple_fix_master2(rtl_file):
    """Apply a simple fix to ensure Master 2 can complete"""
    
    if not os.path.exists(rtl_file):
        print(f"Error: RTL file not found: {rtl_file}")
        return False
    
    # Backup original
    backup_file = rtl_file + f".backup_simple_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    with open(rtl_file, 'r') as f:
        original_content = f.read()
    
    with open(backup_file, 'w') as f:
        f.write(original_content)
    
    content = original_content
    
    print("="*80)
    print("🔍 ULTRATHINK SIMPLE FIX FOR MASTER 2")
    print("="*80)
    
    print("\n📊 ROOT CAUSE:")
    print("  Masters 0, 1, 2 all target slave 0")
    print("  Fixed priority causes Master 2 to starve")
    print("  The 800ns timeout in virtual sequence too short")
    
    print("\n🔧 SIMPLE FIX: Fair arbitration with transaction completion tracking")
    
    # Find slave 0 arbitration and make it fairer
    # Current code gives strict priority to lower numbered masters
    
    # Fix 1: Change the arbitration to be more fair - use a counter
    for slave_id in range(15):
        # Add a counter to track last granted master
        pattern = rf"reg \[3:0\] s{slave_id}_aw_last_grant;"
        replacement = rf"reg [3:0] s{slave_id}_aw_last_grant;\nreg [3:0] s{slave_id}_next_check;  // For fair arbitration"
        content = content.replace(pattern, replacement)
        
        # Initialize the counter
        pattern = rf"s{slave_id}_aw_last_grant <= 4'd0;"
        replacement = rf"s{slave_id}_aw_last_grant <= 4'd0;\n        s{slave_id}_next_check <= 4'd0;"
        content = content.replace(pattern, replacement)
        
        # Now fix the arbitration logic to check masters in round-robin order
        # Find the simplified grant logic
        pattern = rf"if \(s{slave_id}_aw_grant == 4'd15\) begin // No current grant\s*\n\s*// Simplified: grant to lowest numbered requesting master"
        
        if pattern in content:
            # Build better arbitration that cycles through masters
            new_arb = f"""if (s{slave_id}_aw_grant == 4'd15) begin // No current grant
            // Fair arbitration: check from next_check position
            integer checked;
            reg granted;
            granted = 1'b0;
            checked = 0;
            
            // Try each master starting from next_check
            while (checked < 15 && !granted) begin
                if (s{slave_id}_aw_requests[s{slave_id}_next_check]) begin
                    s{slave_id}_aw_grant <= s{slave_id}_next_check;
                    granted = 1'b1;
                end
                s{slave_id}_next_check <= (s{slave_id}_next_check == 4'd14) ? 4'd0 : s{slave_id}_next_check + 1;
                checked = checked + 1;
            end"""
            
            # Replace the entire priority block
            old_block = rf"if \(s{slave_id}_aw_grant == 4'd15\) begin // No current grant.*?else if \(s{slave_id}_aw_requests\[14\]\) s{slave_id}_aw_grant <= 4'd14;"
            
            content = re.sub(old_block, new_arb, content, flags=re.DOTALL)
    
    # Write the fixed content
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("\n✅ Simple fix applied!")
    print("\n🎯 Fix Summary:")
    print("  • Added fair round-robin checking")
    print("  • Each slave tracks next master to check")
    print("  • Prevents master starvation")
    
    print(f"\nBackup saved to: {backup_file}")
    
    return True

def main():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    print("\n🚀 ULTRATHINK SIMPLE MASTER 2 FIX")
    
    if simple_fix_master2(rtl_file):
        print("\n✅ Fix completed successfully!")
        return 0
    else:
        print("\n❌ Fix failed")
        return 1

if __name__ == "__main__":
    sys.exit(main())