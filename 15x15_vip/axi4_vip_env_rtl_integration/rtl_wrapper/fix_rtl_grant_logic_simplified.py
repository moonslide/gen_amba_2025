#!/usr/bin/env python3
"""
Simplified Fix for Master 2 Grant Issue - ULTRATHINK
Focuses on the core grant release problem
"""

import os
import sys
import re
import shutil
from datetime import datetime

def fix_grant_logic(rtl_file):
    """Fix the grant logic to properly handle multiple masters"""
    
    if not os.path.exists(rtl_file):
        print(f"Error: RTL file not found: {rtl_file}")
        return False
    
    # Backup original
    backup_file = rtl_file + f".backup_grant_fix_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    with open(rtl_file, 'r') as f:
        original_content = f.read()
    
    with open(backup_file, 'w') as f:
        f.write(original_content)
    
    content = original_content
    
    print("="*80)
    print("🔍 ULTRATHINK SIMPLIFIED GRANT FIX")
    print("="*80)
    
    print("\n📊 ROOT CAUSE ANALYSIS:")
    print("  The grant is released on awready && awvalid")
    print("  But the grant check for wready uses the CURRENT grant")
    print("  This causes Master 2 to never get wready after Master 0/1 complete")
    
    print("\n🔧 APPLYING TARGETED FIX:")
    
    # FIX: Make sure the grant is properly maintained during write burst
    # The key issue is that once the AW handshake completes, the grant is released
    # but the W channel still needs it
    
    # Solution: Keep track of which master is doing a write burst to each slave
    
    # Add write burst tracking registers after the grant registers
    for slave_id in range(15):
        # Find where the grant registers are declared
        pattern = rf"reg \[3:0\] s{slave_id}_aw_grant;.*?\nreg \[3:0\] s{slave_id}_ar_grant;"
        
        match = re.search(pattern, content)
        if match:
            # Add write burst tracking
            new_regs = match.group(0) + f"""
reg [3:0] s{slave_id}_w_master;  // Track which master is sending W data
reg s{slave_id}_w_active;        // Track if W burst is active"""
            
            content = content.replace(match.group(0), new_regs)
    
    # Now update the arbitration logic to track write bursts
    for slave_id in range(15):
        # Find the arbitration always block
        pattern = rf"(// Round-robin arbitration for slave {slave_id}.*?always @\(posedge aclk or negedge aresetn\) begin.*?)(\n\s*// AR channel arbitration)"
        
        match = re.search(pattern, content, re.DOTALL)
        if match:
            arb_logic = match.group(1)
            
            # Add initialization for new registers
            arb_logic = arb_logic.replace(
                f"s{slave_id}_ar_last_grant <= 4'd0;",
                f"""s{slave_id}_ar_last_grant <= 4'd0;
        s{slave_id}_w_master <= 4'd15;
        s{slave_id}_w_active <= 1'b0;"""
            )
            
            # Modify the grant release logic
            # OLD: Release grant immediately after AW handshake
            # NEW: Track the write burst
            old_release = rf"else if \(s{slave_id}_awready && s{slave_id}_awvalid\) begin\s*\n\s*// Transaction accepted, release grant\s*\n\s*s{slave_id}_aw_last_grant <= s{slave_id}_aw_grant;\s*\n\s*s{slave_id}_aw_grant <= 4'd15;"
            
            new_release = f"""else if (s{slave_id}_awready && s{slave_id}_awvalid) begin
            // AW transaction accepted, track write burst
            s{slave_id}_aw_last_grant <= s{slave_id}_aw_grant;
            s{slave_id}_w_master <= s{slave_id}_aw_grant;  // Remember who's writing
            s{slave_id}_w_active <= 1'b1;                  // Mark write as active
            s{slave_id}_aw_grant <= 4'd15;                 // Can release AW grant
        end
        
        // Clear write tracking when WLAST completes
        if (s{slave_id}_w_active && s{slave_id}_wready && s{slave_id}_wvalid && s{slave_id}_wlast) begin
            s{slave_id}_w_active <= 1'b0;
            s{slave_id}_w_master <= 4'd15;"""
            
            arb_logic = re.sub(old_release, new_release, arb_logic, flags=re.DOTALL)
            
            # Replace in content
            content = content.replace(match.group(1), arb_logic)
    
    # Now fix the wready routing to use the write burst tracking
    print("\n🔧 Fixing WREADY routing to use write burst tracking...")
    
    for master_id in range(15):
        # Find current wready assignment
        pattern = rf"assign m{master_id}_wready = .*?(?=\nassign|$)"
        
        # Build new wready that checks both grant AND write burst tracking
        new_wready = f"assign m{master_id}_wready = "
        
        for slave_id in range(15):
            # WREADY if:
            # 1. This master has the current AW grant to this slave, OR
            # 2. This master is the active writer to this slave
            condition = f"((m{master_id}_aw_target == 4'd{slave_id} && s{slave_id}_aw_grant == 4'd{master_id}) || "
            condition += f"(s{slave_id}_w_active && s{slave_id}_w_master == 4'd{master_id}))"
            
            if slave_id < 14:
                new_wready += f"\n                 {condition} ? s{slave_id}_wready :"
            else:
                new_wready += f"\n                 {condition} ? s{slave_id}_wready : 1'b0;"
        
        content = re.sub(pattern, new_wready, content, flags=re.DOTALL | re.MULTILINE)
    
    # Similarly fix wvalid routing to slaves
    print("\n🔧 Fixing WVALID routing to slaves...")
    
    for slave_id in range(15):
        # Find current wvalid assignment
        pattern = rf"assign s{slave_id}_wvalid = .*?(?=\nassign|$)"
        
        # Build new wvalid that checks write burst tracking
        new_wvalid = f"assign s{slave_id}_wvalid = "
        
        for master_id in range(15):
            if master_id == 0:
                new_wvalid += f"\n(s{slave_id}_w_active && s{slave_id}_w_master == 4'd{master_id}) ? m{master_id}_wvalid :"
            elif master_id < 14:
                new_wvalid += f"\n                    (s{slave_id}_w_active && s{slave_id}_w_master == 4'd{master_id}) ? m{master_id}_wvalid :"
            else:
                new_wvalid += f"\n                    (s{slave_id}_w_active && s{slave_id}_w_master == 4'd{master_id}) ? m{master_id}_wvalid : 1'b0;"
        
        content = re.sub(pattern, new_wvalid, content, flags=re.DOTALL | re.MULTILINE)
    
    # Write the fixed content
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("\n" + "="*80)
    print("✅ SIMPLIFIED GRANT FIX APPLIED!")
    print("="*80)
    
    print("\n🎯 KEY FIXES:")
    print("  1. Added write burst tracking (w_master, w_active)")
    print("  2. Grant released after AW, but write tracking maintained")
    print("  3. WREADY routed based on write burst tracking")
    print("  4. WVALID routed based on write burst tracking")
    
    print("\n💡 EXPECTED RESULTS:")
    print("  • Master 2 gets wready even after grant released")
    print("  • All 3 masters complete write bursts")
    print("  • WLAST count matches expectations")
    
    print(f"\nBackup saved to: {backup_file}")
    
    return True

def main():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    print("\n🚀 ULTRATHINK SIMPLIFIED GRANT LOGIC FIX")
    print("   Fixing Master 2 Write Burst Completion")
    
    if fix_grant_logic(rtl_file):
        print("\n✅ Grant logic fix completed successfully!")
        return 0
    else:
        print("\n❌ Fix failed")
        return 1

if __name__ == "__main__":
    sys.exit(main())