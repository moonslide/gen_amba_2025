#!/usr/bin/env python3
"""
Fix WLAST routing in RTL interconnect
Ensures proper WLAST signal propagation based on grant signals
"""

import os
import sys
import re

def fix_wlast_routing(rtl_file):
    """Fix WLAST signal routing in RTL interconnect"""
    
    if not os.path.exists(rtl_file):
        print(f"Error: RTL file not found: {rtl_file}")
        return False
    
    # Backup original
    backup_file = rtl_file + ".backup_before_wlast_fix"
    with open(rtl_file, 'r') as f:
        original_content = f.read()
    
    with open(backup_file, 'w') as f:
        f.write(original_content)
    
    content = original_content
    
    # Fix s*_wlast assignments to properly route from granted master
    # Current pattern: assign s0_wlast = (s0_aw_grant == 4'd0) ? m0_wlast : ...
    
    for slave_id in range(15):
        # Find the pattern for this slave's WLAST assignment
        pattern = f"assign s{slave_id}_wlast = .*?(?=assign|endmodule|//|$)"
        
        # Build the correct assignment
        new_assignment = f"assign s{slave_id}_wlast = "
        
        # Route from the granted master
        for master_id in range(15):
            if master_id == 0:
                new_assignment += f"\n                 (s{slave_id}_aw_grant == 4'd{master_id}) ? m{master_id}_wlast :"
            elif master_id < 14:
                new_assignment += f"\n                 (s{slave_id}_aw_grant == 4'd{master_id}) ? m{master_id}_wlast :"
            else:  # Last one
                new_assignment += f"\n                 (s{slave_id}_aw_grant == 4'd{master_id}) ? m{master_id}_wlast : 1'b0;"
        
        # Replace the assignment
        content = re.sub(pattern, new_assignment + "\n", content, flags=re.DOTALL)
    
    # Also need to ensure m*_wready is properly connected
    # This affects whether the master can complete its write burst
    
    for master_id in range(15):
        # Find pattern for wready assignment
        pattern = f"assign m{master_id}_wready = .*?(?=assign|endmodule|//|$)"
        
        # Build correct assignment - wready from target slave when granted
        new_assignment = f"assign m{master_id}_wready = "
        
        # Check all slaves for grant to this master
        for slave_id in range(15):
            if slave_id == 0:
                new_assignment += f"\n                 (m{master_id}_aw_target == 4'd{slave_id} && s{slave_id}_aw_grant == 4'd{master_id}) ? s{slave_id}_wready :"
            elif slave_id < 14:
                new_assignment += f"\n                 (m{master_id}_aw_target == 4'd{slave_id} && s{slave_id}_aw_grant == 4'd{master_id}) ? s{slave_id}_wready :"
            else:  # Last one
                new_assignment += f"\n                 (m{master_id}_aw_target == 4'd{slave_id} && s{slave_id}_aw_grant == 4'd{master_id}) ? s{slave_id}_wready : 1'b0;"
        
        content = re.sub(pattern, new_assignment + "\n", content, flags=re.DOTALL)
    
    # Write the fixed content
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print(f"Fixed WLAST and WREADY routing in {rtl_file}")
    print(f"Backup saved to {backup_file}")
    
    # Verify the fix
    with open(rtl_file, 'r') as f:
        verify_content = f.read()
        
    # Check if our fixes are present
    if "(s0_aw_grant == 4'd14) ? m14_wlast" in verify_content:
        print("✅ Verification: WLAST routing logic successfully updated")
        return True
    else:
        print("⚠️ Warning: Fix may not have been fully applied")
        return False

def main():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    print("="*80)
    print("RTL Interconnect WLAST Routing Fix")
    print("="*80)
    
    if fix_wlast_routing(rtl_file):
        print("\n✅ WLAST routing fix applied successfully!")
        print("\nKey improvements:")
        print("  • WLAST properly routed from granted master to slave")
        print("  • WREADY properly routed from target slave to master")
        print("  • Ensures write burst completion handshake")
        print("\nThis fix should resolve:")
        print("  • WLAST count mismatches")
        print("  • Missing WLAST signals")
        print("  • Write transaction completion issues")
    else:
        print("\n⚠️ Fix may need manual verification")
        return 1
    
    return 0

if __name__ == "__main__":
    sys.exit(main())