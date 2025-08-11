#!/usr/bin/env python3
"""
Fix W channel assignments to use s0_w_owner instead of s0_aw_grant
The comprehensive fix only partially worked - need to fix all assignments
"""

import re

def fix_w_channel_assignments():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("🔧 Fixing W channel assignments to use write ownership...")
    
    # Fix all s0_w* assignments to use s0_w_owner consistently
    signals = ['wdata', 'wstrb', 'wlast', 'wvalid', 'bready']
    
    for signal in signals:
        # Look for the assignment pattern
        pattern = rf"assign s0_{signal} = \s*\n\(s0_w_owner == 4'd0\) \? m0_{signal} :\s*\n\s*\(s0_aw_grant == 4'd1\) \? m1_{signal} :"
        
        # Replace with proper s0_w_owner for all masters
        replacement = f"""assign s0_{signal} = 
(s0_w_owner == 4'd0) ? m0_{signal} :
                   (s0_w_owner == 4'd1) ? m1_{signal} :"""
        
        if re.search(pattern, content):
            content = re.sub(pattern, replacement, content)
            print(f"  ✅ Fixed s0_{signal} assignment to use s0_w_owner")
        
        # Also fix the remaining conditions in the same assignment
        old_pattern = rf"\(s0_aw_grant == 4'd([0-9]+)\) \? m([0-9]+)_{signal} :"
        
        def replace_func(match):
            master_id = match.group(1)
            return f"(s0_w_owner == 4'd{master_id}) ? m{master_id}_{signal} :"
        
        content = re.sub(old_pattern, replace_func, content)
    
    print("  ✅ Fixed all remaining s0_aw_grant references to s0_w_owner")
    
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("✅ Fixed W channel assignments!")
    print("  • All s0_w* signals now use s0_w_owner for consistent write ownership")
    print("  • Masters should now be able to complete write transactions")

if __name__ == "__main__":
    fix_w_channel_assignments()