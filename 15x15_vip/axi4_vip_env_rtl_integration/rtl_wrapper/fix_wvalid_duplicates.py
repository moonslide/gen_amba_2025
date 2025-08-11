#!/usr/bin/env python3
"""
Fix duplicate wvalid assignments after grant logic fix
"""

import re

def fix_wvalid_duplicates():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    # Pattern to find duplicate wvalid assignments
    # After our fix, we have the new assignment ending with : 1'b0;
    # followed by the old assignment starting with (s*_aw_grant
    pattern = r'(\? m\d+_wvalid : 1\'b0;)\n(\(s\d+_aw_grant.*?\? m\d+_wvalid : 1\'b0;)'
    
    # Replace with just the first part (our new assignment)
    content = re.sub(pattern, r'\1', content, flags=re.DOTALL)
    
    # Write back
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("Fixed duplicate wvalid assignments")

if __name__ == "__main__":
    fix_wvalid_duplicates()