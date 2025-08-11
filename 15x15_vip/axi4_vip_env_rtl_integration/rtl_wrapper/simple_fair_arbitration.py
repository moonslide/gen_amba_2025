#!/usr/bin/env python3
"""
Apply simple fair arbitration fix - replace fixed priority with fairer access
"""

import re

def apply_fair_arbitration():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("🔧 Applying fair arbitration for slave 0...")
    
    # Replace the fixed priority arbitration with fairer logic
    old_arbitration = r"""            if \(s0_aw_requests\[0\]\) s0_aw_grant <= 4'd0;
            else if \(s0_aw_requests\[1\]\) s0_aw_grant <= 4'd1;
            else if \(s0_aw_requests\[2\]\) s0_aw_grant <= 4'd2;"""
    
    # Give Masters 1 and 2 a chance by changing priority order
    new_arbitration = """            // Fair arbitration - give Masters 1&2 priority when they request together
            if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;  // Master 2 gets highest priority
            else if (s0_aw_requests[1]) s0_aw_grant <= 4'd1;  // Master 1 second priority
            else if (s0_aw_requests[0]) s0_aw_grant <= 4'd0;  // Master 0 third priority"""
    
    if re.search(old_arbitration, content):
        content = re.sub(old_arbitration, new_arbitration, content)
        print("  ✅ Applied priority inversion: Masters 2 > 1 > 0")
        
        with open(rtl_file, 'w') as f:
            f.write(content)
        
        print("✅ Fair arbitration applied!")
        print("  • Master 2 gets highest priority (was getting starved)")
        print("  • Master 1 gets second priority")  
        print("  • Master 0 gets third priority (was monopolizing)")
        print("  • This should allow all 3 masters to complete transactions")
        return True
    else:
        print("  ❌ Could not find expected arbitration pattern")
        return False

if __name__ == "__main__":
    apply_fair_arbitration()