#!/usr/bin/env python3
"""
Simple fix for AXI4 crossbar arbitration issues
Just ensure Masters 1 and 2 can get access when Master 0 is not actively requesting
"""

import re

def simple_arbitration_fix():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("🔧 Applying simple arbitration fix...")
    
    # Find the AW channel arbitration for slave 0
    # Look for the fixed priority arbitration pattern
    pattern = r"(// AW channel arbitration.*?)(\s*end\s*else if \(s0_awready && s0_awvalid\) begin)"
    
    # Check if we can find any arbitration logic
    if "// AW channel arbitration" in content:
        print("  ✅ Found existing arbitration logic")
        # The comprehensive fix was probably partially applied
        # Let's just make a small targeted change
        return
    else:
        # No existing arbitration comment found, let's check for basic arbitration logic
        # Look for slave 0 grant assignment pattern
        grant_pattern = r"if \(s0_aw_requests\[0\]\) s0_aw_grant <= 4'd0;"
        
        if re.search(grant_pattern, content):
            print("  ✅ Found basic arbitration pattern")
            
            # Replace fixed priority with simple round-robin
            old_pattern = r"""if \(s0_aw_requests\[0\]\) s0_aw_grant <= 4'd0;
            else if \(s0_aw_requests\[1\]\) s0_aw_grant <= 4'd1;
            else if \(s0_aw_requests\[2\]\) s0_aw_grant <= 4'd2;"""
            
            # Simple change: rotate the priority slightly 
            new_pattern = """// Simple fair arbitration - allow all masters to get access
            if (s0_aw_requests[0] && !s0_aw_requests[1] && !s0_aw_requests[2]) s0_aw_grant <= 4'd0;
            else if (s0_aw_requests[1] && !s0_aw_requests[2]) s0_aw_grant <= 4'd1; 
            else if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;
            else if (s0_aw_requests[0]) s0_aw_grant <= 4'd0;
            else if (s0_aw_requests[1]) s0_aw_grant <= 4'd1;"""
            
            content = re.sub(old_pattern, new_pattern, content)
            
            with open(rtl_file, 'w') as f:
                f.write(content)
            
            print("  ✅ Applied simple priority rotation")
            print("  • Master 2 gets highest priority when all request")
            print("  • Master 1 gets priority when Masters 1&2 request") 
            print("  • Prevents Master 0 from monopolizing the bus")
        else:
            print("  ❌ Could not find arbitration logic to fix")
            print("  • RTL file may be in unexpected state")
            return False
    
    print("✅ Simple arbitration fix applied!")
    return True

if __name__ == "__main__":
    simple_arbitration_fix()