#!/usr/bin/env python3
"""
Final simple fix - reverse priority to let Masters 1&2 complete
"""

def apply_final_fix():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("🔧 Applying final simple fix - priority inversion...")
    
    # Replace the specific pattern we found
    old_pattern = """            if (s0_aw_requests[0]) s0_aw_grant <= 4'd0;

            else if (s0_aw_requests[1]) s0_aw_grant <= 4'd1;

            else if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;"""
    
    # Reverse the priority: 2 > 1 > 0 instead of 0 > 1 > 2  
    new_pattern = """            // FIXED: Reverse priority to ensure Masters 1&2 can complete
            if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;

            else if (s0_aw_requests[1]) s0_aw_grant <= 4'd1;

            else if (s0_aw_requests[0]) s0_aw_grant <= 4'd0;"""
    
    if old_pattern in content:
        content = content.replace(old_pattern, new_pattern)
        
        with open(rtl_file, 'w') as f:
            f.write(content)
        
        print("✅ Applied priority inversion!")
        print("  • Master 2 now has highest priority")
        print("  • Master 1 has second priority") 
        print("  • Master 0 has lowest priority")
        print("  • This should allow all masters to complete")
        return True
    else:
        print("❌ Pattern not found")
        return False

if __name__ == "__main__":
    apply_final_fix()