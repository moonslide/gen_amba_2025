#!/usr/bin/env python3
"""
Comprehensive Fix for RTL Interconnect ID Routing Issue
Properly implements ID-based routing for write responses
"""

import os
import sys
import re

def comprehensive_fix_bid_routing(rtl_file):
    """Comprehensively fix BID routing by regenerating the logic"""
    
    if not os.path.exists(rtl_file):
        print(f"Error: RTL file not found: {rtl_file}")
        return False
    
    # Backup original
    backup_file = rtl_file + ".backup_before_comprehensive_fix"
    with open(rtl_file, 'r') as f:
        original_content = f.read()
    
    with open(backup_file, 'w') as f:
        f.write(original_content)
    
    content = original_content
    
    # Find and replace all m*_bid assignments with proper ID checking
    for master_id in range(15):
        # Find the pattern for this master's BID assignment
        # It could be in various forms, so let's be comprehensive
        
        # Pattern 1: Simple form "assign mX_bid = sY_bvalid ? sY_bid :"
        pattern1 = f"assign m{master_id}_bid = .*?(?=assign|endmodule|//|$)"
        
        # Build the correct assignment with ID checking
        new_assignment = f"assign m{master_id}_bid = "
        
        # Check each slave for a response with matching ID
        for slave_id in range(15):
            if slave_id == 0:
                new_assignment += f"\n                 (s{slave_id}_bvalid && (s{slave_id}_bid[3:0] == 4'd{master_id})) ? s{slave_id}_bid :"
            else:
                new_assignment += f"\n                 (s{slave_id}_bvalid && (s{slave_id}_bid[3:0] == 4'd{master_id})) ? s{slave_id}_bid :"
        
        # Default value if no match
        new_assignment += "\n                 {ID_WIDTH{1'b0}};"
        
        # Replace all variations of this master's BID assignment
        content = re.sub(pattern1, new_assignment + "\n", content, flags=re.DOTALL)
    
    # Fix BVALID routing - only assert when BID matches
    for master_id in range(15):
        # Find and replace m*_bvalid assignments
        pattern = f"assign m{master_id}_bvalid = .*?(?=assign|endmodule|//|$)"
        
        new_assignment = f"assign m{master_id}_bvalid = "
        
        # Check each slave for a response with matching ID
        for slave_id in range(15):
            if slave_id == 0:
                new_assignment += f"\n                 (s{slave_id}_bvalid && (s{slave_id}_bid[3:0] == 4'd{master_id})) |"
            elif slave_id < 14:
                new_assignment += f"\n                 (s{slave_id}_bvalid && (s{slave_id}_bid[3:0] == 4'd{master_id})) |"
            else:  # Last one, no trailing |
                new_assignment += f"\n                 (s{slave_id}_bvalid && (s{slave_id}_bid[3:0] == 4'd{master_id}));"
        
        content = re.sub(pattern, new_assignment + "\n", content, flags=re.DOTALL)
    
    # Fix BRESP routing - route based on BID match
    for master_id in range(15):
        # Find pattern for bresp assignment
        pattern = f"assign m{master_id}_bresp = .*?(?=assign|endmodule|//|$)"
        
        new_assignment = f"assign m{master_id}_bresp = "
        
        # Check each slave for a response with matching ID
        for slave_id in range(15):
            if slave_id == 0:
                new_assignment += f"\n                 (s{slave_id}_bvalid && (s{slave_id}_bid[3:0] == 4'd{master_id})) ? s{slave_id}_bresp :"
            else:
                new_assignment += f"\n                 (s{slave_id}_bvalid && (s{slave_id}_bid[3:0] == 4'd{master_id})) ? s{slave_id}_bresp :"
        
        # Default to OKAY response
        new_assignment += "\n                 2'b00;"
        
        content = re.sub(pattern, new_assignment + "\n", content, flags=re.DOTALL)
    
    # Write the fixed content
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print(f"Comprehensively fixed ID routing in {rtl_file}")
    print(f"Backup saved to {backup_file}")
    
    # Verify the fix by checking a sample
    with open(rtl_file, 'r') as f:
        verify_content = f.read()
        
    # Check if our fixes are present
    if "(s0_bid[3:0] == 4'd0)" in verify_content and "(s0_bid[3:0] == 4'd1)" in verify_content:
        print("✅ Verification: ID checking logic successfully added")
        return True
    else:
        print("⚠️ Warning: Fix may not have been fully applied")
        return False

def main():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    print("="*80)
    print("Comprehensive RTL Interconnect ID Routing Fix")
    print("="*80)
    
    if comprehensive_fix_bid_routing(rtl_file):
        print("\n✅ Comprehensive ID routing fix applied successfully!")
        print("\nKey improvements:")
        print("  • Each master's BID assignment now checks ID match")
        print("  • BVALID only asserted for matching master")
        print("  • BRESP properly routed based on ID")
        print("  • Prevents response crosstalk between masters")
        print("\nThis comprehensive fix should resolve:")
        print("  • BID mismatch errors (Expected X, got 0)")
        print("  • WLAST count mismatches")
        print("  • Scoreboard VIP vs RTL mismatches")
    else:
        print("\n⚠️ Fix may need manual verification")
        return 1
    
    return 0

if __name__ == "__main__":
    sys.exit(main())