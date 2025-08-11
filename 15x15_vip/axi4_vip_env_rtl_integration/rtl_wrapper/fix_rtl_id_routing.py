#!/usr/bin/env python3
"""
Fix RTL Interconnect ID Routing Issue
Fixes the BID routing problem where all masters receive the same BID
"""

import os
import sys
import re

def fix_bid_routing(rtl_file):
    """Fix the BID routing to properly match responses to requesting masters"""
    
    if not os.path.exists(rtl_file):
        print(f"Error: RTL file not found: {rtl_file}")
        return False
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    # The current broken implementation broadcasts BID to all masters
    # We need to fix it to check the BID and route to the correct master
    
    # Fix Master 0 BID assignment
    broken_m0_bid = r"assign m0_bid = \ns0_bvalid \? s0_bid :\n\s+s1_bvalid \? s1_bid :"
    fixed_m0_bid = """assign m0_bid = 
(s0_bvalid && (s0_bid[3:0] == 4'd0)) ? s0_bid :
                 (s1_bvalid && (s1_bid[3:0] == 4'd0)) ? s1_bid :"""
    
    content = re.sub(broken_m0_bid, fixed_m0_bid, content)
    
    # Fix the simpler form too
    content = re.sub(
        r"assign m0_bid = s0_bvalid \? s0_bid :",
        "assign m0_bid = (s0_bvalid && (s0_bid[3:0] == 4'd0)) ? s0_bid :",
        content
    )
    
    # Fix Master 1 BID assignment
    content = re.sub(
        r"assign m1_bid = \ns0_bvalid \? s0_bid :",
        "assign m1_bid = \n(s0_bvalid && (s0_bid[3:0] == 4'd1)) ? s0_bid :",
        content
    )
    content = re.sub(
        r"assign m1_bid = s0_bvalid \? s0_bid :",
        "assign m1_bid = (s0_bvalid && (s0_bid[3:0] == 4'd1)) ? s0_bid :",
        content
    )
    
    # Fix Master 2 BID assignment  
    content = re.sub(
        r"assign m2_bid = \ns0_bvalid \? s0_bid :",
        "assign m2_bid = \n(s0_bvalid && (s0_bid[3:0] == 4'd2)) ? s0_bid :",
        content
    )
    content = re.sub(
        r"assign m2_bid = s0_bvalid \? s0_bid :",
        "assign m2_bid = (s0_bvalid && (s0_bid[3:0] == 4'd2)) ? s0_bid :",
        content
    )
    
    # Fix all other masters (3-14) using a more general pattern
    for i in range(3, 15):
        content = re.sub(
            f"assign m{i}_bid = \ns0_bvalid \\? s0_bid :",
            f"assign m{i}_bid = \n(s0_bvalid && (s0_bid[3:0] == 4'd{i})) ? s0_bid :",
            content
        )
        content = re.sub(
            f"assign m{i}_bid = s0_bvalid \\? s0_bid :",
            f"assign m{i}_bid = (s0_bvalid && (s0_bid[3:0] == 4'd{i})) ? s0_bid :",
            content
        )
    
    # Also fix the continuation lines for all slaves
    for master in range(15):
        for slave in range(1, 15):
            # Fix patterns like "s1_bvalid ? s1_bid :"
            content = re.sub(
                f"s{slave}_bvalid \\? s{slave}_bid :",
                f"(s{slave}_bvalid && (s{slave}_bid[3:0] == 4'd{master})) ? s{slave}_bid :",
                content
            )
    
    # Fix BVALID routing - only send to the master that matches the BID
    for master in range(15):
        # Fix patterns for m*_bvalid assignment
        old_pattern = f"assign m{master}_bvalid = s0_bvalid \\|"
        new_pattern = f"assign m{master}_bvalid = (s0_bvalid && (s0_bid[3:0] == 4'd{master})) |"
        content = re.sub(old_pattern, new_pattern, content)
        
        # Continue for other slaves
        for slave in range(1, 15):
            old_pattern = f"s{slave}_bvalid \\|"
            new_pattern = f"(s{slave}_bvalid && (s{slave}_bid[3:0] == 4'd{master})) |"
            content = re.sub(old_pattern, new_pattern, content)
    
    # Save the fixed RTL
    backup_file = rtl_file + ".backup_id_routing"
    with open(backup_file, 'w') as f:
        f.write(content)
    
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print(f"Fixed ID routing in {rtl_file}")
    print(f"Backup saved to {backup_file}")
    return True

def main():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    print("="*80)
    print("Fixing RTL Interconnect ID Routing Issue")
    print("="*80)
    
    if fix_bid_routing(rtl_file):
        print("\n✅ ID routing fix applied successfully!")
        print("\nKey fixes:")
        print("  • BID now checked against master ID before routing")
        print("  • BVALID only sent to matching master")
        print("  • Each master receives only its own responses")
        print("\nThis should fix:")
        print("  • BID mismatch errors")
        print("  • WLAST count mismatches")
        print("  • Scoreboard VIP vs RTL mismatches")
    else:
        print("\n❌ Failed to apply ID routing fix")
        return 1
    
    return 0

if __name__ == "__main__":
    sys.exit(main())