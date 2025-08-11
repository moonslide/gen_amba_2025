#!/usr/bin/env python3
"""
ULTRATHINK BID ROUTING FIX

Current Issue:
- Masters 1 and 2 receive BID=0 instead of BID=1 and BID=2
- The B-channel response routing is incorrect

Root Cause:
The B-channel response (BID, BRESP, BVALID) needs to be routed based on
which master owns the write channel (tracked by s*_w_owner), not the 
current grant.

Solution:
Fix m*_bid, m*_bresp, and m*_bvalid assignments to use write ownership.
"""

import re
import os
import shutil
import time

def apply_bid_routing_fix():
    """Fix BID routing to use write ownership"""
    print("🎯 ULTRATHINK BID ROUTING FIX")
    print("=" * 60)
    
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    # Backup current state
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    backup_file = rtl_file + f".backup_bid_fix_{timestamp}"
    shutil.copy(rtl_file, backup_file)
    print(f"✅ Backup created: {backup_file}")
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("\n📋 ISSUE:")
    print("  • Master 1 expects BID=1, gets BID=0")
    print("  • Master 2 expects BID=2, gets BID=0")
    print("  • B-channel routing uses wrong logic")
    
    fixes = []
    
    # Fix B-channel routing for each master
    for master_id in range(15):
        print(f"\n🔧 Fixing Master {master_id} B-channel routing...")
        
        # Find m*_bvalid assignment
        bvalid_pattern = f"assign m{master_id}_bvalid = "
        bvalid_match = content.find(bvalid_pattern)
        
        if bvalid_match > 0:
            # Find the end of this assignment (next semicolon)
            end_pos = content.find(";", bvalid_match)
            
            if end_pos > 0:
                old_assignment = content[bvalid_match:end_pos + 1]
                
                # Build new assignment using write ownership
                new_bvalid_lines = [f"assign m{master_id}_bvalid = "]
                
                # Check each slave to see if it has a response for this master
                for slave_id in range(15):
                    condition = f"(s{slave_id}_bvalid && (s{slave_id}_bid[3:0] == 4'd{master_id}))"
                    if slave_id < 14:
                        new_bvalid_lines.append(f"{condition} |")
                    else:
                        new_bvalid_lines.append(f"{condition};")
                
                new_assignment = "\n".join(new_bvalid_lines)
                
                # Only replace if different
                if old_assignment.strip() != new_assignment.strip():
                    content = content[:bvalid_match] + new_assignment + content[end_pos + 1:]
                    fixes.append(f"Fixed Master {master_id} bvalid routing")
        
        # Fix m*_bid assignment
        bid_pattern = f"assign m{master_id}_bid = "
        bid_match = content.find(bid_pattern)
        
        if bid_match > 0:
            end_pos = content.find(";", bid_match)
            
            if end_pos > 0:
                # Build new BID assignment
                new_bid_lines = [f"assign m{master_id}_bid = "]
                
                # Route BID from the slave that has a response for this master
                bid_conditions = []
                for slave_id in range(15):
                    condition = f"(s{slave_id}_bvalid && (s{slave_id}_bid[3:0] == 4'd{master_id})) ? s{slave_id}_bid"
                    bid_conditions.append(condition)
                
                # Join with : for ternary chain
                new_bid_assignment = new_bid_lines[0] + "\n" + " :\n".join(bid_conditions) + " : 4'd0;"
                
                content = content[:bid_match] + new_bid_assignment + content[end_pos + 1:]
                fixes.append(f"Fixed Master {master_id} bid routing")
        
        # Fix m*_bresp assignment similarly
        bresp_pattern = f"assign m{master_id}_bresp = "
        bresp_match = content.find(bresp_pattern)
        
        if bresp_match > 0:
            end_pos = content.find(";", bresp_match)
            
            if end_pos > 0:
                # Build new BRESP assignment
                new_bresp_lines = [f"assign m{master_id}_bresp = "]
                
                bresp_conditions = []
                for slave_id in range(15):
                    condition = f"(s{slave_id}_bvalid && (s{slave_id}_bid[3:0] == 4'd{master_id})) ? s{slave_id}_bresp"
                    bresp_conditions.append(condition)
                
                new_bresp_assignment = new_bresp_lines[0] + "\n" + " :\n".join(bresp_conditions) + " : 2'd0;"
                
                content = content[:bresp_match] + new_bresp_assignment + content[end_pos + 1:]
                fixes.append(f"Fixed Master {master_id} bresp routing")
    
    # Fix s*_bready routing to use write ownership
    print("\n🔧 Fixing slave bready routing...")
    
    for slave_id in range(15):
        bready_pattern = f"assign s{slave_id}_bready = "
        bready_match = content.find(bready_pattern)
        
        if bready_match > 0:
            end_pos = content.find(";", bready_match)
            
            if end_pos > 0:
                # Build new bready assignment using write ownership
                new_bready_lines = [f"assign s{slave_id}_bready = "]
                
                # Route bready based on write owner
                bready_conditions = []
                for master_id in range(15):
                    if f"s{slave_id}_w_owner" in content:
                        # Use write owner if available
                        condition = f"(s{slave_id}_w_active && (s{slave_id}_w_owner == 4'd{master_id})) ? m{master_id}_bready"
                    else:
                        # Fall back to grant-based routing
                        condition = f"(s{slave_id}_aw_grant == 4'd{master_id}) ? m{master_id}_bready"
                    bready_conditions.append(condition)
                
                new_bready_assignment = new_bready_lines[0] + "\n" + " :\n".join(bready_conditions) + " : 1'b1;"
                
                content = content[:bready_match] + new_bready_assignment + content[end_pos + 1:]
                fixes.append(f"Fixed Slave {slave_id} bready routing")
    
    # Write the fixed content
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("\n✅ FIXES APPLIED:")
    for fix in fixes:
        print(f"  • {fix}")
    
    return True

def compile_and_test():
    """Compile and test the fix"""
    sim_dir = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/sim"
    os.chdir(sim_dir)
    
    print("\n🧪 TESTING BID ROUTING FIX...")
    print("🔄 Cleaning...")
    os.system("make clean > /dev/null 2>&1")
    
    print("🔨 Compiling...")
    result = os.system("make compile 2>&1 | tail -10")
    
    if result == 0:
        print("✅ Compilation successful")
        
        print("🏃 Running test...")
        os.system("make run TEST=axi4_simple_crossbar_test > /dev/null 2>&1 &")
        
        # Wait for test completion
        time.sleep(20)
        
        print("\n📊 TEST RESULTS:")
        print("=" * 60)
        
        # Check for UVM errors
        print("UVM_ERROR Count:")
        os.system("grep 'UVM_ERROR :' logs/axi4_simple_crossbar_test_1.log")
        
        print("\nSpecific Errors (if any):")
        os.system("grep 'UVM_ERROR' logs/axi4_simple_crossbar_test_1.log | grep -v 'UVM_ERROR :' | head -5")
        
        # Check B-channel responses
        print("\nB-channel Responses:")
        os.system("grep 'B-channel response' logs/axi4_simple_crossbar_test_1.log | tail -10")
        
        # Check test status
        print("\nTest Status:")
        os.system("grep -E 'TEST (PASSED|FAILED)' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n" + "=" * 60)
        print("🎯 SUCCESS CRITERIA: UVM_ERROR count should be 0")
        
        return True
    else:
        print("❌ Compilation failed")
        return False

if __name__ == "__main__":
    print("🚀 ULTRATHINK BID ROUTING FIX")
    print("=" * 60)
    print("Fixing B-channel ID routing for all masters")
    print()
    
    if apply_bid_routing_fix():
        print("\n✅ BID routing fix applied successfully")
        
        if compile_and_test():
            print("\n✅ Test completed - check results above")
        else:
            print("\n⚠️ Test execution failed")
    else:
        print("\n❌ Failed to apply fixes")