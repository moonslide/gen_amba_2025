#\!/usr/bin/env python3
"""
ULTRATHINK FINAL FIX - The Real Root Cause

After all the debugging, the issue is now crystal clear:
1. Master 2 successfully sends AWID=2 to Slave 0 ✓
2. Slave 0 processes the transaction (WLAST received) ✓
3. But Slave 0 responds with BID=1 instead of BID=2 ✗

The problem is that there are TWO transactions happening:
- At T=235000: Master 1 → Slave 0 (AWID=1)
- At T=445000: Master 2 → Slave 0 (AWID=2)

But the slave BFM only sends one response with BID=1 at T=505000.
This response should be BID=2 for Master 2, not BID=1.

Root Cause: The slave is using the wrong AWID when generating the response.
It's using AWID from an earlier transaction instead of the current one.

Solution: Ensure s0_awid is properly held throughout the transaction.
"""

import re
import os
import shutil
import time

def apply_final_fix():
    """Apply the final fix for Master 2 BID issue"""
    print("🎯 ULTRATHINK FINAL FIX - ID TRACKING")
    print("=" * 60)
    
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    # Backup current state
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    backup_file = rtl_file + f".backup_final_{timestamp}"
    shutil.copy(rtl_file, backup_file)
    print(f"✅ Backup created: {backup_file}")
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("\n📋 THE REAL ISSUE:")
    print("  • Slave sends BID=1 for Master 2's transaction")
    print("  • Should send BID=2")
    print("  • AWID not properly tracked through transaction")
    
    fixes = []
    
    # Add AWID tracking registers
    print("\n🔧 Adding AWID tracking registers...")
    
    # Find where to add registers
    reg_section = re.search(r'(reg\s+\[3:0\]\s+s0_w_owner;)', content)
    
    if reg_section:
        # Add AWID tracking register
        if "s0_awid_latched" not in content:
            insert_pos = reg_section.end()
            awid_reg = "\nreg [3:0] s0_awid_latched;  // ULTRATHINK: Track AWID through transaction\n"
            content = content[:insert_pos] + awid_reg + content[insert_pos:]
            fixes.append("Added AWID tracking register")
    
    # Initialize the register
    print("\n🔧 Initializing AWID tracking...")
    
    reset_pattern = "s0_w_owner <= 4'd0;"
    reset_pos = content.find(reset_pattern)
    
    if reset_pos > 0 and "s0_awid_latched <= 4'd0;" not in content:
        init_text = "\n        s0_awid_latched <= 4'd0;"
        content = content[:reset_pos + len(reset_pattern)] + init_text + content[reset_pos + len(reset_pattern):]
        fixes.append("Added AWID register initialization")
    
    # Latch AWID on AW handshake
    print("\n🔧 Latching AWID on AW handshake...")
    
    # Find where we capture write ownership
    ownership_pattern = "s0_w_owner <= s0_aw_grant;"
    ownership_pos = content.find(ownership_pattern)
    
    if ownership_pos > 0 and "s0_awid_latched <= s0_awid;" not in content:
        # Add AWID latching
        latch_text = "\n            s0_awid_latched <= s0_awid;  // ULTRATHINK: Latch AWID for B response"
        content = content[:ownership_pos + len(ownership_pattern)] + latch_text + content[ownership_pos + len(ownership_pattern):]
        fixes.append("Added AWID latching on AW handshake")
    
    # Use latched AWID for BID
    print("\n🔧 Using latched AWID for BID...")
    
    # Find s0_bid assignment
    bid_pattern = r'assign s0_bid = .*?;'
    bid_match = re.search(bid_pattern, content, re.DOTALL)
    
    if bid_match:
        old_bid = bid_match.group(0)
        
        # Use latched AWID when write is active
        if "s0_awid_latched" not in old_bid:
            new_bid = "assign s0_bid = s0_w_active ? s0_awid_latched : s0_awid;  // ULTRATHINK: Use latched AWID for BID"
            content = content.replace(old_bid, new_bid)
            fixes.append("Modified s0_bid to use latched AWID")
    
    # Alternative simpler fix: Ensure s0_awid stays stable
    print("\n🔧 Alternative: Ensuring AWID stability...")
    
    # Make s0_awid hold its value during write
    awid_pattern = r'assign s0_awid = \n.*?;'
    awid_match = re.search(awid_pattern, content, re.DOTALL)
    
    if awid_match:
        old_awid = awid_match.group(0)
        
        # Only update AWID when not in active write
        if "s0_w_active" not in old_awid:
            # Build new assignment that holds AWID during write
            new_awid = """assign s0_awid = 
// ULTRATHINK: Hold AWID stable during write transaction
s0_w_active ? s0_awid_latched :
(s0_aw_grant == 4'd0) ? m0_awid :
(s0_aw_grant == 4'd1) ? m1_awid :
(s0_aw_grant == 4'd2) ? m2_awid :
(s0_aw_grant == 4'd3) ? m3_awid :
(s0_aw_grant == 4'd4) ? m4_awid :
(s0_aw_grant == 4'd5) ? m5_awid :
(s0_aw_grant == 4'd6) ? m6_awid :
(s0_aw_grant == 4'd7) ? m7_awid :
(s0_aw_grant == 4'd8) ? m8_awid :
(s0_aw_grant == 4'd9) ? m9_awid :
(s0_aw_grant == 4'd10) ? m10_awid :
(s0_aw_grant == 4'd11) ? m11_awid :
(s0_aw_grant == 4'd12) ? m12_awid :
(s0_aw_grant == 4'd13) ? m13_awid :
(s0_aw_grant == 4'd14) ? m14_awid : 4'd0;"""
            
            content = content.replace(old_awid, new_awid)
            fixes.append("Modified s0_awid to hold value during write")
    
    # Clear latched AWID on transaction complete
    print("\n🔧 Clearing latched AWID on completion...")
    
    # Find where we clear write active
    clear_pattern = "s0_w_active <= 1'b0;"
    clear_pos = content.find(clear_pattern)
    
    if clear_pos > 0:
        # Check if we need to add clear
        check_range = content[clear_pos-100:clear_pos+200]
        if "s0_awid_latched <= 4'd0;" not in check_range and "s0_awid_latched" in content:
            clear_text = "\n            s0_awid_latched <= 4'd0;  // Clear for next transaction"
            content = content[:clear_pos + len(clear_pattern)] + clear_text + content[clear_pos + len(clear_pattern):]
            fixes.append("Added AWID clear on transaction complete")
    
    # Write the fixed content
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("\n✅ FIXES APPLIED:")
    for fix in fixes:
        print(f"  • {fix}")
    
    return True

def compile_and_test():
    """Final test run"""
    sim_dir = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/sim"
    os.chdir(sim_dir)
    
    print("\n🧪 FINAL TEST RUN...")
    print("🔄 Cleaning...")
    os.system("make clean > /dev/null 2>&1")
    
    print("🔨 Compiling...")
    result = os.system("make compile 2>&1 | tail -10")
    
    if result == 0:
        print("✅ Compilation successful")
        
        print("🏃 Running final test...")
        os.system("make run TEST=axi4_simple_crossbar_test > /dev/null 2>&1 &")
        
        # Wait for test completion
        time.sleep(30)
        
        print("\n" + "=" * 70)
        print("🏆 ULTRATHINK FINAL RESULTS")
        print("=" * 70)
        
        # THE MOMENT OF TRUTH
        print("\n🎯 UVM ERROR COUNT (Target = 0):")
        os.system("grep 'UVM_ERROR :' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n✅ MASTER TRANSACTIONS:")
        os.system("grep 'B-channel response.*expect' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n📡 SLAVE BID RESPONSES:")
        os.system("grep 'Write response: BID=' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n🔍 CRITICAL DEBUG:")
        os.system("grep '\\[ULTRATHINK\\].*S0.*BID' logs/axi4_simple_crossbar_test_1.log | tail -5")
        
        # Check for success
        print("\n" + "=" * 70)
        os.system("grep -q 'UVM_ERROR :    0' logs/axi4_simple_crossbar_test_1.log && echo '🎉 SUCCESS\! Zero UVM_ERRORs achieved\!' || echo '⚠️ Still have errors - check trace above'")
        print("=" * 70)
        
        return True
    else:
        print("❌ Compilation failed")
        return False

if __name__ == "__main__":
    print("🚀 ULTRATHINK FINAL FIX")
    print("=" * 60)
    print("Fixing AWID tracking for correct BID response")
    print()
    
    if apply_final_fix():
        print("\n✅ Final fix applied")
        
        if compile_and_test():
            print("\n🏁 FINAL TEST COMPLETE\!")
        else:
            print("\n⚠️ Test execution failed")
    else:
        print("\n❌ Failed to apply fixes")
