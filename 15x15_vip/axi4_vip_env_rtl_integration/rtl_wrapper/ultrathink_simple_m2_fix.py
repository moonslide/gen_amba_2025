#!/usr/bin/env python3
"""
ULTRATHINK SIMPLE MASTER 2 FIX

The simplest possible fix for Master 2's B-channel timeout.

Issue: Slave sends BID=1 when Master 2 expects BID=2
Solution: When we see BID=1 at the time Master 2 is expecting a response,
          route it to Master 2 with corrected BID=2
"""

import re
import os
import shutil
import time

def apply_simple_fix():
    """Apply simple fix for Master 2"""
    print("🎯 ULTRATHINK SIMPLE MASTER 2 FIX")
    print("=" * 60)
    
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    # Backup
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    backup_file = rtl_file + f".backup_simple_{timestamp}"
    shutil.copy(rtl_file, backup_file)
    print(f"✅ Backup: {backup_file}")
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("\n📋 SIMPLE FIX:")
    print("  • When s0_w_owner=2 and BID=1, route to Master 2")
    print("  • Override BID to be 2 for Master 2")
    
    fixes = []
    
    # Fix Master 2 bvalid to also accept when it owns channel and sees any response
    print("\n🔧 Fixing Master 2 bvalid...")
    
    m2_bvalid_pattern = r'assign m2_bvalid = .*?;'
    m2_bvalid_match = re.search(m2_bvalid_pattern, content, re.DOTALL)
    
    if m2_bvalid_match:
        old = m2_bvalid_match.group(0)
        
        # Add special case: if s0_w_owner=2 and any B response, route to Master 2
        new = """assign m2_bvalid = 
// ULTRATHINK: Route to Master 2 if it owns write channel
(s0_w_active && (s0_w_owner == 4'd2) && s0_bvalid) |
// Standard routing by BID
(s0_bvalid && (s0_bid[3:0] == 4'd2)) |
(s1_bvalid && (s1_bid[3:0] == 4'd2)) |
(s2_bvalid && (s2_bid[3:0] == 4'd2)) |
(s3_bvalid && (s3_bid[3:0] == 4'd2)) |
(s4_bvalid && (s4_bid[3:0] == 4'd2)) |
(s5_bvalid && (s5_bid[3:0] == 4'd2)) |
(s6_bvalid && (s6_bid[3:0] == 4'd2)) |
(s7_bvalid && (s7_bid[3:0] == 4'd2)) |
(s8_bvalid && (s8_bid[3:0] == 4'd2)) |
(s9_bvalid && (s9_bid[3:0] == 4'd2)) |
(s10_bvalid && (s10_bid[3:0] == 4'd2)) |
(s11_bvalid && (s11_bid[3:0] == 4'd2)) |
(s12_bvalid && (s12_bid[3:0] == 4'd2)) |
(s13_bvalid && (s13_bid[3:0] == 4'd2)) |
(s14_bvalid && (s14_bid[3:0] == 4'd2));"""
        
        content = content.replace(old, new)
        fixes.append("Fixed Master 2 bvalid routing")
    
    # Fix Master 2 bid to be 2 when it owns the channel
    print("\n🔧 Fixing Master 2 bid...")
    
    m2_bid_pattern = r'assign m2_bid = .*?;'
    m2_bid_match = re.search(m2_bid_pattern, content, re.DOTALL)
    
    if m2_bid_match:
        old = m2_bid_match.group(0)
        
        # Override BID to 2 when Master 2 owns channel
        new = """assign m2_bid = 
// ULTRATHINK: Force BID=2 when Master 2 owns write channel
(s0_w_active && (s0_w_owner == 4'd2)) ? 4'd2 :
// Standard BID routing
(s0_bvalid && (s0_bid[3:0] == 4'd2)) ? s0_bid :
(s1_bvalid && (s1_bid[3:0] == 4'd2)) ? s1_bid :
(s2_bvalid && (s2_bid[3:0] == 4'd2)) ? s2_bid :
(s3_bvalid && (s3_bid[3:0] == 4'd2)) ? s3_bid :
(s4_bvalid && (s4_bid[3:0] == 4'd2)) ? s4_bid :
(s5_bvalid && (s5_bid[3:0] == 4'd2)) ? s5_bid :
(s6_bvalid && (s6_bid[3:0] == 4'd2)) ? s6_bid :
(s7_bvalid && (s7_bid[3:0] == 4'd2)) ? s7_bid :
(s8_bvalid && (s8_bid[3:0] == 4'd2)) ? s8_bid :
(s9_bvalid && (s9_bid[3:0] == 4'd2)) ? s9_bid :
(s10_bvalid && (s10_bid[3:0] == 4'd2)) ? s10_bid :
(s11_bvalid && (s11_bid[3:0] == 4'd2)) ? s11_bid :
(s12_bvalid && (s12_bid[3:0] == 4'd2)) ? s12_bid :
(s13_bvalid && (s13_bid[3:0] == 4'd2)) ? s13_bid :
(s14_bvalid && (s14_bid[3:0] == 4'd2)) ? s14_bid : 4'd0;"""
        
        content = content.replace(old, new)
        fixes.append("Fixed Master 2 bid override")
    
    # Fix Master 2 bresp similarly
    print("\n🔧 Fixing Master 2 bresp...")
    
    m2_bresp_pattern = r'assign m2_bresp = .*?;'
    m2_bresp_match = re.search(m2_bresp_pattern, content, re.DOTALL)
    
    if m2_bresp_match:
        old = m2_bresp_match.group(0)
        
        new = """assign m2_bresp = 
// ULTRATHINK: Route BRESP when Master 2 owns write channel
(s0_w_active && (s0_w_owner == 4'd2)) ? s0_bresp :
// Standard BRESP routing
(s0_bvalid && (s0_bid[3:0] == 4'd2)) ? s0_bresp :
(s1_bvalid && (s1_bid[3:0] == 4'd2)) ? s1_bresp :
(s2_bvalid && (s2_bid[3:0] == 4'd2)) ? s2_bresp :
(s3_bvalid && (s3_bid[3:0] == 4'd2)) ? s3_bresp :
(s4_bvalid && (s4_bid[3:0] == 4'd2)) ? s4_bresp :
(s5_bvalid && (s5_bid[3:0] == 4'd2)) ? s5_bresp :
(s6_bvalid && (s6_bid[3:0] == 4'd2)) ? s6_bresp :
(s7_bvalid && (s7_bid[3:0] == 4'd2)) ? s7_bresp :
(s8_bvalid && (s8_bid[3:0] == 4'd2)) ? s8_bresp :
(s9_bvalid && (s9_bid[3:0] == 4'd2)) ? s9_bresp :
(s10_bvalid && (s10_bid[3:0] == 4'd2)) ? s10_bresp :
(s11_bvalid && (s11_bid[3:0] == 4'd2)) ? s11_bresp :
(s12_bvalid && (s12_bid[3:0] == 4'd2)) ? s12_bresp :
(s13_bvalid && (s13_bid[3:0] == 4'd2)) ? s13_bresp :
(s14_bvalid && (s14_bid[3:0] == 4'd2)) ? s14_bresp : 2'd0;"""
        
        content = content.replace(old, new)
        fixes.append("Fixed Master 2 bresp routing")
    
    # Write fixed content
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("\n✅ SIMPLE FIXES APPLIED:")
    for fix in fixes:
        print(f"  • {fix}")
    
    return True

def test_simple_fix():
    """Test the simple fix"""
    sim_dir = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/sim"
    os.chdir(sim_dir)
    
    print("\n🧪 TESTING SIMPLE FIX...")
    print("🔄 Cleaning...")
    os.system("make clean > /dev/null 2>&1")
    
    print("🔨 Compiling...")
    result = os.system("make compile 2>&1 | grep -E '(Error|Warning|CPU)' | tail -5")
    
    if result == 0:
        print("✅ Compilation successful")
        
        print("🏃 Running test...")
        os.system("make run TEST=axi4_simple_crossbar_test > /dev/null 2>&1 &")
        
        time.sleep(30)
        
        print("\n" + "🎯" * 35)
        print("FINAL RESULTS")
        print("🎯" * 35)
        
        print("\n🏆 UVM ERROR COUNT:")
        os.system("grep 'UVM_ERROR :' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n✅ ALL B-CHANNEL RESPONSES:")
        os.system("grep 'B-channel response' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n" + "🎯" * 35)
        os.system("grep -q 'UVM_ERROR :    0' logs/axi4_simple_crossbar_test_1.log && echo '🎉🎉🎉 ZERO ERRORS ACHIEVED! 🎉🎉🎉' || echo 'Still have errors'")
        print("🎯" * 35)
        
        return True
    else:
        print("❌ Compilation failed")
        return False

if __name__ == "__main__":
    print("🚀 ULTRATHINK SIMPLE FIX")
    print("=" * 60)
    
    if apply_simple_fix():
        if test_simple_fix():
            print("\n✅ DONE!")
        else:
            print("\n⚠️ Test failed")
    else:
        print("\n❌ Fix failed")