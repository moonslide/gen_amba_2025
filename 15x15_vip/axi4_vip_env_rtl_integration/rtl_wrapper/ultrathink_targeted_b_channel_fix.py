#!/usr/bin/env python3
"""
ULTRATHINK TARGETED B-CHANNEL FIX

After analysis, the issue is clear:
- Master 2 completes WLAST successfully
- But Slave 0 never sends B-channel response with BID=2
- The issue is in the B-channel response path

Looking at the logs:
- Slave BFM sends BID=0 for Master 0 ✓
- Slave BFM sends BID=1 for Master 1 ✓  
- Slave BFM never sends BID=2 for Master 2 ✗

The problem: Slave 0's bvalid/bid signals aren't reaching Master 2
"""

import re

def apply_targeted_b_channel_fix():
    """Apply targeted fix for Master 2 B-channel"""
    print("🎯 ULTRATHINK TARGETED B-CHANNEL FIX")
    print("=" * 60)
    
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("📋 TARGETED ANALYSIS:")
    print("  • Master 0 receives BID=0 ✓")
    print("  • Master 1 receives BID=1 ✓")  
    print("  • Master 2 never receives BID=2 ✗")
    print("  • Fix: Ensure BID=2 routes to Master 2")
    
    fixes = []
    
    # FIX 1: Check Master 2's B-channel routing
    print("\n🔧 Checking Master 2 B-channel routing...")
    
    # Find m2_bvalid assignment
    m2_bvalid_pattern = r'assign m2_bvalid = \n\(s0_bvalid && \(s0_bid\[3:0\] == 4\'d2\)\)'
    
    if re.search(m2_bvalid_pattern, content):
        print("  ✅ Basic routing exists")
        
        # Enhance it to handle more cases
        old_m2_bvalid = re.search(r'assign m2_bvalid = \n.*?\);', content, re.DOTALL)
        if old_m2_bvalid:
            old_text = old_m2_bvalid.group(0)
            
            # Check if it already has our previous fixes
            if "(s0_bid == 10)" in old_text:
                print("  ✅ ID=10 routing already added")
            else:
                # Add comprehensive BID checking
                new_m2_bvalid = """assign m2_bvalid = 
// ULTRATHINK: Comprehensive BID routing for Master 2
(s0_bvalid && ((s0_bid[3:0] == 4'd2) || (s0_bid == 4'd2))) |
(s1_bvalid && ((s1_bid[3:0] == 4'd2) || (s1_bid == 4'd2))) |
(s2_bvalid && ((s2_bid[3:0] == 4'd2) || (s2_bid == 4'd2))) |
(s3_bvalid && ((s3_bid[3:0] == 4'd2) || (s3_bid == 4'd2))) |
(s4_bvalid && ((s4_bid[3:0] == 4'd2) || (s4_bid == 4'd2))) |
(s5_bvalid && ((s5_bid[3:0] == 4'd2) || (s5_bid == 4'd2))) |
(s6_bvalid && ((s6_bid[3:0] == 4'd2) || (s6_bid == 4'd2))) |
(s7_bvalid && ((s7_bid[3:0] == 4'd2) || (s7_bid == 4'd2))) |
(s8_bvalid && ((s8_bid[3:0] == 4'd2) || (s8_bid == 4'd2))) |
(s9_bvalid && ((s9_bid[3:0] == 4'd2) || (s9_bid == 4'd2))) |
(s10_bvalid && ((s10_bid[3:0] == 4'd2) || (s10_bid == 4'd2))) |
(s11_bvalid && ((s11_bid[3:0] == 4'd2) || (s11_bid == 4'd2))) |
(s12_bvalid && ((s12_bid[3:0] == 4'd2) || (s12_bid == 4'd2))) |
(s13_bvalid && ((s13_bid[3:0] == 4'd2) || (s13_bid == 4'd2))) |
(s14_bvalid && ((s14_bid[3:0] == 4'd2) || (s14_bid == 4'd2)));"""
                
                content = content.replace(old_text, new_m2_bvalid)
                fixes.append("Enhanced BID=2 routing for all slaves")
    
    # FIX 2: Ensure s0_bid is properly connected
    print("🔧 Checking slave 0 BID connection...")
    
    # Check if s0_bid is assigned from slave
    s0_bid_pattern = r'assign s0_bid = '
    if not re.search(s0_bid_pattern, content):
        print("  ⚠️ s0_bid assignment not found - this is critical!")
        # s0_bid should come directly from the slave interface
        # This would be in dut_wrapper.sv, not here
    else:
        print("  ✅ s0_bid assignment exists")
    
    # FIX 3: Add debug visibility
    print("🔧 Adding debug signals...")
    
    # Add always block to monitor B-channel
    debug_block = """
// ULTRATHINK DEBUG: Monitor B-channel transactions
always @(posedge aclk) begin
    if (s0_bvalid && s0_bready) begin
        $display("[ULTRATHINK] Time %0t: S0 B-channel: BID=%0d BRESP=%0d", $time, s0_bid, s0_bresp);
    end
    if (m2_bvalid && m2_bready) begin
        $display("[ULTRATHINK] Time %0t: M2 B-channel: BID=%0d BRESP=%0d", $time, m2_bid, m2_bresp);
    end
end
"""
    
    # Add before endmodule if not already present
    if "[ULTRATHINK]" not in content:
        endmodule_pos = content.rfind("endmodule")
        if endmodule_pos > 0:
            content = content[:endmodule_pos] + debug_block + "\n" + content[endmodule_pos:]
            fixes.append("Added B-channel debug monitoring")
    
    # FIX 4: Ensure m2_bid gets the right value
    print("🔧 Checking Master 2 BID routing...")
    
    # Find m2_bid assignment
    m2_bid_pattern = r'assign m2_bid = '
    m2_bid_match = re.search(m2_bid_pattern + r'.*?;', content, re.DOTALL)
    
    if m2_bid_match:
        old_bid = m2_bid_match.group(0)
        if "s0_bid" in old_bid:
            print("  ✅ m2_bid receives from s0_bid")
        else:
            print("  ⚠️ m2_bid routing may be incorrect")
    
    # Write the fixed content
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("\n✅ TARGETED FIXES APPLIED:")
    for fix in fixes:
        print(f"  • {fix}")
    
    return True

def test_fix():
    """Quick test of the fix"""
    import os
    import time
    
    sim_dir = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/sim"
    os.chdir(sim_dir)
    
    print("\n🧪 TESTING TARGETED FIX...")
    
    # Clean and compile
    print("🔄 Cleaning...")
    os.system("make clean > /dev/null 2>&1")
    
    print("🔨 Compiling...")
    result = os.system("make compile 2>&1 | tail -5")
    
    if result == 0:
        print("✅ Compilation successful")
        
        print("🏃 Running test...")
        os.system("make run TEST=axi4_simple_crossbar_test > /dev/null 2>&1 &")
        
        # Wait for test
        time.sleep(15)
        
        # Check for errors
        os.system("grep 'UVM_ERROR' logs/axi4_simple_crossbar_test_1.log | tail -5")
        
        return True
    else:
        print("❌ Compilation failed")
        return False

if __name__ == "__main__":
    print("🚀 ULTRATHINK TARGETED B-CHANNEL FIX")
    print("=" * 60)
    
    if apply_targeted_b_channel_fix():
        print("\n✅ Targeted fixes applied")
        
        if test_fix():
            print("\n📊 Test completed - check results above")
        else:
            print("\n⚠️ Test failed")
    else:
        print("\n❌ Failed to apply fixes")