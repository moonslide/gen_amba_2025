#!/usr/bin/env python3
"""
ULTRATHINK SLAVE SIGNAL FIX

Current Status:
- Master 2 gets grant ✓
- Master 2 owns write channel ✓
- But slave BFM never receives Master 2's transaction ✗

Root Cause:
The slave output signals (s0_awvalid, s0_awid, etc.) are not being
properly driven when Master 2 has the grant. The issue is in how
the interconnect routes Master 2's signals to Slave 0.

Solution:
Fix the signal assignments from Master 2 to Slave 0.
"""

import re
import os
import shutil
import time

def apply_slave_signal_fix():
    """Fix slave signal routing for Master 2"""
    print("🎯 ULTRATHINK SLAVE SIGNAL FIX")
    print("=" * 60)
    
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    # Backup current state
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    backup_file = rtl_file + f".backup_signal_fix_{timestamp}"
    shutil.copy(rtl_file, backup_file)
    print(f"✅ Backup created: {backup_file}")
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("\n📋 PROBLEM:")
    print("  • Master 2 owns channel but slave sees nothing")
    print("  • s0_awvalid not driven when grant=2")
    print("  • Need to fix signal multiplexing")
    
    fixes = []
    
    # Fix s0_awvalid to properly include Master 2
    print("\n🔧 Fixing s0_awvalid assignment...")
    
    # Find current s0_awvalid assignment
    awvalid_pattern = r'assign s0_awvalid = \n.*?;'
    awvalid_match = re.search(awvalid_pattern, content, re.DOTALL)
    
    if awvalid_match:
        old_awvalid = awvalid_match.group(0)
        
        # Check if it's using grant-based multiplexing
        if "s0_aw_grant" in old_awvalid:
            print("  Found grant-based awvalid mux")
            
            # Make sure Master 2 is properly included
            new_awvalid = """assign s0_awvalid = 
(s0_aw_grant == 4'd0) ? (m0_awvalid && (m0_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd1) ? (m1_awvalid && (m1_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd2) ? (m2_awvalid && (m2_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd3) ? (m3_awvalid && (m3_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd4) ? (m4_awvalid && (m4_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd5) ? (m5_awvalid && (m5_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd6) ? (m6_awvalid && (m6_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd7) ? (m7_awvalid && (m7_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd8) ? (m8_awvalid && (m8_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd9) ? (m9_awvalid && (m9_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd10) ? (m10_awvalid && (m10_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd11) ? (m11_awvalid && (m11_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd12) ? (m12_awvalid && (m12_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd13) ? (m13_awvalid && (m13_awaddr[63:13] == 51'd0)) :
(s0_aw_grant == 4'd14) ? (m14_awvalid && (m14_awaddr[63:13] == 51'd0)) : 1'b0;"""
            
            content = content.replace(old_awvalid, new_awvalid)
            fixes.append("Fixed s0_awvalid grant-based mux")
        else:
            print("  awvalid uses OR-based logic")
            # If it's OR-based, make sure Master 2 is included
            if "m2_awvalid" not in old_awvalid:
                fixes.append("ERROR: Master 2 not in awvalid!")
    
    # Fix s0_wvalid for write data
    print("\n🔧 Fixing s0_wvalid assignment...")
    
    wvalid_pattern = r'assign s0_wvalid = \n.*?;'
    wvalid_match = re.search(wvalid_pattern, content, re.DOTALL)
    
    if wvalid_match:
        old_wvalid = wvalid_match.group(0)
        
        # Use write ownership if available, else use grant
        if "s0_w_owner" in content:
            print("  Using write ownership for wvalid")
            new_wvalid = """assign s0_wvalid = 
(s0_w_active && (s0_w_owner == 4'd0)) ? m0_wvalid :
(s0_w_active && (s0_w_owner == 4'd1)) ? m1_wvalid :
(s0_w_active && (s0_w_owner == 4'd2)) ? m2_wvalid :
(s0_w_active && (s0_w_owner == 4'd3)) ? m3_wvalid :
(s0_w_active && (s0_w_owner == 4'd4)) ? m4_wvalid :
(s0_w_active && (s0_w_owner == 4'd5)) ? m5_wvalid :
(s0_w_active && (s0_w_owner == 4'd6)) ? m6_wvalid :
(s0_w_active && (s0_w_owner == 4'd7)) ? m7_wvalid :
(s0_w_active && (s0_w_owner == 4'd8)) ? m8_wvalid :
(s0_w_active && (s0_w_owner == 4'd9)) ? m9_wvalid :
(s0_w_active && (s0_w_owner == 4'd10)) ? m10_wvalid :
(s0_w_active && (s0_w_owner == 4'd11)) ? m11_wvalid :
(s0_w_active && (s0_w_owner == 4'd12)) ? m12_wvalid :
(s0_w_active && (s0_w_owner == 4'd13)) ? m13_wvalid :
(s0_w_active && (s0_w_owner == 4'd14)) ? m14_wvalid : 1'b0;"""
        else:
            print("  Using grant for wvalid")
            new_wvalid = """assign s0_wvalid = 
(s0_aw_grant == 4'd0) ? m0_wvalid :
(s0_aw_grant == 4'd1) ? m1_wvalid :
(s0_aw_grant == 4'd2) ? m2_wvalid :
(s0_aw_grant == 4'd3) ? m3_wvalid :
(s0_aw_grant == 4'd4) ? m4_wvalid :
(s0_aw_grant == 4'd5) ? m5_wvalid :
(s0_aw_grant == 4'd6) ? m6_wvalid :
(s0_aw_grant == 4'd7) ? m7_wvalid :
(s0_aw_grant == 4'd8) ? m8_wvalid :
(s0_aw_grant == 4'd9) ? m9_wvalid :
(s0_aw_grant == 4'd10) ? m10_wvalid :
(s0_aw_grant == 4'd11) ? m11_wvalid :
(s0_aw_grant == 4'd12) ? m12_wvalid :
(s0_aw_grant == 4'd13) ? m13_wvalid :
(s0_aw_grant == 4'd14) ? m14_wvalid : 1'b0;"""
        
        content = content.replace(old_wvalid, new_wvalid)
        fixes.append("Fixed s0_wvalid multiplexing")
    
    # Add debug to see what's happening
    print("\n🔧 Adding signal monitoring...")
    
    debug_block = """
// ULTRATHINK: Monitor slave signals
always @(posedge aclk) begin
    if (s0_awvalid && s0_awready) begin
        $display("[ULTRATHINK] Time %0t: S0 AW handshake - AWID=%0d, AWADDR=0x%0h, grant=%0d", 
                 $time, s0_awid, s0_awaddr, s0_aw_grant);
    end
    if (s0_wvalid && s0_wready && s0_wlast) begin
        $display("[ULTRATHINK] Time %0t: S0 WLAST received, owner=%0d", 
                 $time, s0_w_owner);
    end
    if (s0_bvalid && s0_bready) begin
        $display("[ULTRATHINK] Time %0t: S0 B response - BID=%0d, BRESP=%0d", 
                 $time, s0_bid, s0_bresp);
    end
end
"""
    
    # Add before endmodule if not present
    if "Monitor slave signals" not in content:
        endmodule_pos = content.rfind("endmodule")
        if endmodule_pos > 0:
            content = content[:endmodule_pos] + debug_block + "\n" + content[endmodule_pos:]
            fixes.append("Added slave signal monitoring")
    
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
    
    print("\n🧪 TESTING SLAVE SIGNAL FIX...")
    print("🔄 Cleaning...")
    os.system("make clean > /dev/null 2>&1")
    
    print("🔨 Compiling...")
    result = os.system("make compile 2>&1 | tail -10")
    
    if result == 0:
        print("✅ Compilation successful")
        
        print("🏃 Running test...")
        os.system("make run TEST=axi4_simple_crossbar_test > /dev/null 2>&1 &")
        
        # Wait for test completion
        time.sleep(25)
        
        print("\n" + "=" * 70)
        print("📊 ULTRATHINK FINAL TEST RESULTS")
        print("=" * 70)
        
        # Main result
        print("\n🎯 UVM ERROR COUNT:")
        os.system("grep 'UVM_ERROR :' logs/axi4_simple_crossbar_test_1.log")
        
        # Error details
        print("\n📍 ERROR DETAILS:")
        os.system("grep 'UVM_ERROR' logs/axi4_simple_crossbar_test_1.log | grep -v 'UVM_ERROR :' | grep -v 'demoted' | grep -v 'caught'")
        
        # Success indicators
        print("\n✅ SUCCESSFUL TRANSACTIONS:")
        os.system("grep 'B-channel response.*expect' logs/axi4_simple_crossbar_test_1.log")
        
        # Debug trace
        print("\n🔍 ULTRATHINK DEBUG TRACE:")
        os.system("grep '\\[ULTRATHINK\\]' logs/axi4_simple_crossbar_test_1.log | tail -20")
        
        # Slave responses
        print("\n📡 SLAVE RESPONSES:")
        os.system("grep 'Write response: BID=' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n" + "=" * 70)
        print("🏆 SUCCESS = UVM_ERROR : 0")
        print("=" * 70)
        
        return True
    else:
        print("❌ Compilation failed")
        return False

if __name__ == "__main__":
    print("🚀 ULTRATHINK SLAVE SIGNAL FIX")
    print("=" * 60)
    print("Fixing slave interface signal routing for Master 2")
    print()
    
    if apply_slave_signal_fix():
        print("\n✅ Slave signal fix applied")
        
        if compile_and_test():
            print("\n🏁 Test completed - check results above!")
        else:
            print("\n⚠️ Test execution failed")
    else:
        print("\n❌ Failed to apply fixes")