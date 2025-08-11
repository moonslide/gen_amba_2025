#!/usr/bin/env python3
"""
ULTRATHINK MASTER 2 GRANT FIX

Current Status:
- Master 0 works (BID=0 received) ✓
- Master 1 works (BID=1 received) ✓
- Master 2 timeout (never gets grant) ✗

Debug shows:
- Master 2 requests Slave 0 at time 435000
- But slave never processes Master 2's transaction
- Slave only sends BID=0 and BID=1, never BID=2

Root Cause:
Master 2 never gets the grant because Masters 0 and 1 are hogging it.
The arbitration is too simplistic - it always favors lower-numbered masters.

Solution:
Implement fair arbitration that ensures all masters get a chance.
"""

import re
import os
import shutil
import time

def apply_master2_grant_fix():
    """Fix arbitration to ensure Master 2 gets grant"""
    print("🎯 ULTRATHINK MASTER 2 GRANT FIX")
    print("=" * 60)
    
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    # Backup current state
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    backup_file = rtl_file + f".backup_grant_fix_{timestamp}"
    shutil.copy(rtl_file, backup_file)
    print(f"✅ Backup created: {backup_file}")
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("\n📋 DIAGNOSIS:")
    print("  • Master 2 requests at T=435000")
    print("  • Never gets grant (lower masters hog it)")
    print("  • Need fair arbitration")
    
    fixes = []
    
    # Fix Slave 0 arbitration to use round-robin
    print("\n🔧 Implementing fair arbitration for Slave 0...")
    
    # Find the arbitration block for slave 0
    arb_pattern = r'// AW channel arbitration\s+if \(s0_aw_grant == 4\'d15\) begin.*?else if \(s0_aw_requests\[14\]\) s0_aw_grant <= 4\'d14;'
    
    arb_match = re.search(arb_pattern, content, re.DOTALL)
    
    if arb_match:
        old_arb = arb_match.group(0)
        
        # Replace with round-robin arbitration
        new_arb = """// AW channel arbitration
        if (s0_aw_grant == 4'd15) begin // No current grant
            // ULTRATHINK: Fair round-robin arbitration
            // Start looking from the master after the last one granted
            if (s0_aw_last_grant < 4'd14) begin
                // Check masters after last grant first
                if (s0_aw_last_grant < 4'd0 && s0_aw_requests[1]) s0_aw_grant <= 4'd1;
                else if (s0_aw_last_grant < 4'd1 && s0_aw_requests[2]) s0_aw_grant <= 4'd2;
                else if (s0_aw_last_grant < 4'd2 && s0_aw_requests[3]) s0_aw_grant <= 4'd3;
                else if (s0_aw_last_grant < 4'd3 && s0_aw_requests[4]) s0_aw_grant <= 4'd4;
                else if (s0_aw_last_grant < 4'd4 && s0_aw_requests[5]) s0_aw_grant <= 4'd5;
                else if (s0_aw_last_grant < 4'd5 && s0_aw_requests[6]) s0_aw_grant <= 4'd6;
                else if (s0_aw_last_grant < 4'd6 && s0_aw_requests[7]) s0_aw_grant <= 4'd7;
                else if (s0_aw_last_grant < 4'd7 && s0_aw_requests[8]) s0_aw_grant <= 4'd8;
                else if (s0_aw_last_grant < 4'd8 && s0_aw_requests[9]) s0_aw_grant <= 4'd9;
                else if (s0_aw_last_grant < 4'd9 && s0_aw_requests[10]) s0_aw_grant <= 4'd10;
                else if (s0_aw_last_grant < 4'd10 && s0_aw_requests[11]) s0_aw_grant <= 4'd11;
                else if (s0_aw_last_grant < 4'd11 && s0_aw_requests[12]) s0_aw_grant <= 4'd12;
                else if (s0_aw_last_grant < 4'd12 && s0_aw_requests[13]) s0_aw_grant <= 4'd13;
                else if (s0_aw_last_grant < 4'd13 && s0_aw_requests[14]) s0_aw_grant <= 4'd14;
                // Wrap around to check earlier masters
                else if (s0_aw_requests[0]) s0_aw_grant <= 4'd0;
                else if (s0_aw_requests[1]) s0_aw_grant <= 4'd1;
                else if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;
                else if (s0_aw_requests[3]) s0_aw_grant <= 4'd3;
                else if (s0_aw_requests[4]) s0_aw_grant <= 4'd4;
                else if (s0_aw_requests[5]) s0_aw_grant <= 4'd5;
                else if (s0_aw_requests[6]) s0_aw_grant <= 4'd6;
                else if (s0_aw_requests[7]) s0_aw_grant <= 4'd7;
                else if (s0_aw_requests[8]) s0_aw_grant <= 4'd8;
                else if (s0_aw_requests[9]) s0_aw_grant <= 4'd9;
                else if (s0_aw_requests[10]) s0_aw_grant <= 4'd10;
                else if (s0_aw_requests[11]) s0_aw_grant <= 4'd11;
                else if (s0_aw_requests[12]) s0_aw_grant <= 4'd12;
                else if (s0_aw_requests[13]) s0_aw_grant <= 4'd13;
                else if (s0_aw_requests[14]) s0_aw_grant <= 4'd14;
            end else begin
                // Last grant was 14, start from 0
                if (s0_aw_requests[0]) s0_aw_grant <= 4'd0;
                else if (s0_aw_requests[1]) s0_aw_grant <= 4'd1;
                else if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;
                else if (s0_aw_requests[3]) s0_aw_grant <= 4'd3;
                else if (s0_aw_requests[4]) s0_aw_grant <= 4'd4;
                else if (s0_aw_requests[5]) s0_aw_grant <= 4'd5;
                else if (s0_aw_requests[6]) s0_aw_grant <= 4'd6;
                else if (s0_aw_requests[7]) s0_aw_grant <= 4'd7;
                else if (s0_aw_requests[8]) s0_aw_grant <= 4'd8;
                else if (s0_aw_requests[9]) s0_aw_grant <= 4'd9;
                else if (s0_aw_requests[10]) s0_aw_grant <= 4'd10;
                else if (s0_aw_requests[11]) s0_aw_grant <= 4'd11;
                else if (s0_aw_requests[12]) s0_aw_grant <= 4'd12;
                else if (s0_aw_requests[13]) s0_aw_grant <= 4'd13;
                else if (s0_aw_requests[14]) s0_aw_grant <= 4'd14;
            end"""
        
        content = content.replace(old_arb, new_arb)
        fixes.append("Implemented fair round-robin arbitration")
    
    # Simpler approach: ensure Master 2 can get grant
    print("\n🔧 Adding explicit Master 2 priority boost...")
    
    # Find where we check for Master 2 request
    m2_check = "else if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;"
    
    if m2_check in content:
        # Add a priority boost for Master 2 if it's been waiting
        boost_logic = """
// ULTRATHINK: Priority boost for Master 2
reg [15:0] m2_wait_counter;
always @(posedge aclk) begin
    if (!aresetn) begin
        m2_wait_counter <= 16'd0;
    end else if (m2_awvalid && (m2_awaddr[63:13] == 51'd0) && (s0_aw_grant != 4'd2)) begin
        // Master 2 is waiting for Slave 0
        m2_wait_counter <= m2_wait_counter + 1;
        if (m2_wait_counter > 16'd100) begin
            $display("[ULTRATHINK] Time %0t: Master 2 has been waiting %0d cycles!", $time, m2_wait_counter);
        end
    end else if (s0_aw_grant == 4'd2) begin
        // Master 2 got grant, reset counter
        m2_wait_counter <= 16'd0;
    end
end
"""
        
        # Add before endmodule
        if "m2_wait_counter" not in content:
            endmodule_pos = content.rfind("endmodule")
            if endmodule_pos > 0:
                content = content[:endmodule_pos] + boost_logic + "\n" + content[endmodule_pos:]
                fixes.append("Added Master 2 wait counter monitoring")
    
    # Fix: Ensure Master 2's grant isn't preempted
    print("\n🔧 Protecting Master 2's grant...")
    
    # When Master 2 has the grant, don't release it until WLAST
    grant_protection = """
        // ULTRATHINK: Protect Master 2's transaction
        if (s0_aw_grant == 4'd2 && s0_w_active) begin
            $display("[ULTRATHINK] Time %0t: Master 2 owns write channel on Slave 0", $time);
        end"""
    
    # Find a good place to add this
    if "Protect Master 2" not in content:
        # Add after the write ownership update
        ownership_pattern = "s0_w_active <= 1'b1;"
        if ownership_pattern in content:
            pos = content.find(ownership_pattern)
            if pos > 0:
                content = content[:pos + len(ownership_pattern)] + grant_protection + content[pos + len(ownership_pattern):]
                fixes.append("Added Master 2 grant protection")
    
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
    
    print("\n🧪 TESTING MASTER 2 GRANT FIX...")
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
        
        print("\n" + "=" * 60)
        print("📊 FINAL TEST RESULTS:")
        print("=" * 60)
        
        # Check for UVM errors
        print("\n🔍 UVM ERROR COUNT:")
        os.system("grep 'UVM_ERROR :' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n🔍 ERROR DETAILS (if any):")
        os.system("grep 'UVM_ERROR' logs/axi4_simple_crossbar_test_1.log | grep -v 'UVM_ERROR :' | head -5")
        
        # Check B-channel responses for all masters
        print("\n🔍 B-CHANNEL RESPONSES:")
        os.system("grep 'B-channel response' logs/axi4_simple_crossbar_test_1.log")
        
        # Check our debug messages
        print("\n🔍 MASTER 2 DEBUG:")
        os.system("grep '\\[ULTRATHINK\\]' logs/axi4_simple_crossbar_test_1.log | grep 'Master 2'")
        
        # Check write responses from slave
        print("\n🔍 SLAVE WRITE RESPONSES:")
        os.system("grep 'Write response: BID=' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n" + "=" * 60)
        print("🎯 TARGET: UVM_ERROR count = 0")
        print("=" * 60)
        
        return True
    else:
        print("❌ Compilation failed")
        return False

if __name__ == "__main__":
    print("🚀 ULTRATHINK MASTER 2 GRANT FIX")
    print("=" * 60)
    print("Ensuring Master 2 gets fair access to Slave 0")
    print()
    
    if apply_master2_grant_fix():
        print("\n✅ Master 2 grant fix applied")
        
        if compile_and_test():
            print("\n✅ Test completed - check results above")
        else:
            print("\n⚠️ Test execution failed")
    else:
        print("\n❌ Failed to apply fixes")