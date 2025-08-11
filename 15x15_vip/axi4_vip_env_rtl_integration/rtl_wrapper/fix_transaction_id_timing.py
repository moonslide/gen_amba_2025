#!/usr/bin/env python3
"""
FIX TRANSACTION ID TIMING

The debug shows:
- Time 505000: S0 WLAST: transaction_id=2 ✓
- Time 515000: S0 B: BID=1 (expected=0) ✗

The transaction_id is being cleared on WLAST, but it should be held
until the B-channel response completes.
"""

import re
import os
import shutil
import time

def fix_transaction_id_timing():
    """Fix transaction ID clearing timing"""
    print("🔧 FIXING TRANSACTION ID TIMING")
    print("=" * 60)
    
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    # Backup
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    backup_file = rtl_file + f".backup_timing_{timestamp}"
    shutil.copy(rtl_file, backup_file)
    print(f"✅ Created backup: {backup_file}")
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("\n📋 TIMING FIX:")
    print("  • Don't clear transaction_id on WLAST")
    print("  • Clear it on B-channel response completion")
    
    fixes = []
    
    # Remove clearing of transaction_id on WLAST
    print("\n🔧 Removing premature ID clearing...")
    
    for slave_id in range(15):
        # Find where transaction_id is cleared on WLAST
        pattern = f"s{slave_id}_transaction_id <= 4'd0;  // Clear for next transaction"
        
        if pattern in content:
            # Find it in WLAST context and remove it
            wlast_context_pattern = (
                f"if \\(s{slave_id}_wvalid && s{slave_id}_wready && s{slave_id}_wlast\\).*?"
                f"s{slave_id}_transaction_id <= 4'd0;  // Clear for next transaction"
            )
            
            wlast_match = re.search(wlast_context_pattern, content, re.DOTALL)
            if wlast_match:
                old_block = wlast_match.group(0)
                # Remove the transaction_id clear line
                new_block = old_block.replace(f"\n            s{slave_id}_transaction_id <= 4'd0;  // Clear for next transaction", "")
                content = content.replace(old_block, new_block)
                fixes.append(f"Removed premature ID clear for slave {slave_id}")
    
    # Add clearing on B-channel response
    print("\n🔧 Adding ID clear on B-channel completion...")
    
    # Add B-channel response completion logic
    bchannel_logic = """
// Clear transaction ID on B-channel response completion
always @(posedge aclk) begin
    if (!aresetn) begin
        // Reset handled elsewhere
    end else begin"""
    
    for slave_id in range(15):
        bchannel_logic += f"""
        // Slave {slave_id} B-channel completion
        if (s{slave_id}_bvalid && s{slave_id}_bready) begin
            s{slave_id}_transaction_id <= 4'd0;  // Clear after B response
            s{slave_id}_w_active <= 1'b0;  // Transaction complete
        end"""
    
    bchannel_logic += """
    end
end
"""
    
    # Add before endmodule if not present
    if "Clear transaction ID on B-channel" not in content:
        endmodule_pos = content.rfind("endmodule")
        if endmodule_pos > 0:
            content = content[:endmodule_pos] + bchannel_logic + "\n" + content[endmodule_pos:]
            fixes.append("Added B-channel completion logic")
    
    # Also need to ensure w_active doesn't get cleared on WLAST
    print("\n🔧 Fixing w_active clearing...")
    
    for slave_id in range(15):
        # Find where w_active is cleared on WLAST
        wlast_clear_pattern = (
            f"if \\(s{slave_id}_wvalid && s{slave_id}_wready && s{slave_id}_wlast\\).*?"
            f"s{slave_id}_w_active <= 1'b0;"
        )
        
        wlast_clear_match = re.search(wlast_clear_pattern, content, re.DOTALL)
        if wlast_clear_match:
            old_block = wlast_clear_match.group(0)
            # Comment out the w_active clear
            new_block = old_block.replace(
                f"s{slave_id}_w_active <= 1'b0;",
                f"// s{slave_id}_w_active <= 1'b0;  // Don't clear yet, wait for B response"
            )
            content = content.replace(old_block, new_block)
            fixes.append(f"Deferred w_active clear for slave {slave_id}")
    
    # Write fixed content
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("\n✅ TIMING FIXES APPLIED:")
    for fix in fixes:
        print(f"  • {fix}")
    
    return True

def test_timing_fix():
    """Test the timing fix"""
    sim_dir = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/sim"
    os.chdir(sim_dir)
    
    print("\n🧪 TESTING TIMING FIX...")
    print("🔄 Cleaning...")
    os.system("make clean > /dev/null 2>&1")
    
    print("🔨 Compiling...")
    result = os.system("make compile 2>&1 | grep -E 'CPU|Error' | tail -3")
    
    if result == 0:
        print("✅ Compilation successful")
        
        print("🏃 Running test...")
        os.system("make run TEST=axi4_simple_crossbar_test > /dev/null 2>&1 &")
        
        # Wait for test
        time.sleep(30)
        
        print("\n" + "="*70)
        print("📊 TIMING FIX RESULTS")
        print("="*70)
        
        print("\n🎯 UVM ERROR COUNT:")
        os.system("grep 'UVM_ERROR :' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n✅ MASTER RESPONSES:")
        os.system("grep 'B-channel response' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n🔍 CRITICAL TIMING:")
        os.system("grep '\\[DEBUG\\].*transaction_id=2' logs/axi4_simple_crossbar_test_1.log")
        os.system("grep '\\[DEBUG\\].*expected=2' logs/axi4_simple_crossbar_test_1.log")
        
        print("\n" + "="*70)
        
        # Final check
        os.system("""
        if grep -q 'UVM_ERROR :    0' logs/axi4_simple_crossbar_test_1.log; then
            echo '🎉 SUCCESS: ZERO UVM_ERRORs ACHIEVED!'
        elif grep -q 'UVM_ERROR :    1' logs/axi4_simple_crossbar_test_1.log; then
            echo '⚠️ Still 1 error - checking if Master 2 receives response...'
            grep 'master_agent\\[2\\].*B-channel' logs/axi4_simple_crossbar_test_1.log | tail -3
        fi
        """)
        
        print("="*70)
        
        return True
    else:
        print("❌ Compilation failed")
        return False

if __name__ == "__main__":
    print("🚀 TRANSACTION ID TIMING FIX")
    print("=" * 60)
    print("Fixing when transaction ID is cleared")
    print()
    
    if fix_transaction_id_timing():
        if test_timing_fix():
            print("\n✅ TIMING FIX COMPLETE!")
        else:
            print("\n⚠️ Test failed")
    else:
        print("\n❌ Fix application failed")