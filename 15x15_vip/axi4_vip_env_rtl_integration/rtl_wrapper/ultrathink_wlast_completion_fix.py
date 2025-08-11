#!/usr/bin/env python3
"""
ULTRATHINK WLAST COMPLETION FIX

ROOT CAUSE FOUND:
The grant is released immediately after AW handshake (awready && awvalid),
but it should be held until the write data phase completes (wlast).

This causes:
- Master sends AW, gets grant
- AW handshake completes, grant is released  
- Master tries to send W data, but no longer has grant
- WLAST never arrives, causing timeout

Solution:
Hold the grant until WLAST is received, not just AW handshake.
"""

import re
import os
import shutil
import time

def apply_wlast_completion_fix():
    """Fix grant release to wait for WLAST"""
    print("🎯 ULTRATHINK WLAST COMPLETION FIX")
    print("=" * 60)
    
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    # Backup current state
    timestamp = time.strftime("%Y%m%d_%H%M%S")
    backup_file = rtl_file + f".backup_wlast_fix_{timestamp}"
    shutil.copy(rtl_file, backup_file)
    print(f"✅ Backup created: {backup_file}")
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("\n📋 ROOT CAUSE:")
    print("  • Grant released after AW handshake")
    print("  • Should hold grant until WLAST")
    print("  • This breaks write data phase")
    
    fixes = []
    
    # Fix all slave arbitration blocks (s0 through s14)
    for slave_id in range(15):
        print(f"\n🔧 Fixing Slave {slave_id} arbitration...")
        
        # Pattern to find grant release on AW handshake
        old_pattern = re.escape(f"end else if (s{slave_id}_awready && s{slave_id}_awvalid) begin") + r".*?" + \
                     re.escape(f"s{slave_id}_aw_last_grant <= s{slave_id}_aw_grant;") + r".*?" + \
                     re.escape(f"s{slave_id}_aw_grant <= 4'd15;")
        
        # Replace with grant release on WLAST
        new_block = f"""end else if (s{slave_id}_awready && s{slave_id}_awvalid) begin
            // ULTRATHINK FIX: Don't release grant yet, wait for WLAST
            s{slave_id}_aw_last_grant <= s{slave_id}_aw_grant;
            // Grant will be released after WLAST
        end else if (s{slave_id}_wvalid && s{slave_id}_wready && s{slave_id}_wlast) begin
            // ULTRATHINK FIX: Release grant after write data completes
            s{slave_id}_aw_grant <= 4'd15;"""
        
        # Apply the fix
        matches = re.findall(old_pattern, content, re.DOTALL)
        if matches:
            for match in matches:
                # Create the exact replacement
                old_block = f"""end else if (s{slave_id}_awready && s{slave_id}_awvalid) begin
            // Transaction accepted, release grant
            s{slave_id}_aw_last_grant <= s{slave_id}_aw_grant;
            s{slave_id}_aw_grant <= 4'd15;"""
                
                if old_block in content:
                    content = content.replace(old_block, new_block)
                    fixes.append(f"Fixed Slave {slave_id} grant release")
                    break
    
    # Add write ownership tracking for proper routing
    print("\n🔧 Adding write ownership tracking...")
    
    # Find the reg declarations section
    reg_section = re.search(r'(reg\s+\[3:0\]\s+s0_aw_grant;)', content)
    
    if reg_section:
        insert_pos = reg_section.end()
        
        # Add write ownership registers if not already present
        if "s0_w_owner" not in content:
            ownership_regs = "\n\n// ULTRATHINK: Write channel ownership tracking\n"
            for i in range(15):
                ownership_regs += f"reg [3:0] s{i}_w_owner;\n"
                ownership_regs += f"reg       s{i}_w_active;\n"
            
            content = content[:insert_pos] + ownership_regs + content[insert_pos:]
            fixes.append("Added write ownership registers")
    
    # Initialize ownership in reset
    print("\n🔧 Initializing write ownership...")
    
    for slave_id in range(15):
        reset_pattern = f"s{slave_id}_aw_grant <= 4'd15; // No grant"
        reset_match = content.find(reset_pattern)
        
        if reset_match > 0 and f"s{slave_id}_w_owner <= 4'd0;" not in content:
            # Add initialization after grant reset
            init_text = f"\n        s{slave_id}_w_owner <= 4'd0;\n        s{slave_id}_w_active <= 1'b0;"
            content = content[:reset_match + len(reset_pattern)] + init_text + content[reset_match + len(reset_pattern):]
    
    # Update ownership on AW handshake
    print("\n🔧 Updating ownership logic...")
    
    for slave_id in range(15):
        # Find where we set aw_last_grant
        pattern = f"s{slave_id}_aw_last_grant <= s{slave_id}_aw_grant;"
        
        if pattern in content and f"s{slave_id}_w_owner <= s{slave_id}_aw_grant;" not in content:
            # Add ownership capture
            ownership_update = f"\n            s{slave_id}_w_owner <= s{slave_id}_aw_grant;\n            s{slave_id}_w_active <= 1'b1;"
            content = content.replace(pattern, pattern + ownership_update)
            fixes.append(f"Added Slave {slave_id} ownership tracking")
    
    # Clear ownership on WLAST
    for slave_id in range(15):
        wlast_pattern = f"s{slave_id}_aw_grant <= 4'd15;"
        
        # Find the WLAST grant release we just added
        wlast_context = f"s{slave_id}_wvalid && s{slave_id}_wready && s{slave_id}_wlast"
        
        if wlast_context in content:
            # Add ownership clear
            wlast_match = content.find(wlast_context)
            if wlast_match > 0:
                # Find the grant release line after this condition
                grant_release = content.find(f"s{slave_id}_aw_grant <= 4'd15;", wlast_match)
                if grant_release > 0 and f"s{slave_id}_w_active <= 1'b0;" not in content[wlast_match:grant_release+100]:
                    clear_ownership = f"\n            s{slave_id}_w_active <= 1'b0;"
                    insert_at = grant_release + len(f"s{slave_id}_aw_grant <= 4'd15;")
                    content = content[:insert_at] + clear_ownership + content[insert_at:]
    
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
    
    print("\n🧪 TESTING WLAST FIX...")
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
        print("-" * 40)
        
        # Check for UVM errors
        print("Checking for UVM_ERRORs...")
        os.system("grep 'UVM_ERROR :' logs/axi4_simple_crossbar_test_1.log | tail -3")
        
        # Check WLAST statistics
        print("\nWLAST Statistics:")
        os.system("grep 'WLAST' logs/axi4_simple_crossbar_test_1.log | grep -E '(COUNT|Expected|Actual)' | tail -10")
        
        # Check if test passed
        print("\nTest Summary:")
        os.system("grep 'TEST PASSED\\|TEST FAILED' logs/axi4_simple_crossbar_test_1.log")
        
        return True
    else:
        print("❌ Compilation failed")
        return False

if __name__ == "__main__":
    print("🚀 ULTRATHINK WLAST COMPLETION FIX")
    print("=" * 60)
    print("Fixing grant release timing to wait for WLAST")
    print()
    
    if apply_wlast_completion_fix():
        print("\n✅ WLAST completion fix applied successfully")
        
        if compile_and_test():
            print("\n✅ Fix tested - check results above")
            print("\n🎯 If UVM_ERROR count is 0, the fix is successful!")
        else:
            print("\n⚠️ Test execution failed")
    else:
        print("\n❌ Failed to apply fixes")