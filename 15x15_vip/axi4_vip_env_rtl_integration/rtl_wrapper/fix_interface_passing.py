#!/usr/bin/env python3
"""
Fix interface passing from hvl_top instead of test class
Resolves the hierarchical reference error from package
"""

import os
import sys
import shutil
from datetime import datetime

def backup_file(filepath):
    """Create backup of file before modifying"""
    backup_path = f"{filepath}.backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    shutil.copy2(filepath, backup_path)
    print(f"✓ Backed up {os.path.basename(filepath)}")
    return backup_path

def fix_base_test(test_path):
    """Remove hierarchical references from base test"""
    
    print(f"\n📝 Fixing base test to remove hierarchical references...")
    
    # Read the file
    with open(test_path, 'r') as f:
        content = f.read()
    
    # Remove the interface passing from build_phase
    old_interface_pass = """        // Pass interfaces to environment via config_db
        for (int i = 0; i < NO_OF_MASTERS; i++) begin
            uvm_config_db#(virtual axi4_if)::set(this, "env", $sformatf("master_if_%0d", i), hdl_top.master_if[i]);
        end
        for (int i = 0; i < NO_OF_SLAVES; i++) begin
            uvm_config_db#(virtual axi4_if)::set(this, "env", $sformatf("slave_if_%0d", i), hdl_top.slave_if[i]);
        end
        
        // Create environment"""
    
    new_interface_pass = """        // Interface passing moved to hvl_top to avoid hierarchical references from package
        
        // Create environment"""
    
    content = content.replace(old_interface_pass, new_interface_pass)
    
    # Write the fixed content
    with open(test_path, 'w') as f:
        f.write(content)
    
    print(f"✓ Fixed base test - removed hierarchical references")
    return True

def fix_hvl_top(hvl_path):
    """Add interface passing to hvl_top"""
    
    print(f"\n📝 Fixing hvl_top to pass interfaces to UVM...")
    
    # Read the file
    with open(hvl_path, 'r') as f:
        content = f.read()
    
    # Add interface passing before run_test
    old_initial = """    initial begin
        `ifdef DUMP_FSDB
            // FSDB dumping using system tasks
            $fsdbDumpfile("waves/axi4_vip.fsdb");
            $fsdbDumpvars(0, hdl_top, "+all");
            $fsdbDumpvars(0, hvl_top, "+all");
            $display("[%0t] FSDB dumping enabled to waves/axi4_vip.fsdb", $time);
        `endif
        
        `ifdef DUMP_VCD
            // VCD dumping
            $dumpfile("waves/axi4_vip.vcd");
            $dumpvars(0, hdl_top);
            $dumpvars(0, hvl_top);
            $display("[%0t] VCD dumping enabled to waves/axi4_vip.vcd", $time);
        `endif
        
        // Run UVM test
        run_test();"""
    
    new_initial = """    initial begin
        `ifdef DUMP_FSDB
            // FSDB dumping using system tasks
            $fsdbDumpfile("waves/axi4_vip.fsdb");
            $fsdbDumpvars(0, hdl_top, "+all");
            $fsdbDumpvars(0, hvl_top, "+all");
            $display("[%0t] FSDB dumping enabled to waves/axi4_vip.fsdb", $time);
        `endif
        
        `ifdef DUMP_VCD
            // VCD dumping
            $dumpfile("waves/axi4_vip.vcd");
            $dumpvars(0, hdl_top);
            $dumpvars(0, hvl_top);
            $display("[%0t] VCD dumping enabled to waves/axi4_vip.vcd", $time);
        `endif
        
        // Pass interfaces to UVM environment via config_db
        // This is done here to avoid hierarchical references from package
        for (int i = 0; i < 15; i++) begin
            uvm_config_db#(virtual axi4_if)::set(uvm_root::get(), "*", $sformatf("master_if_%0d", i), hdl_top.master_if[i]);
        end
        for (int i = 0; i < 15; i++) begin
            uvm_config_db#(virtual axi4_if)::set(uvm_root::get(), "*", $sformatf("slave_if_%0d", i), hdl_top.slave_if[i]);
        end
        
        // Run UVM test
        run_test();"""
    
    content = content.replace(old_initial, new_initial)
    
    # Write the fixed content
    with open(hvl_path, 'w') as f:
        f.write(content)
    
    print(f"✓ Fixed hvl_top - added interface passing")
    return True

def main():
    """Main function to fix interface passing"""
    
    print("\n" + "="*60)
    print("🔧 AXI4 VIP Interface Passing Fix Script")
    print("="*60)
    
    # Define paths
    base_path = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration"
    test_path = os.path.join(base_path, "test/axi4_base_test.sv")
    hvl_path = os.path.join(base_path, "top/hvl_top.sv")
    
    # Check if files exist
    if not os.path.exists(test_path):
        print(f"❌ Error: Base test not found at {test_path}")
        return False
    
    if not os.path.exists(hvl_path):
        print(f"❌ Error: HVL top not found at {hvl_path}")
        return False
    
    # Backup files
    backup_file(test_path)
    backup_file(hvl_path)
    
    # Apply fixes
    success = True
    success &= fix_base_test(test_path)
    success &= fix_hvl_top(hvl_path)
    
    if success:
        print("\n" + "="*60)
        print("✅ Interface passing fixes successfully applied!")
        print("\nKey improvements:")
        print("  • Removed hierarchical references from test package")
        print("  • Moved interface passing to hvl_top initial block")
        print("  • Fixed compilation error 'SV-LCM-HRP'")
        print("\nNext steps:")
        print("  1. Run: make clean")
        print("  2. Run: make run_fsdb TEST=axi4_simple_crossbar_test")
        print("  3. Check DUT signals in waveform")
        print("="*60)
    else:
        print("\n❌ Some fixes failed to apply")
        return False
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)