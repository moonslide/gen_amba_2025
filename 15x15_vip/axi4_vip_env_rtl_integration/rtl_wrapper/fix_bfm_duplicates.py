#!/usr/bin/env python3
"""
Fix duplicate variable declarations and auto-drive issues in BFMs
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

def fix_master_bfm_duplicates(master_driver_path):
    """Fix duplicate declarations and auto-drive in master BFM"""
    
    print(f"\n📝 Fixing duplicate declarations in master driver BFM...")
    
    # Read the file
    with open(master_driver_path, 'r') as f:
        lines = f.readlines()
    
    # Track if we've seen the declarations
    seen_declarations = False
    fixed_lines = []
    skip_next_lines = 0
    
    for i, line in enumerate(lines):
        if skip_next_lines > 0:
            skip_next_lines -= 1
            continue
            
        # Remove duplicate control signal declarations (around line 258-263)
        if i >= 255 and i <= 265:
            if "// Control signals for BFM operation" in line:
                # Skip this block as it's a duplicate
                skip_next_lines = 5  # Skip the next 5 lines
                print(f"  Removing duplicate control signals at line {i+1}")
                continue
            elif "bit enable_auto_drive = 0;" in line and seen_declarations:
                print(f"  Removing duplicate enable_auto_drive at line {i+1}")
                continue
            elif "bit bfm_enable = 0;" in line and seen_declarations:
                print(f"  Removing duplicate bfm_enable at line {i+1}")
                continue
            elif "int transaction_count = 0;" in line and seen_declarations:
                print(f"  Removing duplicate transaction_count at line {i+1}")
                continue
        
        # Mark that we've seen the first declarations
        if "bit enable_auto_drive = 0;" in line and not seen_declarations:
            seen_declarations = True
            
        # Change default BFM enable behavior - don't auto-start
        if "// Default: enable BFM driving for signal visibility" in line:
            fixed_lines.append(line)
            # Skip the next two lines and replace with disabled version
            if i+1 < len(lines) and "bfm_enable = 1;" in lines[i+2]:
                fixed_lines.append('            `uvm_info("AXI_MASTER_DRIVER_BFM", "BFM driving disabled by default - use +BFM_AUTO_DRIVE=1 to enable", UVM_LOW)\n')
                fixed_lines.append('            bfm_enable = 0;  // Disabled by default to prevent interference\n')
                skip_next_lines = 2
                print(f"  Changed default BFM enable to disabled at line {i+3}")
                continue
                
        fixed_lines.append(line)
    
    # Write the fixed content
    with open(master_driver_path, 'w') as f:
        f.writelines(fixed_lines)
    
    print(f"✓ Fixed duplicate declarations and auto-drive in master driver BFM")
    return True

def fix_simple_crossbar_test(test_path):
    """Fix the simple crossbar test to have proper timeout"""
    
    print(f"\n📝 Fixing simple crossbar test timeout...")
    
    # Read the file
    with open(test_path, 'r') as f:
        content = f.read()
    
    # Replace the hardcoded delay with a proper timeout
    old_wait = """        // Wait for completion
        #5000;"""
    
    new_wait = """        // Wait for completion with timeout
        fork
            begin
                #50000;  // 50us timeout
                `uvm_error(get_type_name(), "Test timeout - sequences did not complete in time")
            end
            begin
                // Wait for actual sequence completion
                wait(vseq.seq_done == 1);
                `uvm_info(get_type_name(), "Virtual sequence completed successfully", UVM_LOW)
            end
        join_any
        disable fork;
        
        // Small delay to let transactions complete
        #1000;"""
    
    content = content.replace(old_wait, new_wait)
    
    # Write the fixed content
    with open(test_path, 'w') as f:
        f.write(content)
    
    print(f"✓ Fixed simple crossbar test timeout")
    return True

def fix_virtual_sequence(vseq_path):
    """Fix the virtual sequence to signal completion"""
    
    print(f"\n📝 Fixing virtual sequence completion signaling...")
    
    # Read the file
    with open(vseq_path, 'r') as f:
        content = f.read()
    
    # Add completion flag
    old_class_start = """class axi4_virtual_simple_crossbar_seq extends axi4_virtual_base_seq;
    `uvm_object_utils(axi4_virtual_simple_crossbar_seq)
    
    function new(string name = "axi4_virtual_simple_crossbar_seq");"""
    
    new_class_start = """class axi4_virtual_simple_crossbar_seq extends axi4_virtual_base_seq;
    `uvm_object_utils(axi4_virtual_simple_crossbar_seq)
    
    bit seq_done = 0;  // Completion flag
    
    function new(string name = "axi4_virtual_simple_crossbar_seq");"""
    
    content = content.replace(old_class_start, new_class_start)
    
    # Signal completion at the end
    old_end = """        `uvm_info(get_type_name(), "Simple Crossbar Virtual Sequence Completed", UVM_LOW)
    endtask"""
    
    new_end = """        `uvm_info(get_type_name(), "Simple Crossbar Virtual Sequence Completed", UVM_LOW)
        seq_done = 1;  // Signal completion
    endtask"""
    
    content = content.replace(old_end, new_end)
    
    # Write the fixed content
    with open(vseq_path, 'w') as f:
        f.write(content)
    
    print(f"✓ Fixed virtual sequence completion signaling")
    return True

def main():
    """Main function to apply BFM and test fixes"""
    
    print("\n" + "="*60)
    print("🔧 AXI4 VIP BFM and Test Fix Script")
    print("="*60)
    
    # Define paths
    base_path = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration"
    master_driver_path = os.path.join(base_path, "agent/master_agent_bfm/axi4_master_driver_bfm.sv")
    test_path = os.path.join(base_path, "test/axi4_simple_crossbar_test.sv")
    vseq_path = os.path.join(base_path, "virtual_seq/axi4_virtual_simple_crossbar_seq.sv")
    
    # Check if files exist
    if not os.path.exists(master_driver_path):
        print(f"❌ Error: Master driver not found at {master_driver_path}")
        return False
    
    if not os.path.exists(test_path):
        print(f"❌ Error: Test not found at {test_path}")
        return False
        
    if not os.path.exists(vseq_path):
        print(f"❌ Error: Virtual sequence not found at {vseq_path}")
        return False
    
    # Backup files
    backup_file(master_driver_path)
    backup_file(test_path)
    backup_file(vseq_path)
    
    # Apply fixes
    success = True
    success &= fix_master_bfm_duplicates(master_driver_path)
    success &= fix_simple_crossbar_test(test_path)
    success &= fix_virtual_sequence(vseq_path)
    
    if success:
        print("\n" + "="*60)
        print("✅ BFM and test fixes successfully applied!")
        print("\nKey improvements:")
        print("  • Removed duplicate variable declarations")
        print("  • Disabled BFM auto-drive by default")
        print("  • Added proper timeout handling in test")
        print("  • Added completion signaling in virtual sequence")
        print("\nNext steps:")
        print("  1. Run: make clean")
        print("  2. Run: make run_fsdb TEST=axi4_simple_crossbar_test")
        print("  3. Test should complete successfully")
        print("="*60)
    else:
        print("\n❌ Some fixes failed to apply")
        return False
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)