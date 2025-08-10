#!/usr/bin/env python3
"""
Direct fix for syntax error in vip_environment_generator.py
Fixes the unclosed f-string causing failure at step 6/10 for 17x18 configuration
"""

import os
import shutil
from datetime import datetime

def apply_direct_fix():
    """Apply a direct fix to the syntax error"""
    
    script_dir = os.path.dirname(os.path.abspath(__file__))
    src_dir = os.path.join(script_dir, "..", "src")
    generator_file = os.path.join(src_dir, "vip_environment_generator.py")
    
    if not os.path.exists(generator_file):
        print(f"Error: Cannot find {generator_file}")
        return False
    
    # Backup original file
    backup_file = generator_file + ".backup_direct_fix_" + datetime.now().strftime("%Y%m%d_%H%M%S")
    shutil.copy2(generator_file, backup_file)
    print(f"Created backup: {backup_file}")
    
    # Read the file
    with open(generator_file, 'r') as f:
        lines = f.readlines()
    
    print(f"Total lines in file: {len(lines)}")
    
    # Check line 1215-1217 for the issue
    if len(lines) > 1216:
        print(f"Line 1215: {repr(lines[1214].rstrip())}")
        print(f"Line 1216: {repr(lines[1215].rstrip())}")
        print(f"Line 1217: {repr(lines[1216].rstrip())}")
        
        # If line 1216 is empty and 1217 starts with def, we have the problem
        if lines[1215].strip() == '' and 'def _create_makefile_enhanced' in lines[1216]:
            print("Found the syntax error - unclosed f-string!")
            
            # Insert the missing closing and content
            # Replace the empty line 1216 with the proper sequence content and closing
            fixed_content = '''class axi4_master_base_seq extends uvm_sequence #(axi4_master_tx);
    
    `uvm_object_utils(axi4_master_base_seq)
    
    // Number of transactions
    int num_trans = 1;
    
    // Constructor
    function new(string name = "axi4_master_base_seq");
        super.new(name);
    endfunction
    
    // Pre body
    virtual task pre_body();
        // Objection handling if needed
    endtask
    
    // Post body  
    virtual task post_body();
        // Objection handling if needed
    endtask
    
    // Body method
    virtual task body();
        `uvm_info(get_type_name(), "Starting base sequence", UVM_MEDIUM)
    endtask : body
    
endclass : axi4_master_base_seq
""")

'''
            # Update line 1216 with the missing content
            lines[1215] = fixed_content
            
            # Write the fixed content back
            with open(generator_file, 'w') as f:
                f.writelines(lines)
            
            print("✅ Applied fix: Added missing sequence content and closed f-string")
            return True
        else:
            print("Pattern not found, checking alternative location...")
    
    return False

def verify_syntax():
    """Verify Python syntax after fix"""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    src_dir = os.path.join(script_dir, "..", "src")
    generator_file = os.path.join(src_dir, "vip_environment_generator.py")
    
    try:
        with open(generator_file, 'r') as f:
            code = f.read()
        compile(code, generator_file, 'exec')
        print("✅ Python syntax check: PASSED - No syntax errors!")
        return True
    except SyntaxError as e:
        print(f"❌ Python syntax check: FAILED")
        print(f"   Error at line {e.lineno}: {e.msg}")
        print(f"   Text: {e.text}")
        return False

if __name__ == "__main__":
    print("=== Direct Syntax Error Fix for 17x18 VIP Generation ===")
    print("Fixing unclosed f-string causing step 6/10 failure\n")
    
    if apply_direct_fix():
        print("\n🔍 Verifying Python syntax...")
        if verify_syntax():
            print("\n✅ SUCCESS: Syntax error has been fixed!")
            print("✅ The 17x18 configuration should now generate without errors.")
            print("\n📌 Next steps:")
            print("   1. Launch GUI: ./launch_gui_ultrathin.sh")
            print("   2. Configure 17 masters and 18 slaves")
            print("   3. Generate VIP - it should complete all 10 steps")
        else:
            print("\n⚠️  Fix was applied but syntax check still fails.")
            print("   Please check the error details above.")
    else:
        print("\n❌ Could not apply the fix. The file structure may have changed.")