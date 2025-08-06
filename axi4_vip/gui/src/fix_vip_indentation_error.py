#!/usr/bin/env python3
"""
Fix indentation error in vip_gui_integration.py that prevents VIP from loading
"""

import os

def fix_vip_indentation():
    """Fix the indentation error in scalability patch import"""
    
    vip_file = os.path.join(os.path.dirname(__file__), 'vip_gui_integration.py')
    
    print("🔧 Fixing VIP indentation error...")
    print("="*50)
    
    # Read the file
    with open(vip_file, 'r') as f:
        lines = f.readlines()
    
    # Find the problematic section
    fixed_lines = []
    in_error_section = False
    fixed = False
    
    i = 0
    while i < len(lines):
        line = lines[i]
        
        # Check for the misindented scalability patch section
        if "# Apply scalability patch for large bus matrices" in line and line.startswith("            #"):
            # This line should be inside a method, not at this indentation
            # Skip this entire misplaced block
            print(f"Found misplaced scalability patch at line {i+1}")
            # Skip lines until we find proper indentation again
            j = i
            while j < len(lines) and (lines[j].startswith("try:") or 
                                     lines[j].startswith("    from vip_environment_generator_scalability_patch") or
                                     lines[j].startswith("    apply_scalability_patch") or
                                     lines[j].startswith("    print(") or
                                     lines[j].startswith("except Exception") or
                                     lines[j].startswith("    print(f")):
                j += 1
            
            # Also skip the misplaced comment after
            if j < len(lines) and lines[j].strip() == "# Import the VIP environment generator":
                j += 1
            
            print(f"Removed misplaced code block from lines {i+1} to {j}")
            i = j
            fixed = True
            continue
        
        fixed_lines.append(line)
        i += 1
    
    if fixed:
        # Write back the fixed file
        with open(vip_file, 'w') as f:
            f.writelines(fixed_lines)
        print("✓ Removed misplaced scalability patch code")
        
        # Now add the patch in the correct place - at module level
        print("\nAdding scalability patch at correct location...")
        
        # Read again
        with open(vip_file, 'r') as f:
            content = f.read()
        
        # Add after the other imports at the top
        import_section_end = content.find("# Import with fallback for missing modules")
        if import_section_end > 0:
            # Insert before this comment
            patch_import = """
# Apply scalability patch for large bus matrices (11x11+)
try:
    from vip_environment_generator_scalability_patch import apply_scalability_patch
    apply_scalability_patch()
    print("[VIP] Scalability patch applied for large bus matrix support")
except Exception as e:
    print(f"[VIP] Warning: Could not apply scalability patch: {e}")

"""
            content = content[:import_section_end] + patch_import + content[import_section_end:]
            
            with open(vip_file, 'w') as f:
                f.write(content)
            
            print("✓ Added scalability patch import at module level")
    else:
        print("✓ No indentation errors found")
    
    print("\n✅ VIP module should now load correctly!")
    return True

if __name__ == "__main__":
    if fix_vip_indentation():
        print("\n🎉 VIP indentation fix complete!")
        print("\nThe VIP menu commands should now work properly.")
    else:
        print("\n❌ Failed to fix VIP indentation")