#!/usr/bin/env python3
"""
Fix all duplicate assignments after grant logic fix
"""

import re

def fix_all_duplicates():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    with open(rtl_file, 'r') as f:
        lines = f.readlines()
    
    fixed_lines = []
    i = 0
    
    while i < len(lines):
        line = lines[i]
        
        # Check if this line ends an assignment (ends with : 1'b0; or similar)
        if re.match(r'.*\? \w+ : 1\'b0;\s*$', line):
            # Check if next line starts a duplicate assignment (starts with space and parenthesis)
            if i + 1 < len(lines) and re.match(r'^\s+\(', lines[i + 1]):
                # Found a duplicate, keep current line
                fixed_lines.append(line)
                # Skip lines until we find the end of the duplicate assignment
                i += 1
                while i < len(lines):
                    if ': 1\'b0;' in lines[i]:
                        # Found end of duplicate, skip it and continue
                        i += 1
                        break
                    i += 1
            else:
                fixed_lines.append(line)
                i += 1
        else:
            fixed_lines.append(line)
            i += 1
    
    # Write back
    with open(rtl_file, 'w') as f:
        f.writelines(fixed_lines)
    
    print(f"Fixed duplicate assignments, reduced from {len(lines)} to {len(fixed_lines)} lines")

if __name__ == "__main__":
    fix_all_duplicates()