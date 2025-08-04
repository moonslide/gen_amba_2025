#!/usr/bin/env python3
"""Fix all array declarations in test files by wrapping them in begin/end blocks"""

import re
import os

test_dir = '/home/timtim01/eda_test/project/gen_amba_2025/vip_test/axi4_vip_env_rtl_integration/test'

# Pattern to find array declarations inside tasks
pattern = re.compile(
    r'(\s+)(int|bit\s*\[\d+:\d+\])\s+(\w+)\[\]\s*=\s*\'{([^}]+)};',
    re.MULTILINE
)

def fix_file(filepath):
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Find all matches
    matches = list(pattern.finditer(content))
    if not matches:
        return False
    
    # Process from end to beginning to preserve positions
    for match in reversed(matches):
        indent = match.group(1)
        type_str = match.group(2)
        var_name = match.group(3)
        values = match.group(4)
        
        # Check if already in a begin block
        before_pos = match.start()
        lines_before = content[:before_pos].split('\n')
        
        # Look for previous begin statement
        found_begin = False
        for i in range(len(lines_before)-1, max(0, len(lines_before)-5), -1):
            if 'begin' in lines_before[i] and 'end' not in lines_before[i]:
                found_begin = True
                break
        
        if not found_begin:
            # Need to wrap in begin/end
            # Find where to place the begin
            begin_pos = match.start()
            
            # Find where to place the end - after the foreach loop or block that uses this array
            after_content = content[match.end():]
            lines_after = after_content.split('\n')
            
            # Count indent level
            base_indent_level = len(indent) - len(indent.lstrip())
            
            end_pos = None
            current_indent = base_indent_level
            in_foreach = False
            
            for i, line in enumerate(lines_after):
                stripped = line.strip()
                if stripped.startswith('foreach') and var_name in stripped:
                    in_foreach = True
                elif in_foreach:
                    line_indent = len(line) - len(line.lstrip())
                    if line_indent <= base_indent_level and 'end' in line:
                        # Found the end of the foreach block
                        end_pos = match.end() + sum(len(l) + 1 for l in lines_after[:i+1])
                        break
            
            if end_pos:
                # Insert begin before array declaration and end after foreach
                new_content = (
                    content[:begin_pos] + 
                    indent + "begin\n" +
                    content[begin_pos:end_pos] + "\n" +
                    indent + "end\n" +
                    content[end_pos:]
                )
                content = new_content
    
    with open(filepath, 'w') as f:
        f.write(content)
    
    return True

# Fix all test files
test_files = [
    'axi4_exclusive_access_test.sv',
    'axi4_protocol_compliance_test.sv'
]

for test_file in test_files:
    filepath = os.path.join(test_dir, test_file)
    if os.path.exists(filepath):
        if fix_file(filepath):
            print(f"Fixed array declarations in {test_file}")
        else:
            print(f"No fixes needed in {test_file}")

print("Array declaration fixes completed")