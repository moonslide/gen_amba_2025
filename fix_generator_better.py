#!/usr/bin/env python3
"""Fix SystemVerilog literals in generator - better approach"""

import re

# Read the generator file
with open('/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_environment_generator.py', 'r') as f:
    content = f.read()

# First, undo the previous escaped quotes
content = content.replace("\\'", "'")

# Now replace the problematic hex literals with a format that works in f-strings
# Replace 64'h with 64'h (using different quote style around the entire string)
# But this requires more complex parsing. Let's use a different approach.

# Find all f-string blocks that contain SystemVerilog hex literals
# and convert them to regular strings with .format()

# For the test file generations, we need to be more surgical
# Let's replace specific problematic sections

# Pattern to find f.write(f""" ... """) blocks that contain hex literals
def fix_fstring_with_hex_literals(match):
    """Convert f-string with hex literals to regular string with format"""
    content = match.group(1)
    
    # Check if it contains hex literals
    if "'h" in content:
        # Replace f""" with """ and add .format() at the end
        # First extract any {variable} expressions
        variables = re.findall(r'{([^}]+)}', content)
        
        # Create format string by replacing {var} with {0}, {1}, etc
        format_content = content
        format_args = []
        for i, var in enumerate(variables):
            format_content = format_content.replace('{' + var + '}', '{' + str(i) + '}')
            format_args.append(var)
        
        if format_args:
            return f'f.write("""{format_content}""".format({", ".join(format_args)}))'
        else:
            return f'f.write("""{content}""")'
    else:
        return match.group(0)

# Apply fix to specific f.write(f""" ... """) patterns
# This is a simplified approach - for complex cases we might need manual fixes

# For now, let's just fix the specific files that have issues
# by replacing f-strings with regular strings for those sections

# Find the test file generation sections
test_files = [
    'axi4_4kb_boundary_test',
    'axi4_exclusive_access_test', 
    'axi4_protocol_compliance_test',
    'axi4_advanced_error_test',
    'axi4_multi_master_contention_test',
    'axi4_data_integrity_test'
]

for test_file in test_files:
    # Find the section for this test file
    pattern = rf'with open\(.*"{test_file}.sv".*?\n(.*?)f\.write\(f"""(.*?)"""\)',
    
    # Use a simpler approach - find and replace specific problem areas
    # Replace hex literals in a way that works with f-strings
    
# Actually, let's use a different approach entirely
# Replace 64'h with a placeholder that gets substituted later

# Replace all instances of digit+'h with digit + underscore + h
content = re.sub(r"(\d+)'h", r"\1_TICK_h", content)
content = re.sub(r"(\d+)'b", r"\1_TICK_b", content)

# Write the modified content
with open('/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_environment_generator.py', 'w') as f:
    f.write(content)

print("Fixed SystemVerilog literals using placeholder approach")