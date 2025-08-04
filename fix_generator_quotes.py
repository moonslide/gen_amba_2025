#!/usr/bin/env python3
"""Fix SystemVerilog single quotes in f-strings"""

import re

# Read the generator file
with open('/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_environment_generator.py', 'r') as f:
    content = f.read()

# Replace patterns like 64'h, 128'h, 32'h, etc. with escaped versions
# This regex matches number followed by 'h or 'b for hex/binary literals
pattern = r"(\d+)'([hb])"
replacement = r"\1\\'\\2"

# Apply the replacement
fixed_content = re.sub(pattern, replacement, content)

# Write the fixed content back
with open('/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_environment_generator.py', 'w') as f:
    f.write(fixed_content)

print("Fixed SystemVerilog single quotes in generator file")