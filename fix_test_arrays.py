#!/usr/bin/env python3
"""Fix array declarations in comprehensive test files"""

import re
import os

test_dir = '/home/timtim01/eda_test/project/gen_amba_2025/vip_test/axi4_vip_env_rtl_integration/test'

# Files to fix
test_files = [
    'axi4_4kb_boundary_test.sv',
    'axi4_protocol_compliance_test.sv',
    'axi4_comprehensive_burst_test.sv',
    'axi4_exclusive_access_test.sv',
    'axi4_multi_master_contention_test.sv',
    'axi4_advanced_error_test.sv',
    'axi4_data_integrity_test.sv'
]

# Fix patterns
fixes = [
    # Fix simple array declarations with initialization
    (r'(\s+)int (\w+)\[\] = \{([^}]+)\};', r'\1int \2[] = \'{{\3}};'),
    (r'(\s+)bit \[63:0\] (\w+)\[\] = \{([^}]+)\};', r'\1bit [63:0] \2[] = \'{{\3}};'),
    (r'(\s+)bit \[127:0\] (\w+)\[\] = \{([^}]+)\};', r'\1bit [127:0] \2[] = \'{{\3}};'),
    
    # Fix typedef struct arrays
    (r"(priority_config_t \w+\[\] = )\{", r"\1'{"),
    (r"(wstrb_test_t \w+\[\] = )\{", r"\1'{"),
    
    # Fix struct field initializations
    (r"'\{(\d+), (\d+), (\d+), (64'h[\w_]+)\}", r"'{{\1, \2, \3, \4}}"),
    (r"'\{(8'b\w+), \"([^\"]+)\"\}", r"'{{\1, \"\2\"}}"),
]

for test_file in test_files:
    file_path = os.path.join(test_dir, test_file)
    if os.path.exists(file_path):
        with open(file_path, 'r') as f:
            content = f.read()
        
        # Apply fixes
        for pattern, replacement in fixes:
            content = re.sub(pattern, replacement, content)
        
        # Write back
        with open(file_path, 'w') as f:
            f.write(content)
        
        print(f"Fixed array declarations in {test_file}")
    else:
        print(f"File not found: {test_file}")

print("Array declaration fixes completed")