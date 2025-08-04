#!/usr/bin/env python3
"""Fix SystemVerilog array initialization in generated test files"""

import os
import re

test_dir = "/home/timtim01/eda_test/project/gen_amba_2025/vip_test/axi4_vip_env_rtl_integration/test"

# List of test files to fix
test_files = [
    "axi4_protocol_compliance_test.sv",
    "axi4_comprehensive_burst_test.sv",
    "axi4_4kb_boundary_test.sv",
    "axi4_exclusive_access_test.sv",
    "axi4_advanced_error_test.sv",
    "axi4_multi_master_contention_test.sv",
    "axi4_data_integrity_test.sv"
]

for test_file in test_files:
    file_path = os.path.join(test_dir, test_file)
    if os.path.exists(file_path):
        with open(file_path, 'r') as f:
            content = f.read()
        
        # Fix array initialization patterns
        # Pattern 1: int array_name[] = {values};
        content = re.sub(r'(\s+int\s+\w+\[\]\s*=\s*){([^}]+)}', r"\1'{2}", content)
        
        # Pattern 2: inside {values} constraints
        content = re.sub(r'(inside\s+){{([^}]+)}}', r'\1{\2}', content)
        
        with open(file_path, 'w') as f:
            f.write(content)
        
        print(f"Fixed {test_file}")

print("Done fixing SystemVerilog array syntax")