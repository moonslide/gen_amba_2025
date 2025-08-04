#!/usr/bin/env python3
"""Fix array declarations in VIP generator to work with VCS"""

import re

# Read the generator file
with open('/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_environment_generator.py', 'r') as f:
    content = f.read()

# First, revert any previous _TICK_ replacements
content = content.replace("_TICK_h", "'h").replace("_TICK_b", "'b")

# Now fix array declarations in test generation functions

# Fix protocol compliance test
old_pattern = r'''        int burst_types\[\$?\] = '{\d+, \d+, \d+}; // FIXED, INCR, WRAP'''
new_pattern = '''// Arrays are declared as class properties'''
content = re.sub(old_pattern, new_pattern, content)

old_pattern2 = r'''        int qos_values\[\$?\] = '{\d+, \d+, \d+, \d+, \d+};'''
new_pattern2 = '''// QoS values array declared as class property'''
content = re.sub(old_pattern2, new_pattern2, content)

# Fix comprehensive burst test
old_pattern3 = r'''        int burst_lengths\[\$?\] = '{[^}]+}; // AXI4 supports up to 256'''
new_pattern3 = '''// Burst lengths array declared as class property'''
content = re.sub(old_pattern3, new_pattern3, content)

old_pattern4 = r'''        int wrap_lengths\[\$?\] = '{[^}]+}; // Valid WRAP lengths only'''
new_pattern4 = '''// Wrap lengths array declared as class property'''
content = re.sub(old_pattern4, new_pattern4, content)

old_pattern5 = r'''        int burst_sizes\[\$?\] = '{[^}]+}; // 1 to 128 bytes'''
new_pattern5 = '''// Burst sizes array declared as class property'''
content = re.sub(old_pattern5, new_pattern5, content)

# Add class property declarations after uvm_component_utils
def add_class_properties(match):
    class_name = match.group(1)
    utils_line = match.group(0)
    
    properties = ""
    
    if "protocol_compliance" in class_name:
        properties = """
    
    // Test arrays
    int burst_types[3];
    int qos_values[5];"""
    elif "comprehensive_burst" in class_name:
        properties = """
    
    // Test arrays
    int burst_lengths[9];
    int wrap_lengths[4];
    int burst_sizes[8];"""
    elif "4kb_boundary" in class_name:
        properties = """
    
    // Test arrays
    int burst_lengths[8];
    int burst_sizes[8];"""
    elif "exclusive_access" in class_name:
        properties = """
    
    // Test arrays
    int exclusive_sizes[8];"""
    elif "multi_master_contention" in class_name:
        properties = """
    
    // Test arrays
    int qos_levels[5];"""
    elif "data_integrity" in class_name:
        properties = """
    
    // Test arrays
    int burst_types[3];
    int burst_lengths[8];"""
    
    return utils_line + properties

# Add property declarations
content = re.sub(r'(`uvm_component_utils\(axi4_(\w+)\))', add_class_properties, content)

# Add array initialization in constructors
def add_constructor_init(match):
    full_match = match.group(0)
    class_name = match.group(1)
    
    init_code = ""
    
    if "protocol_compliance" in class_name:
        init_code = """
        // Initialize arrays
        burst_types[0] = 0; // FIXED
        burst_types[1] = 1; // INCR
        burst_types[2] = 2; // WRAP
        qos_values[0] = 0;
        qos_values[1] = 4;
        qos_values[2] = 8;
        qos_values[3] = 12;
        qos_values[4] = 15;"""
    elif "comprehensive_burst" in class_name:
        init_code = """
        // Initialize arrays
        burst_lengths[0] = 1;
        burst_lengths[1] = 2;
        burst_lengths[2] = 4;
        burst_lengths[3] = 8;
        burst_lengths[4] = 16;
        burst_lengths[5] = 32;
        burst_lengths[6] = 64;
        burst_lengths[7] = 128;
        burst_lengths[8] = 256;
        wrap_lengths[0] = 2;
        wrap_lengths[1] = 4;
        wrap_lengths[2] = 8;
        wrap_lengths[3] = 16;
        burst_sizes[0] = 1;
        burst_sizes[1] = 2;
        burst_sizes[2] = 4;
        burst_sizes[3] = 8;
        burst_sizes[4] = 16;
        burst_sizes[5] = 32;
        burst_sizes[6] = 64;
        burst_sizes[7] = 128;"""
    elif "4kb_boundary" in class_name:
        init_code = """
        // Initialize arrays
        burst_lengths[0] = 1;
        burst_lengths[1] = 4;
        burst_lengths[2] = 8;
        burst_lengths[3] = 16;
        burst_lengths[4] = 32;
        burst_lengths[5] = 64;
        burst_lengths[6] = 128;
        burst_lengths[7] = 256;
        burst_sizes[0] = 1;
        burst_sizes[1] = 2;
        burst_sizes[2] = 4;
        burst_sizes[3] = 8;
        burst_sizes[4] = 16;
        burst_sizes[5] = 32;
        burst_sizes[6] = 64;
        burst_sizes[7] = 128;"""
    elif "exclusive_access" in class_name:
        init_code = """
        // Initialize arrays
        exclusive_sizes[0] = 1;
        exclusive_sizes[1] = 2;
        exclusive_sizes[2] = 4;
        exclusive_sizes[3] = 8;
        exclusive_sizes[4] = 16;
        exclusive_sizes[5] = 32;
        exclusive_sizes[6] = 64;
        exclusive_sizes[7] = 128;"""
    elif "multi_master_contention" in class_name:
        init_code = """
        // Initialize arrays
        qos_levels[0] = 0;
        qos_levels[1] = 4;
        qos_levels[2] = 8;
        qos_levels[3] = 12;
        qos_levels[4] = 15;"""
    elif "data_integrity" in class_name:
        init_code = """
        // Initialize arrays
        burst_types[0] = 0; // FIXED
        burst_types[1] = 1; // INCR
        burst_types[2] = 2; // WRAP
        burst_lengths[0] = 1;
        burst_lengths[1] = 2;
        burst_lengths[2] = 4;
        burst_lengths[3] = 8;
        burst_lengths[4] = 16;
        burst_lengths[5] = 32;
        burst_lengths[6] = 64;
        burst_lengths[7] = 128;"""
    
    # Insert initialization code before endfunction
    return full_match.replace("    endfunction", init_code + "\n    endfunction")

# Add constructor initialization
pattern = r'(class axi4_(\w+) extends.*?function new.*?endfunction)'
content = re.sub(pattern, add_constructor_init, content, flags=re.DOTALL)

# Write the fixed content back
with open('/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_environment_generator.py', 'w') as f:
    f.write(content)

print("Fixed array declarations in generator file")