#!/usr/bin/env python3
"""Simple test to verify the Verilog syntax fix by checking existing generated files"""

import os
import re

def check_file(filepath):
    """Check a file for syntax issues"""
    print(f"\nChecking: {filepath}")
    
    if not os.path.exists(filepath):
        print(f"  File not found: {filepath}")
        return False
        
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Check for incorrect patterns
    incorrect_patterns = [
        r"\{ID_WIDTH\}'d0",
        r"\{ADDR_WIDTH\}'d0", 
        r"\{DATA_WIDTH\}'d0"
    ]
    
    found_errors = False
    for pattern in incorrect_patterns:
        matches = re.findall(pattern, content)
        if matches:
            print(f"  ❌ Found incorrect pattern: {pattern}")
            # Find line numbers
            lines = content.split('\n')
            for i, line in enumerate(lines):
                if re.search(pattern, line):
                    print(f"     Line {i+1}: {line.strip()}")
            found_errors = True
    
    # Check for correct patterns
    correct_patterns = [
        r"\{ID_WIDTH\{1'b0\}\}",
        r"\{ADDR_WIDTH\{1'b0\}\}", 
        r"\{DATA_WIDTH\{1'b0\}\}"
    ]
    
    found_correct = 0
    for pattern in correct_patterns:
        if re.search(pattern, content):
            print(f"  ✓ Found correct pattern: {pattern}")
            found_correct += 1
    
    return not found_errors

def main():
    """Check various test directories for generated files"""
    print("Verilog Syntax Fix Verification")
    print("="*50)
    
    # Look for generated testbench files
    test_dirs = [
        "/home/timtim01/eda_test/project/gen_amba_2025/vip_test/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl",
        "/home/timtim01/eda_test/project/gen_amba_2025/vip_out",
        "/home/timtim01/eda_test/project/vip_test"
    ]
    
    for dir_path in test_dirs:
        if os.path.exists(dir_path):
            print(f"\nSearching in: {dir_path}")
            # Find testbench files
            for root, dirs, files in os.walk(dir_path):
                for file in files:
                    if file.startswith("tb_") and file.endswith(".v"):
                        filepath = os.path.join(root, file)
                        check_file(filepath)
    
    print("\n" + "="*50)
    print("To regenerate files with the fix:")
    print("1. Launch the GUI: ./launch_gui.sh")
    print("2. Configure your design")
    print("3. Generate RTL and VIP")
    print("4. Check the generated testbench files")

if __name__ == "__main__":
    main()