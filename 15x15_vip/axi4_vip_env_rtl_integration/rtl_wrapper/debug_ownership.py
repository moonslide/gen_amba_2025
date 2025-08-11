#!/usr/bin/env python3
"""
Debug ownership tracking logic
Check if s0_w_busy is cleared properly after WLAST
"""

import re

def check_ownership_logic():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("Checking ownership clear logic for slave 0...")
    
    # Find the clear logic
    pattern = r"// Clear write ownership when WLAST completes.*?s0_w_owner <= 4'd15;"
    
    match = re.search(pattern, content, re.DOTALL)
    if match:
        print("\n✓ Found ownership clear logic:")
        print(match.group(0))
    else:
        print("\n❌ Ownership clear logic not found!")
    
    # Check if the signals are properly connected
    print("\nChecking s0_wlast assignment...")
    pattern = r"assign s0_wlast = .*?;"
    match = re.search(pattern, content, re.DOTALL)
    if match:
        print("✓ Found s0_wlast assignment:")
        # Print first few lines
        lines = match.group(0).split('\n')[:5]
        for line in lines:
            print(line)
    
    print("\nChecking s0_wready assignment...")
    pattern = r"assign s0_wready = "
    match = re.search(pattern, content)
    if match:
        print("✓ Found s0_wready assignment")
    else:
        print("❌ s0_wready assignment not found!")
    
    print("\nChecking s0_wvalid assignment...")
    pattern = r"assign s0_wvalid = .*?;"
    match = re.search(pattern, content, re.DOTALL)
    if match:
        print("✓ Found s0_wvalid assignment:")
        lines = match.group(0).split('\n')[:5]
        for line in lines:
            print(line)

if __name__ == "__main__":
    check_ownership_logic()