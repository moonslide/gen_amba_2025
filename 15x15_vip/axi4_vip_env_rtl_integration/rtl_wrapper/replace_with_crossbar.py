#!/usr/bin/env python3
"""Replace 1:1 routing with proper AXI4 crossbar"""

import sys

def main():
    # Read the original file
    with open('generated_rtl/axi4_interconnect_m15s15.v', 'r') as f:
        lines = f.readlines()
    
    # Keep lines 1-2344 (0-2343 in 0-indexed)
    header = lines[:2344]
    
    # Generate the crossbar logic
    import generate_crossbar_fixed
    crossbar = generate_crossbar_fixed.generate_complete_crossbar()
    
    # Write new file
    with open('generated_rtl/axi4_interconnect_m15s15.v', 'w') as f:
        f.writelines(header)
        f.write("\n//------------------------------------------------------------------------------\n")
        f.write("// AXI4 Crossbar Switch Implementation\n")
        f.write("// Full crossbar allowing any master to access any slave\n")
        f.write("// Based on address decoding and round-robin arbitration\n")
        f.write("//------------------------------------------------------------------------------\n\n")
        f.write(crossbar)
        f.write("\n\nendmodule\n")
    
    print("Successfully replaced 1:1 routing with proper AXI4 crossbar")

if __name__ == "__main__":
    main()