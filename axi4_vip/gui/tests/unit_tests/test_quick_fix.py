#!/usr/bin/env python3
"""Quick test to verify the Verilog syntax fix by generating a small testbench"""

import os
import sys
import re

sys.path.append('src')

def generate_test_tb():
    """Generate a test testbench using the fixed code"""
    
    # Import after updating path
    from axi_verilog_generator import AXIVerilogGenerator
    
    # Create test config
    class SimpleConfig:
        def __init__(self):
            self.masters = []
            self.slaves = []
            self.data_width = 32
            self.addr_width = 32
            
            # Add 2 masters
            for i in range(2):
                master = type('Master', (), {})()
                master.name = f"master{i}"
                master.id_width = 4
                self.masters.append(master)
                
            # Add 2 slaves  
            for i in range(2):
                slave = type('Slave', (), {})()
                slave.name = f"slave{i}"
                slave.base_address = i * 0x1000_0000
                slave.size = 262144  # 256MB in KB
                self.slaves.append(slave)
    
    config = SimpleConfig()
    gen = AXIVerilogGenerator(config)
    gen.output_dir = "test_fix_output"
    
    # Generate only the testbench
    os.makedirs(gen.output_dir, exist_ok=True)
    try:
        gen.generate_testbench()
    except Exception as e:
        print(f"Error generating testbench: {e}")
        import traceback
        traceback.print_exc()
    
    # List generated files
    print(f"\nGenerated files in {gen.output_dir}:")
    if os.path.exists(gen.output_dir):
        for f in os.listdir(gen.output_dir):
            print(f"  - {f}")
    
    # Check the generated file
    tb_file = os.path.join(gen.output_dir, "tb_axi4_interconnect.v")
    
    if os.path.exists(tb_file):
        print(f"✓ Generated testbench: {tb_file}")
        
        with open(tb_file, 'r') as f:
            content = f.read()
            
        # Check for old syntax
        old_pattern = r"\{ID_WIDTH\}'d0"
        if re.search(old_pattern, content):
            print("❌ ERROR: Old syntax still present!")
            return False
            
        # Check for new syntax
        new_pattern = r"\{ID_WIDTH\{1'b0\}\}"
        matches = re.findall(new_pattern, content)
        if matches:
            print(f"✓ SUCCESS: Found {len(matches)} instances of correct syntax")
            
            # Show a few examples
            print("\nExample lines with correct syntax:")
            lines = content.split('\n')
            count = 0
            for i, line in enumerate(lines):
                if "{ID_WIDTH{1'b0}}" in line and count < 3:
                    print(f"  Line {i+1}: {line.strip()}")
                    count += 1
            
            return True
        else:
            print("⚠ WARNING: Could not find new syntax pattern")
            return False
    else:
        print(f"❌ ERROR: Testbench not generated at {tb_file}")
        return False

def main():
    print("Quick Verilog Syntax Fix Test")
    print("="*40)
    
    success = generate_test_tb()
    
    # Cleanup
    import shutil
    if os.path.exists("test_fix_output"):
        shutil.rmtree("test_fix_output")
        print("\n✓ Cleaned up test files")
    
    print("\n" + "="*40)
    if success:
        print("TEST PASSED: Verilog syntax fix is working!")
        print("\nThe fix changes:")
        print("  OLD: assign m0_awid = {ID_WIDTH}'d0;")
        print("  NEW: assign m0_awid = {ID_WIDTH{1'b0}};")
        print("\nThis is the correct Verilog replication operator syntax.")
    else:
        print("TEST FAILED: Please check the fix implementation")

if __name__ == "__main__":
    main()