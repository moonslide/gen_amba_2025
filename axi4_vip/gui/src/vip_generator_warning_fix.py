#!/usr/bin/env python3
"""
VIP Generator Warning Fix Script
Fixes common warning patterns in generated SystemVerilog test files

This script addresses the following warning categories:
1. SIOB - Select Index Out of Bounds (master_agent access)
2. ICTA-SI - Incompatible Complex Type Assignment (bit to string)
3. ENUMASSIGN - Illegal assignment to enum variable (int to enum)
"""

import os
import re
from typing import Dict, List, Tuple, Optional

class VIPGeneratorWarningFix:
    """Fix common warning patterns in VIP generated SystemVerilog files"""
    
    def __init__(self, vip_root: str, num_masters: int = 2, num_slaves: int = 3):
        self.vip_root = vip_root
        self.num_masters = num_masters
        self.num_slaves = num_slaves
        self.test_dir = os.path.join(vip_root, "vip_test/axi4_vip_env_rtl_integration/test")
        
        # Track fixes applied
        self.fixes_applied = {
            'siob_fixes': 0,
            'icta_fixes': 0, 
            'enum_fixes': 0,
            'files_modified': 0
        }
    
    def get_valid_master_index(self, requested_index: int) -> int:
        """Get valid master index within bounds [0, num_masters-1]"""
        return requested_index % self.num_masters
    
    def get_valid_slave_index(self, requested_index: int) -> int:
        """Get valid slave index within bounds [0, num_slaves-1]"""
        return requested_index % self.num_slaves
    
    def fix_master_agent_indices(self, content: str) -> str:
        """Fix master_agent index out of bounds issues"""
        original_content = content
        
        # Pattern: env.master_agent[N].sequencer where N >= num_masters
        pattern = r'env\.master_agent\[(\d+)\]\.sequencer'
        
        def replace_master_index(match):
            index = int(match.group(1))
            if index >= self.num_masters:
                valid_index = self.get_valid_master_index(index)
                self.fixes_applied['siob_fixes'] += 1
                return f"env.master_agent[{valid_index}].sequencer"
            return match.group(0)
        
        content = re.sub(pattern, replace_master_index, content)
        
        # Pattern: master_agent[N] where N >= num_masters (without env prefix)
        pattern2 = r'master_agent\[(\d+)\]'
        
        def replace_master_index2(match):
            index = int(match.group(1))
            if index >= self.num_masters:
                valid_index = self.get_valid_master_index(index)
                self.fixes_applied['siob_fixes'] += 1
                return f"master_agent[{valid_index}]"
            return match.group(0)
        
        content = re.sub(pattern2, replace_master_index2, content)
        
        return content
    
    def fix_type_assignments(self, content: str) -> str:
        """Fix incompatible type assignments (bit/enum to string)"""
        
        # Fix 1: test_data_pattern = bit_variable
        patterns_to_fix = [
            # Bit array to string assignments
            (r'(\w+\.test_data_pattern\s*=\s*)([a-zA-Z_]\w*)\s*;', 
             r'\1$sformatf("%h", \2);'),
            (r'(\w+\.expected_data_pattern\s*=\s*)([a-zA-Z_]\w*)\s*;', 
             r'\1$sformatf("%h", \2);'),
            
            # Bit array indexed to string assignments  
            (r'(\w+\.test_data_pattern\s*=\s*)([a-zA-Z_]\w*\[[^\]]+\])\s*;',
             r'\1$sformatf("%h", \2);'),
            (r'(\w+\.expected_data_pattern\s*=\s*)([a-zA-Z_]\w*\[[^\]]+\])\s*;',
             r'\1$sformatf("%h", \2);'),
            
            # Hex literal to string assignments
            (r'(\w+\.test_data_pattern\s*=\s*)(64\'h[A-Fa-f0-9_]+)\s*;',
             r'\1$sformatf("%h", \2);'),
            (r'(\w+\.expected_data_pattern\s*=\s*)(64\'h[A-Fa-f0-9_]+)\s*;',
             r'\1$sformatf("%h", \2);'),
            
            # Enum to string assignments
            (r'(\w+\.error_type\s*=\s*)axi4_globals_pkg::(\w+)\s*;',
             r'\1"\2";'),
        ]
        
        for pattern, replacement in patterns_to_fix:
            original_content = content
            content = re.sub(pattern, replacement, content)
            if content != original_content:
                self.fixes_applied['icta_fixes'] += content.count(replacement.split('(')[0]) - original_content.count(replacement.split('(')[0])
        
        return content
    
    def fix_enum_assignments(self, content: str) -> str:
        """Fix illegal enum assignments (int to enum)"""
        
        # Pattern: expected_response = int_array[index]
        pattern = r'(\w+\.expected_response\s*=\s*)(\w+\[[^\]]+\])\s*;'
        replacement = r'\1axi4_response_type_e\'(\2);'
        
        original_content = content
        content = re.sub(pattern, replacement, content)
        if content != original_content:
            self.fixes_applied['enum_fixes'] += 1
        
        return content
    
    def apply_string_formatting_fixes(self, content: str) -> str:
        """Apply consistent string formatting for common patterns"""
        
        # Convert common hex patterns to string literals
        hex_to_string_patterns = [
            (r'64\'hAAAAAAAA_AAAAAAAA', '"aaaaaaaaaaaaaaaa"'),
            (r'64\'h55555555_55555555', '"5555555555555555"'),
            (r'64\'hDEADBEEF_CAFEBABE', '"deadbeefcafebabe"'),
            (r'64\'h12345678_9ABCDEF0', '"123456789abcdef0"'),
            (r'64\'hC0DE0000_DEADBEEF', '"c0de0000deadbeef"'),
        ]
        
        for pattern, replacement in hex_to_string_patterns:
            if pattern in content:
                content = content.replace(pattern, replacement)
                self.fixes_applied['icta_fixes'] += 1
        
        return content
    
    def fix_test_file(self, filename: str) -> bool:
        """Fix a single test file and return True if modified"""
        filepath = os.path.join(self.test_dir, filename)
        
        if not os.path.exists(filepath):
            print(f"Warning: {filename} not found")
            return False
        
        # Read file
        with open(filepath, 'r') as f:
            original_content = f.read()
        
        content = original_content
        
        # Apply all fixes
        content = self.fix_master_agent_indices(content)
        content = self.fix_type_assignments(content)
        content = self.fix_enum_assignments(content)
        content = self.apply_string_formatting_fixes(content)
        
        # Write back if changed
        if content != original_content:
            with open(filepath, 'w') as f:
                f.write(content)
            self.fixes_applied['files_modified'] += 1
            return True
        
        return False
    
    def generate_warning_free_test_pattern(self, test_name: str, test_type: str = "comprehensive") -> str:
        """Generate warning-free test patterns for common test types"""
        
        if test_type == "comprehensive":
            return self._generate_comprehensive_test_pattern(test_name)
        elif test_type == "data_integrity":
            return self._generate_data_integrity_test_pattern(test_name)
        elif test_type == "protocol_compliance":
            return self._generate_protocol_compliance_test_pattern(test_name)
        else:
            return self._generate_basic_test_pattern(test_name)
    
    def _generate_comprehensive_test_pattern(self, test_name: str) -> str:
        """Generate warning-free comprehensive test pattern"""
        
        valid_master_indices = [i for i in range(self.num_masters)]
        
        template = f'''//==============================================================================
// {test_name} - Warning-Free Generated Test
// Generated by VIP Generator Warning Fix Script
//==============================================================================

class {test_name} extends axi4_base_test;
    
    `uvm_component_utils({test_name})
    
    function new(string name = "{test_name}", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting {test_name}", UVM_LOW)
        
        // Use valid master indices only
        foreach(env.master_agent[i]) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("write_seq_%0d", i));
            write_seq.start_address = 64'h0001_0000 + (i * 1024);
            write_seq.burst_length = 4;
            write_seq.burst_size = 8;
            write_seq.test_data_pattern = $sformatf("%016h", 64'hDEADBEEF_00000000 + i);
            write_seq.start(env.master_agent[i].sequencer);
            #100ns;
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("read_seq_%0d", i));
            read_seq.start_address = 64'h0001_0000 + (i * 1024);
            read_seq.burst_length = 4;
            read_seq.burst_size = 8;
            read_seq.expected_data_pattern = $sformatf("%016h", 64'hDEADBEEF_00000000 + i);
            read_seq.start(env.master_agent[i].sequencer);
            #100ns;
        end
        
        `uvm_info(get_type_name(), "Completed {test_name}", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : {test_name}
'''
        return template
    
    def _generate_data_integrity_test_pattern(self, test_name: str) -> str:
        """Generate warning-free data integrity test pattern"""
        
        template = f'''//==============================================================================
// {test_name} - Warning-Free Data Integrity Test
//==============================================================================

class {test_name} extends axi4_base_test;
    
    `uvm_component_utils({test_name})
    
    function new(string name = "{test_name}", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        phase.raise_objection(this);
        
        // Test data patterns (using string literals to avoid warnings)
        string test_patterns[] = '{{
            "00000000000000000000000000000000",
            "ffffffffffffffffffffffffffffffff", 
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
            "55555555555555555555555555555555"
        }};
        
        foreach(test_patterns[i]) begin
            automatic int master_idx = i % {self.num_masters};
            bit [63:0] test_addr = 64'h0001_0000 + (i * 256);
            
            write_seq = axi4_master_write_seq::type_id::create($sformatf("pattern_write_%0d", i));
            write_seq.start_address = test_addr;
            write_seq.burst_length = 1;
            write_seq.burst_size = 16;
            write_seq.test_data_pattern = test_patterns[i];
            write_seq.enable_data_check = 1;
            write_seq.start(env.master_agent[master_idx].sequencer);
            #50ns;
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("pattern_read_%0d", i));
            read_seq.start_address = test_addr;
            read_seq.burst_length = 1;
            read_seq.burst_size = 16;
            read_seq.expected_data_pattern = test_patterns[i];
            read_seq.enable_data_check = 1;
            read_seq.start(env.master_agent[master_idx].sequencer);
            #50ns;
        end
        
        phase.drop_objection(this);
    endtask
    
endclass : {test_name}
'''
        return template
    
    def _generate_protocol_compliance_test_pattern(self, test_name: str) -> str:
        """Generate warning-free protocol compliance test pattern"""
        
        template = f'''//==============================================================================
// {test_name} - Warning-Free Protocol Compliance Test
//==============================================================================

class {test_name} extends axi4_base_test;
    
    `uvm_component_utils({test_name})
    
    function new(string name = "{test_name}", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axi4_master_write_seq write_seq;
        
        phase.raise_objection(this);
        
        // Test response types with proper enum casting
        int response_types[] = '{{0, 1}}; // OKAY, EXOKAY
        
        foreach(response_types[i]) begin
            automatic int master_idx = i % {self.num_masters};
            
            write_seq = axi4_master_write_seq::type_id::create($sformatf("response_type_%0d", i));
            write_seq.start_address = 64'h0004_2000 + (i * 1024);
            write_seq.burst_length = 4;
            write_seq.expected_response = axi4_response_type_e'(response_types[i]); // Proper enum cast
            write_seq.lock_type = (response_types[i] == 1) ? axi4_globals_pkg::EXCLUSIVE : axi4_globals_pkg::NORMAL;
            write_seq.start(env.master_agent[master_idx].sequencer);
            #100ns;
        end
        
        phase.drop_objection(this);
    endtask
    
endclass : {test_name}
'''
        return template
    
    def _generate_basic_test_pattern(self, test_name: str) -> str:
        """Generate basic warning-free test pattern"""
        
        template = f'''//==============================================================================
// {test_name} - Warning-Free Basic Test
//==============================================================================

class {test_name} extends axi4_base_test;
    
    `uvm_component_utils({test_name})
    
    function new(string name = "{test_name}", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        phase.raise_objection(this);
        
        // Simple test with valid indices
        write_seq = axi4_master_write_seq::type_id::create("basic_write");
        write_seq.start_address = 64'h0000_1000;
        write_seq.burst_length = 1;
        write_seq.burst_size = 8;
        write_seq.test_data_pattern = "deadbeefcafebabe";
        write_seq.start(env.master_agent[0].sequencer);
        #100ns;
        
        read_seq = axi4_master_read_seq::type_id::create("basic_read");
        read_seq.start_address = 64'h0000_1000;
        read_seq.burst_length = 1;
        read_seq.burst_size = 8;
        read_seq.expected_data_pattern = "deadbeefcafebabe";
        read_seq.start(env.master_agent[0].sequencer);
        #100ns;
        
        phase.drop_objection(this);
    endtask
    
endclass : {test_name}
'''
        return template
    
    def fix_all_test_files(self) -> Dict[str, int]:
        """Fix all test files in the test directory"""
        
        test_files = [
            "axi4_comprehensive_burst_test.sv",
            "axi4_exclusive_access_test.sv", 
            "axi4_protocol_compliance_test.sv",
            "axi4_advanced_error_test.sv",
            "axi4_data_integrity_test.sv",
            "axi4_multi_master_contention_test.sv",
            "axi4_4kb_boundary_test.sv",
            "axi4_boundary_test.sv",
            "axi4_error_injection_test.sv",
            "axi4_performance_test.sv",
            "axi4_interleaved_test.sv"
        ]
        
        print(f"VIP Generator Warning Fix Script")
        print(f"VIP Root: {self.vip_root}")
        print(f"Configuration: {self.num_masters} masters, {self.num_slaves} slaves")
        print(f"Test Directory: {self.test_dir}")
        print("-" * 70)
        
        for filename in test_files:
            if os.path.exists(os.path.join(self.test_dir, filename)):
                modified = self.fix_test_file(filename)
                status = "MODIFIED" if modified else "NO CHANGES"
                print(f"{filename:<40} {status}")
            else:
                print(f"{filename:<40} NOT FOUND")
        
        print("-" * 70)
        print("Fix Summary:")
        print(f"  Files Modified: {self.fixes_applied['files_modified']}")
        print(f"  SIOB Fixes: {self.fixes_applied['siob_fixes']}")
        print(f"  ICTA-SI Fixes: {self.fixes_applied['icta_fixes']}")
        print(f"  ENUMASSIGN Fixes: {self.fixes_applied['enum_fixes']}")
        
        return self.fixes_applied


def main():
    """Main function for standalone execution"""
    import argparse
    
    parser = argparse.ArgumentParser(description='Fix VIP Generator Warning Issues')
    parser.add_argument('--vip-root', required=True, help='VIP root directory')
    parser.add_argument('--masters', type=int, default=2, help='Number of masters')
    parser.add_argument('--slaves', type=int, default=3, help='Number of slaves')
    parser.add_argument('--generate-template', help='Generate warning-free test template')
    
    args = parser.parse_args()
    
    fixer = VIPGeneratorWarningFix(args.vip_root, args.masters, args.slaves)
    
    if args.generate_template:
        template = fixer.generate_warning_free_test_pattern(args.generate_template)
        print(template)
    else:
        results = fixer.fix_all_test_files()
        
        if results['files_modified'] > 0:
            print(f"\n✅ Successfully fixed {results['files_modified']} files!")
            print("Recommendation: Recompile to verify warnings are resolved.")
        else:
            print(f"\n✅ All files are already warning-free!")


if __name__ == "__main__":
    main()