#!/usr/bin/env python3
"""
VIP Unaligned Address Test Generator
Implements comprehensive unaligned address test scenarios
Based on tim_axi4_vip unaligned transfer and boundary testing
"""

import os
from datetime import datetime
from typing import Dict, List, Optional, Tuple

class VIPUnalignedAddressTestGenerator:
    """Generate unaligned address test sequences"""
    
    def __init__(self, config):
        self.config = config
        self.timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        # Unaligned scenarios
        self.unaligned_scenarios = {
            "basic_unaligned": [
                "byte_unaligned", "halfword_unaligned", "word_unaligned",
                "dword_unaligned", "random_unaligned"
            ],
            "boundary_crossing": [
                "cross_word_boundary", "cross_dword_boundary", 
                "cross_bus_width_boundary", "cross_4kb_boundary",
                "cross_cache_line_boundary"
            ],
            "burst_unaligned": [
                "incr_burst_unaligned", "wrap_burst_unaligned",
                "fixed_burst_unaligned", "mixed_burst_unaligned"
            ],
            "size_mismatch": [
                "large_size_unaligned_addr", "narrow_unaligned",
                "max_size_unaligned", "variable_size_unaligned"
            ],
            "corner_cases": [
                "near_4kb_boundary", "wrap_around_unaligned",
                "exclusive_unaligned", "sparse_unaligned"
            ]
        }
        
        # Alignment requirements per size
        self.alignment_requirements = {
            0: 1,    # 1 byte - no alignment required
            1: 2,    # 2 bytes - 2-byte aligned
            2: 4,    # 4 bytes - 4-byte aligned
            3: 8,    # 8 bytes - 8-byte aligned
            4: 16,   # 16 bytes - 16-byte aligned
            5: 32,   # 32 bytes - 32-byte aligned
            6: 64,   # 64 bytes - 64-byte aligned
            7: 128   # 128 bytes - 128-byte aligned
        }
        
    def generate_unaligned_address_tests(self, output_dir: str):
        """Generate all unaligned address test components"""
        
        # Create directory structure
        unaligned_dir = os.path.join(output_dir, "unaligned_address")
        os.makedirs(unaligned_dir, exist_ok=True)
        
        # Generate components
        self._generate_alignment_calculator(unaligned_dir)
        self._generate_unaligned_checker(unaligned_dir)
        self._generate_unaligned_test_sequences(unaligned_dir)
        self._generate_boundary_detector(unaligned_dir)
        self._generate_unaligned_coverage(unaligned_dir)
        
        return True
        
    def _generate_alignment_calculator(self, output_dir: str):
        """Generate alignment calculation utilities"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Alignment Calculator
// Generated: {self.timestamp}
// Description: Calculates alignment requirements and violations
//------------------------------------------------------------------------------

class axi4_alignment_calculator extends uvm_object;
    
    `uvm_object_utils(axi4_alignment_calculator)
    
    // Constructor
    function new(string name = "axi4_alignment_calculator");
        super.new(name);
    endfunction
    
    // Check if address is naturally aligned for given size
    function bit is_naturally_aligned(bit [63:0] addr, int unsigned size);
        int unsigned alignment_mask = (1 << size) - 1;
        return (addr & alignment_mask) == 0;
    endfunction
    
    // Calculate alignment offset
    function int unsigned get_alignment_offset(bit [63:0] addr, int unsigned size);
        int unsigned alignment_mask = (1 << size) - 1;
        return addr & alignment_mask;
    endfunction
    
    // Get required alignment for burst
    function int unsigned get_burst_alignment(axi4_burst_e burst_type, int unsigned size, int unsigned len);
        case (burst_type)
            AXI4_FIXED: return 1 << size; // Natural alignment
            AXI4_INCR: return 1; // No specific alignment required
            AXI4_WRAP: return (len + 1) * (1 << size); // Total burst size aligned
        endcase
    endfunction
    
    // Calculate aligned address
    function bit [63:0] align_address(bit [63:0] addr, int unsigned size);
        int unsigned alignment_mask = ~((1 << size) - 1);
        return addr & alignment_mask;
    endfunction
    
    // Calculate next aligned address
    function bit [63:0] next_aligned_address(bit [63:0] addr, int unsigned size);
        bit [63:0] aligned = align_address(addr, size);
        if (aligned == addr)
            return addr;
        else
            return aligned + (1 << size);
    endfunction
    
    // Check if transfer crosses alignment boundary
    function bit crosses_alignment_boundary(bit [63:0] addr, int unsigned size, int unsigned len, axi4_burst_e burst_type);
        bit [63:0] start_addr = addr;
        bit [63:0] end_addr;
        
        case (burst_type)
            AXI4_FIXED: begin
                // Fixed burst doesn't cross boundaries
                return 0;
            end
            
            AXI4_INCR: begin
                end_addr = start_addr + ((len + 1) * (1 << size)) - 1;
                // Check if start and end are in different aligned regions
                return (align_address(start_addr, size) != align_address(end_addr, size));
            end
            
            AXI4_WRAP: begin
                // WRAP inherently handles boundaries
                return 0;
            end
        endcase
    endfunction
    
    // Calculate boundary crossings
    function int unsigned count_boundary_crossings(bit [63:0] addr, int unsigned size, int unsigned len, int unsigned boundary_size);
        bit [63:0] current_addr = addr;
        int unsigned crossings = 0;
        bit [63:0] boundary_mask = ~(boundary_size - 1);
        bit [63:0] current_boundary, next_boundary;
        
        for (int i = 0; i <= len; i++) begin
            current_boundary = current_addr & boundary_mask;
            next_boundary = (current_addr + (1 << size) - 1) & boundary_mask;
            
            if (current_boundary != next_boundary) begin
                crossings++;
            end
            
            current_addr += (1 << size);
        end
        
        return crossings;
    endfunction
    
    // Check 4KB boundary crossing
    function bit crosses_4kb_boundary(bit [63:0] addr, int unsigned size, int unsigned len);
        bit [63:0] start_addr = addr;
        bit [63:0] end_addr = addr + ((len + 1) * (1 << size)) - 1;
        
        // Check if in different 4KB pages
        return ((start_addr >> 12) != (end_addr >> 12));
    endfunction
    
    // Calculate effective address for unaligned access
    function bit [63:0] calculate_effective_address(bit [63:0] addr, int unsigned byte_offset);
        return addr + byte_offset;
    endfunction
    
    // Get byte lanes for unaligned transfer
    function bit [15:0] get_byte_lanes(bit [63:0] addr, int unsigned size, int unsigned bus_bytes);
        bit [15:0] lanes = 0;
        int unsigned start_lane = addr & (bus_bytes - 1);
        int unsigned num_bytes = 1 << size;
        
        for (int i = 0; i < num_bytes; i++) begin
            if ((start_lane + i) < bus_bytes) begin
                lanes[start_lane + i] = 1'b1;
            end
        end
        
        return lanes;
    endfunction
    
    // Calculate wrap boundary for unaligned WRAP burst
    function bit [63:0] calculate_wrap_boundary(bit [63:0] addr, int unsigned size, int unsigned len);
        int unsigned total_bytes = (len + 1) * (1 << size);
        bit [63:0] boundary_mask = ~(total_bytes - 1);
        return addr & boundary_mask;
    endfunction
    
    // Check if address is cache line aligned
    function bit is_cache_line_aligned(bit [63:0] addr, int unsigned cache_line_size = 64);
        return (addr & (cache_line_size - 1)) == 0;
    endfunction
    
    // Calculate padding for alignment
    function int unsigned calculate_padding(bit [63:0] addr, int unsigned required_alignment);
        int unsigned offset = addr & (required_alignment - 1);
        if (offset == 0)
            return 0;
        else
            return required_alignment - offset;
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_alignment_calculator.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_unaligned_checker(self, output_dir: str):
        """Generate unaligned address checker"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Unaligned Address Checker
// Generated: {self.timestamp}
// Description: Validates unaligned address handling and data integrity
//------------------------------------------------------------------------------

class axi4_unaligned_checker extends uvm_component;
    
    `uvm_component_utils(axi4_unaligned_checker)
    
    // Analysis port
    uvm_analysis_imp #(axi4_transaction, axi4_unaligned_checker) analysis_export;
    
    // Configuration
    axi4_config cfg;
    axi4_alignment_calculator align_calc;
    
    // Memory model for unaligned accesses
    bit [7:0] memory_model[bit[63:0]];
    
    // Statistics
    int unsigned unaligned_write_count;
    int unsigned unaligned_read_count;
    int unsigned boundary_crossing_count;
    int unsigned wrap_unaligned_count;
    int unsigned exclusive_unaligned_count;
    int unsigned data_misalignment_errors;
    int unsigned protocol_violations;
    
    // Tracking
    typedef struct {
        bit [63:0] addr;
        int size;
        int len;
        axi4_burst_e burst_type;
        bit is_unaligned;
        int alignment_offset;
        bit crosses_4kb;
        time timestamp;
    } unaligned_info_t;
    
    unaligned_info_t active_transfers[bit[7:0]];
    
    // Constructor
    function new(string name = "axi4_unaligned_checker", uvm_component parent = null);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(axi4_config)::get(this, "", "axi4_config", cfg)) begin
            `uvm_fatal("CONFIG", "Failed to get axi4_config")
        end
        
        align_calc = axi4_alignment_calculator::type_id::create("align_calc");
    endfunction
    
    // Write method
    function void write(axi4_transaction trans);
        check_unaligned_access(trans);
    endfunction
    
    // Check unaligned access
    function void check_unaligned_access(axi4_transaction trans);
        unaligned_info_t info;
        
        // Gather transfer info
        info.addr = trans.addr;
        info.size = trans.size;
        info.len = trans.len;
        info.burst_type = trans.burst;
        info.is_unaligned = !align_calc.is_naturally_aligned(trans.addr, trans.size);
        info.alignment_offset = align_calc.get_alignment_offset(trans.addr, trans.size);
        info.crosses_4kb = align_calc.crosses_4kb_boundary(trans.addr, trans.size, trans.len);
        info.timestamp = $time;
        
        // Store info
        active_transfers[trans.id] = info;
        
        // Check based on transaction type
        if (trans.trans_type == AXI4_WRITE) begin
            check_unaligned_write(trans, info);
        end else begin
            check_unaligned_read(trans, info);
        end
        
        // Check for violations
        check_alignment_violations(trans, info);
    endfunction
    
    // Check unaligned write
    function void check_unaligned_write(axi4_transaction trans, unaligned_info_t info);
        if (info.is_unaligned) begin
            unaligned_write_count++;
            
            `uvm_info(get_name(), $sformatf("Unaligned write: addr=%0h, size=%0d, offset=%0d", 
                                           info.addr, 1 << info.size, info.alignment_offset), UVM_MEDIUM)
            
            // Store data with byte-level granularity
            store_unaligned_data(trans);
            
            // Check strobe generation for unaligned
            check_unaligned_strobes(trans, info);
        end
        
        if (info.crosses_4kb) begin
            boundary_crossing_count++;
            `uvm_warning(get_name(), $sformatf("Write crosses 4KB boundary: addr=%0h, len=%0d", info.addr, info.len))
        end
    endfunction
    
    // Check unaligned read
    function void check_unaligned_read(axi4_transaction trans, unaligned_info_t info);
        if (info.is_unaligned) begin
            unaligned_read_count++;
            
            `uvm_info(get_name(), $sformatf("Unaligned read: addr=%0h, size=%0d, offset=%0d", 
                                           info.addr, 1 << info.size, info.alignment_offset), UVM_MEDIUM)
            
            // Verify read data alignment
            verify_unaligned_read_data(trans, info);
        end
        
        if (info.crosses_4kb) begin
            boundary_crossing_count++;
            `uvm_warning(get_name(), $sformatf("Read crosses 4KB boundary: addr=%0h, len=%0d", info.addr, info.len))
        end
    endfunction
    
    // Store unaligned write data
    function void store_unaligned_data(axi4_transaction trans);
        for (int beat = 0; beat <= trans.len; beat++) begin
            bit [63:0] beat_addr;
            
            // Calculate beat address
            case (trans.burst)
                AXI4_FIXED: beat_addr = trans.addr;
                AXI4_INCR: beat_addr = trans.addr + beat * (1 << trans.size);
                AXI4_WRAP: begin
                    bit [63:0] wrap_boundary = align_calc.calculate_wrap_boundary(trans.addr, trans.size, trans.len);
                    int wrap_size = (trans.len + 1) * (1 << trans.size);
                    beat_addr = wrap_boundary + ((trans.addr - wrap_boundary + beat * (1 << trans.size)) % wrap_size);
                end
            endcase
            
            // Store bytes based on strobe
            for (int byte_idx = 0; byte_idx < cfg.data_width/8; byte_idx++) begin
                if (trans.strb[beat][byte_idx]) begin
                    memory_model[beat_addr + byte_idx] = trans.data[beat][byte_idx*8 +: 8];
                end
            end
        end
    endfunction
    
    // Check unaligned strobes
    function void check_unaligned_strobes(axi4_transaction trans, unaligned_info_t info);
        bit [15:0] expected_lanes;
        int bus_bytes = cfg.data_width / 8;
        
        for (int beat = 0; beat <= trans.len; beat++) begin
            bit [63:0] beat_addr;
            
            // Calculate beat address
            case (trans.burst)
                AXI4_FIXED: beat_addr = trans.addr;
                AXI4_INCR: beat_addr = trans.addr + beat * (1 << trans.size);
                AXI4_WRAP: begin
                    bit [63:0] wrap_boundary = align_calc.calculate_wrap_boundary(trans.addr, trans.size, trans.len);
                    int wrap_size = (trans.len + 1) * (1 << trans.size);
                    beat_addr = wrap_boundary + ((trans.addr - wrap_boundary + beat * (1 << trans.size)) % wrap_size);
                end
            endcase
            
            // Get expected byte lanes
            expected_lanes = align_calc.get_byte_lanes(beat_addr, trans.size, bus_bytes);
            
            // Compare with actual strobes
            for (int i = 0; i < bus_bytes; i++) begin
                if (expected_lanes[i] != trans.strb[beat][i]) begin
                    `uvm_error(get_name(), $sformatf("Strobe mismatch for unaligned access at beat %0d, lane %0d", beat, i))
                    data_misalignment_errors++;
                end
            end
        end
    endfunction
    
    // Verify unaligned read data
    function void verify_unaligned_read_data(axi4_transaction trans, unaligned_info_t info);
        for (int beat = 0; beat <= trans.len; beat++) begin
            bit [63:0] beat_addr;
            bit [1023:0] expected_data = 0;
            
            // Calculate beat address (same as write)
            case (trans.burst)
                AXI4_FIXED: beat_addr = trans.addr;
                AXI4_INCR: beat_addr = trans.addr + beat * (1 << trans.size);
                AXI4_WRAP: begin
                    bit [63:0] wrap_boundary = align_calc.calculate_wrap_boundary(trans.addr, trans.size, trans.len);
                    int wrap_size = (trans.len + 1) * (1 << trans.size);
                    beat_addr = wrap_boundary + ((trans.addr - wrap_boundary + beat * (1 << trans.size)) % wrap_size);
                end
            endcase
            
            // Build expected data from memory model
            for (int byte_idx = 0; byte_idx < cfg.data_width/8; byte_idx++) begin
                if (memory_model.exists(beat_addr + byte_idx)) begin
                    expected_data[byte_idx*8 +: 8] = memory_model[beat_addr + byte_idx];
                end
            end
            
            // For unaligned reads, only compare relevant bytes
            bit [15:0] relevant_lanes = align_calc.get_byte_lanes(beat_addr, trans.size, cfg.data_width/8);
            
            for (int i = 0; i < cfg.data_width/8; i++) begin
                if (relevant_lanes[i]) begin
                    if (expected_data[i*8 +: 8] !== trans.data[beat][i*8 +: 8]) begin
                        `uvm_error(get_name(), $sformatf("Read data mismatch at beat %0d, byte %0d: Expected=%0h, Got=%0h",
                                                        beat, i, expected_data[i*8 +: 8], trans.data[beat][i*8 +: 8]))
                        data_misalignment_errors++;
                    end
                end
            end
        end
    endfunction
    
    // Check alignment violations
    function void check_alignment_violations(axi4_transaction trans, unaligned_info_t info);
        // WRAP burst must be aligned to total size
        if (trans.burst == AXI4_WRAP) begin
            int total_bytes = (trans.len + 1) * (1 << trans.size);
            if (trans.addr & (total_bytes - 1)) begin
                `uvm_error(get_name(), $sformatf("WRAP burst not aligned to total size: addr=%0h, total_bytes=%0d",
                                                trans.addr, total_bytes))
                protocol_violations++;
                wrap_unaligned_count++;
            end
        end
        
        // Exclusive access must be naturally aligned
        if (trans.lock == 1'b1 && info.is_unaligned) begin
            `uvm_error(get_name(), $sformatf("Exclusive access must be aligned: addr=%0h, size=%0d",
                                            trans.addr, 1 << trans.size))
            protocol_violations++;
            exclusive_unaligned_count++;
        end
        
        // Check 4KB boundary crossing
        if (info.crosses_4kb) begin
            `uvm_error(get_name(), "Transaction crosses 4KB boundary")
            protocol_violations++;
        end
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Unaligned Address Checker Report ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Unaligned writes: %0d", unaligned_write_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Unaligned reads: %0d", unaligned_read_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Boundary crossings: %0d", boundary_crossing_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("WRAP unaligned: %0d", wrap_unaligned_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Exclusive unaligned: %0d", exclusive_unaligned_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Data misalignment errors: %0d", data_misalignment_errors), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Protocol violations: %0d", protocol_violations), UVM_LOW)
        
        if (data_misalignment_errors > 0 || protocol_violations > 0) begin
            `uvm_error(get_name(), "Unaligned address handling errors detected!")
        end
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_unaligned_checker.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_unaligned_test_sequences(self, output_dir: str):
        """Generate unaligned address test sequences"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Unaligned Address Test Sequences
// Generated: {self.timestamp}
// Description: Comprehensive unaligned address test scenarios
//------------------------------------------------------------------------------

// Base unaligned test sequence
class unaligned_base_sequence extends axi4_base_test_sequence;
    
    `uvm_object_utils(unaligned_base_sequence)
    
    // Configuration
    rand bit [5:0] unalign_offset;
    rand int unsigned target_size;
    
    axi4_alignment_calculator align_calc;
    
    constraint unaligned_c {
        unalign_offset inside {[1:63]};
        target_size inside {[0:6]}; // Up to 64-byte transfers
    }
    
    // Constructor
    function new(string name = "unaligned_base_sequence");
        super.new(name);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        align_calc = axi4_alignment_calculator::type_id::create("align_calc");
    endfunction
    
    // Helper to create unaligned address
    function bit [63:0] create_unaligned_address(bit [63:0] base_addr, int size, int offset);
        bit [63:0] aligned = base_addr & ~((1 << size) - 1);
        return aligned + offset;
    endfunction
    
endclass

// Basic unaligned write test
class unaligned_write_sequence extends unaligned_base_sequence;
    
    `uvm_object_utils(unaligned_write_sequence)
    
    function new(string name = "unaligned_write_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        `uvm_info(get_type_name(), "Starting unaligned write sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            trans = axi4_transaction::type_id::create("trans");
            
            // First randomize normally
            assert(trans.randomize() with {
                trans_type == AXI4_WRITE;
                size inside {[1:3]}; // 2 to 8 byte transfers
                burst_type == AXI4_INCR;
                burst_len inside {[0:7]};
            });
            
            // Make address unaligned
            trans.addr = create_unaligned_address(trans.addr, trans.size, $urandom_range(1, (1 << trans.size) - 1));
            
            `uvm_info(get_type_name(), $sformatf("Unaligned write: addr=%0h, size=%0d bytes, offset=%0d",
                                               trans.addr, 1 << trans.size, trans.addr & ((1 << trans.size) - 1)), UVM_MEDIUM)
            
            start_item(trans);
            finish_item(trans);
            
            wait_random_delay();
        end
    endtask
    
endclass

// Unaligned read sequence
class unaligned_read_sequence extends unaligned_base_sequence;
    
    `uvm_object_utils(unaligned_read_sequence)
    
    function new(string name = "unaligned_read_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        `uvm_info(get_type_name(), "Starting unaligned read sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            trans = axi4_transaction::type_id::create("trans");
            
            assert(trans.randomize() with {
                trans_type == AXI4_READ;
                size inside {[1:3]}; // 2 to 8 byte transfers
                burst_type == AXI4_INCR;
                burst_len inside {[0:7]};
            });
            
            // Make address unaligned
            trans.addr = create_unaligned_address(trans.addr, trans.size, $urandom_range(1, (1 << trans.size) - 1));
            
            start_item(trans);
            finish_item(trans);
            
            wait_random_delay();
        end
    endtask
    
endclass

// Boundary crossing test
class boundary_crossing_sequence extends unaligned_base_sequence;
    
    `uvm_object_utils(boundary_crossing_sequence)
    
    function new(string name = "boundary_crossing_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        bit [63:0] boundary_addresses[] = '{
            64'h0000_0FFE,  // Near 4KB boundary
            64'h0000_0FFC,  // 4 bytes from 4KB
            64'h0000_0FF8,  // 8 bytes from 4KB
            64'h0000_0FF0,  // 16 bytes from 4KB
            64'h0000_7FFC,  // Near 32KB boundary
            64'h0000_FFFC   // Near 64KB boundary
        };
        
        `uvm_info(get_type_name(), "Starting boundary crossing sequence", UVM_LOW)
        
        foreach (boundary_addresses[i]) begin
            trans = axi4_transaction::type_id::create("trans");
            
            assert(trans.randomize() with {
                trans_type inside {AXI4_WRITE, AXI4_READ};
                addr == boundary_addresses[i];
                size inside {[2:4]}; // 4 to 16 byte transfers
                burst_type == AXI4_INCR;
                burst_len inside {[1:3]}; // Will cross boundary
            });
            
            `uvm_info(get_type_name(), $sformatf("Boundary crossing: addr=%0h, size=%0d, len=%0d",
                                               trans.addr, 1 << trans.size, trans.len + 1), UVM_MEDIUM)
            
            start_item(trans);
            finish_item(trans);
            
            // Check if it would cross 4KB
            if (align_calc.crosses_4kb_boundary(trans.addr, trans.size, trans.len)) begin
                `uvm_info(get_type_name(), "Transaction crosses 4KB boundary", UVM_HIGH)
            end
            
            #10ns;
        end
    endtask
    
endclass

// Unaligned WRAP burst test
class unaligned_wrap_sequence extends unaligned_base_sequence;
    
    `uvm_object_utils(unaligned_wrap_sequence)
    
    function new(string name = "unaligned_wrap_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        `uvm_info(get_type_name(), "Starting unaligned WRAP sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            trans = axi4_transaction::type_id::create("trans");
            
            // WRAP burst with potential misalignment
            assert(trans.randomize() with {
                trans_type inside {AXI4_WRITE, AXI4_READ};
                size inside {[1:3]}; // 2 to 8 bytes
                burst_type == AXI4_WRAP;
                burst_len inside {1, 3, 7, 15}; // Valid WRAP lengths
            });
            
            // Intentionally misalign for WRAP (should be caught)
            if ($urandom_range(0, 1)) begin
                int total_bytes = (trans.len + 1) * (1 << trans.size);
                trans.addr = trans.addr | $urandom_range(1, total_bytes - 1);
                `uvm_info(get_type_name(), $sformatf("Intentionally misaligned WRAP: addr=%0h, total_bytes=%0d",
                                                   trans.addr, total_bytes), UVM_MEDIUM)
            end
            
            start_item(trans);
            finish_item(trans);
            
            wait_random_delay();
        end
    endtask
    
endclass

// Cache line crossing test
class cache_line_crossing_sequence extends unaligned_base_sequence;
    
    `uvm_object_utils(cache_line_crossing_sequence)
    
    function new(string name = "cache_line_crossing_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        int cache_line_size = 64; // Typical cache line
        
        `uvm_info(get_type_name(), "Starting cache line crossing sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            trans = axi4_transaction::type_id::create("trans");
            
            // Start near cache line boundary
            bit [63:0] base_addr = ($urandom & ~(cache_line_size - 1)) + cache_line_size - 8;
            
            assert(trans.randomize() with {
                trans_type inside {AXI4_WRITE, AXI4_READ};
                addr == base_addr;
                size inside {[2:4]}; // 4 to 16 bytes
                burst_type == AXI4_INCR;
                burst_len inside {[1:3]};
            });
            
            `uvm_info(get_type_name(), $sformatf("Cache line crossing: addr=%0h crosses %0d-byte boundary",
                                               trans.addr, cache_line_size), UVM_MEDIUM)
            
            start_item(trans);
            finish_item(trans);
            
            wait_random_delay();
        end
    endtask
    
endclass

// Mixed size unaligned test
class mixed_size_unaligned_sequence extends unaligned_base_sequence;
    
    `uvm_object_utils(mixed_size_unaligned_sequence)
    
    function new(string name = "mixed_size_unaligned_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        bit [63:0] base_addr = 64'h1000_0000;
        
        `uvm_info(get_type_name(), "Starting mixed size unaligned sequence", UVM_LOW)
        
        // Test each size with different alignments
        for (int size = 0; size <= 6; size++) begin
            for (int offset = 0; offset < (1 << size); offset++) begin
                trans = axi4_transaction::type_id::create("trans");
                
                assert(trans.randomize() with {
                    trans_type == AXI4_WRITE;
                    addr == base_addr + offset;
                    size == local::size;
                    burst_type == AXI4_INCR;
                    burst_len == 0; // Single transfer
                });
                
                `uvm_info(get_type_name(), $sformatf("Size %0d (%0d bytes) at offset %0d: %s",
                                                   size, 1 << size, offset,
                                                   align_calc.is_naturally_aligned(trans.addr, trans.size) ? 
                                                   "aligned" : "unaligned"), UVM_HIGH)
                
                start_item(trans);
                finish_item(trans);
                
                base_addr += 'h100;
            end
        end
    endtask
    
endclass

// Exclusive unaligned test (should fail)
class exclusive_unaligned_sequence extends unaligned_base_sequence;
    
    `uvm_object_utils(exclusive_unaligned_sequence)
    
    function new(string name = "exclusive_unaligned_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction ex_read, ex_write;
        
        `uvm_info(get_type_name(), "Starting exclusive unaligned sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            // Exclusive read with unaligned address
            ex_read = axi4_transaction::type_id::create("ex_read");
            
            assert(ex_read.randomize() with {
                trans_type == AXI4_READ;
                size inside {[1:3]}; // 2 to 8 bytes
                burst_type == AXI4_INCR;
                burst_len == 0; // Single transfer for exclusive
                lock == 1'b1; // Exclusive
            });
            
            // Make unaligned
            ex_read.addr = create_unaligned_address(ex_read.addr, ex_read.size, 
                                                   $urandom_range(1, (1 << ex_read.size) - 1));
            
            `uvm_warning(get_type_name(), $sformatf("Exclusive read with unaligned address: %0h (should fail)", ex_read.addr))
            
            start_item(ex_read);
            finish_item(ex_read);
            
            // Exclusive write
            ex_write = axi4_transaction::type_id::create("ex_write");
            
            assert(ex_write.randomize() with {
                trans_type == AXI4_WRITE;
                addr == ex_read.addr;
                id == ex_read.id;
                size == ex_read.size;
                burst_type == AXI4_INCR;
                burst_len == 0;
                lock == 1'b1; // Exclusive
            });
            
            start_item(ex_write);
            finish_item(ex_write);
            
            // Should not get EXOKAY for unaligned
            if (ex_write.resp == AXI4_EXOKAY) begin
                `uvm_error(get_type_name(), "Exclusive succeeded with unaligned address!")
            end
            
            wait_random_delay();
        end
    endtask
    
endclass

// Near 4KB boundary test
class near_4kb_boundary_sequence extends unaligned_base_sequence;
    
    `uvm_object_utils(near_4kb_boundary_sequence)
    
    function new(string name = "near_4kb_boundary_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        `uvm_info(get_type_name(), "Starting near 4KB boundary sequence", UVM_LOW)
        
        // Test various distances from 4KB boundary
        for (int distance = 1; distance <= 128; distance *= 2) begin
            trans = axi4_transaction::type_id::create("trans");
            
            bit [63:0] boundary_addr = 64'h1000 - distance; // Just before 4KB
            
            assert(trans.randomize() with {
                trans_type inside {AXI4_WRITE, AXI4_READ};
                addr == boundary_addr;
                size inside {[0:4]}; // 1 to 16 bytes
                burst_type == AXI4_INCR;
                burst_len inside {[0:15]};
            });
            
            // Calculate if crosses
            bit crosses = align_calc.crosses_4kb_boundary(trans.addr, trans.size, trans.len);
            
            `uvm_info(get_type_name(), $sformatf("Near 4KB test: addr=%0h, size=%0d, len=%0d, crosses=%0b",
                                               trans.addr, 1 << trans.size, trans.len + 1, crosses), UVM_MEDIUM)
            
            start_item(trans);
            finish_item(trans);
            
            #10ns;
        end
    endtask
    
endclass

// Maximum unaligned stress test
class unaligned_stress_sequence extends unaligned_base_sequence;
    
    `uvm_object_utils(unaligned_stress_sequence)
    
    function new(string name = "unaligned_stress_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans_q[$];
        
        `uvm_info(get_type_name(), "Starting unaligned stress test", UVM_LOW)
        
        // Generate many unaligned transfers
        repeat (100) begin
            axi4_transaction trans = axi4_transaction::type_id::create("trans");
            
            assert(trans.randomize() with {
                trans_type inside {AXI4_WRITE, AXI4_READ};
                size inside {[0:4]}; // Up to 16 bytes
                burst_type inside {AXI4_FIXED, AXI4_INCR, AXI4_WRAP};
                burst_len inside {[0:15]};
            });
            
            // Various unalignment strategies
            case ($urandom_range(0, 3))
                0: begin // Random offset
                    trans.addr = trans.addr + $urandom_range(1, 7);
                end
                1: begin // Near boundary
                    trans.addr = (trans.addr & ~12'hFFF) + 12'hFF0 + $urandom_range(0, 15);
                end
                2: begin // Specific misalignment
                    trans.addr = create_unaligned_address(trans.addr, trans.size, 
                                                         $urandom_range(1, (1 << trans.size) - 1));
                end
                3: begin // Keep aligned (control)
                    trans.addr = align_calc.align_address(trans.addr, trans.size);
                end
            endcase
            
            // Fix WRAP alignment if needed
            if (trans.burst == AXI4_WRAP) begin
                int total_bytes = (trans.len + 1) * (1 << trans.size);
                trans.addr = trans.addr & ~(total_bytes - 1);
            end
            
            trans_q.push_back(trans);
        end
        
        // Send all transactions
        foreach (trans_q[i]) begin
            fork
                automatic int idx = i;
                begin
                    #(idx * 0.1ns);
                    start_item(trans_q[idx]);
                    finish_item(trans_q[idx]);
                end
            join_none
        end
        
        wait fork;
        
        `uvm_info(get_type_name(), "Unaligned stress test complete", UVM_LOW)
    endtask
    
endclass
'''
        
        filepath = os.path.join(output_dir, "unaligned_address_test_sequences.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_boundary_detector(self, output_dir: str):
        """Generate boundary crossing detector"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Boundary Detector
// Generated: {self.timestamp}
// Description: Detects various boundary crossing conditions
//------------------------------------------------------------------------------

class axi4_boundary_detector extends uvm_component;
    
    `uvm_component_utils(axi4_boundary_detector)
    
    // Analysis export
    uvm_analysis_imp #(axi4_transaction, axi4_boundary_detector) analysis_export;
    
    // Configuration
    axi4_config cfg;
    
    // Boundary sizes to check
    int unsigned boundary_sizes[$] = '{
        64,      // Cache line
        256,     // Typical L2 cache line
        1024,    // 1KB
        4096,    // 4KB page
        65536,   // 64KB
        1048576  // 1MB
    };
    
    // Statistics per boundary type
    int unsigned boundary_crossings[int unsigned];
    int unsigned near_boundary_accesses[int unsigned];
    
    // Detailed tracking
    typedef struct {
        bit [63:0] start_addr;
        bit [63:0] end_addr;
        int size;
        int len;
        axi4_burst_e burst_type;
        int boundaries_crossed[int unsigned];
        time timestamp;
    } boundary_info_t;
    
    boundary_info_t transaction_history[$];
    
    // Constructor
    function new(string name = "axi4_boundary_detector", uvm_component parent = null);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(axi4_config)::get(this, "", "axi4_config", cfg)) begin
            `uvm_fatal("CONFIG", "Failed to get axi4_config")
        end
        
        // Initialize statistics
        foreach (boundary_sizes[i]) begin
            boundary_crossings[boundary_sizes[i]] = 0;
            near_boundary_accesses[boundary_sizes[i]] = 0;
        end
    endfunction
    
    // Write method
    function void write(axi4_transaction trans);
        detect_boundary_crossings(trans);
    endfunction
    
    // Detect boundary crossings
    function void detect_boundary_crossings(axi4_transaction trans);
        boundary_info_t info;
        
        // Calculate transfer span
        info.start_addr = trans.addr;
        info.size = trans.size;
        info.len = trans.len;
        info.burst_type = trans.burst;
        info.timestamp = $time;
        
        // Calculate end address based on burst type
        case (trans.burst)
            AXI4_FIXED: begin
                info.end_addr = trans.addr + (1 << trans.size) - 1;
            end
            
            AXI4_INCR: begin
                info.end_addr = trans.addr + ((trans.len + 1) * (1 << trans.size)) - 1;
            end
            
            AXI4_WRAP: begin
                // WRAP doesn't cross its wrap boundary
                int wrap_size = (trans.len + 1) * (1 << trans.size);
                info.end_addr = trans.addr + wrap_size - 1;
            end
        endcase
        
        // Check each boundary type
        foreach (boundary_sizes[i]) begin
            int boundary_size = boundary_sizes[i];
            
            // Check if crosses boundary
            if (crosses_boundary(info.start_addr, info.end_addr, boundary_size)) begin
                boundary_crossings[boundary_size]++;
                info.boundaries_crossed[boundary_size] = 1;
                
                `uvm_info(get_name(), $sformatf("Transaction crosses %0d-byte boundary: addr=%0h, end=%0h",
                                               boundary_size, info.start_addr, info.end_addr), UVM_MEDIUM)
            end
            
            // Check if near boundary (within 16 bytes)
            if (is_near_boundary(info.start_addr, boundary_size, 16) ||
                is_near_boundary(info.end_addr, boundary_size, 16)) begin
                near_boundary_accesses[boundary_size]++;
            end
        end
        
        // Special check for 4KB
        if (crosses_boundary(info.start_addr, info.end_addr, 4096)) begin
            `uvm_warning(get_name(), $sformatf("4KB boundary crossing detected: addr=%0h, len=%0d, size=%0d",
                                             trans.addr, trans.len + 1, 1 << trans.size))
        end
        
        // Store history
        transaction_history.push_back(info);
        if (transaction_history.size() > 1000) begin
            void'(transaction_history.pop_front());
        end
    endfunction
    
    // Check if crosses specific boundary
    function bit crosses_boundary(bit [63:0] start_addr, bit [63:0] end_addr, int unsigned boundary_size);
        bit [63:0] start_boundary = start_addr / boundary_size;
        bit [63:0] end_boundary = end_addr / boundary_size;
        return (start_boundary != end_boundary);
    endfunction
    
    // Check if near boundary
    function bit is_near_boundary(bit [63:0] addr, int unsigned boundary_size, int unsigned threshold);
        bit [63:0] offset = addr % boundary_size;
        // Near start of boundary
        if (offset < threshold) return 1;
        // Near end of boundary
        if (offset > (boundary_size - threshold)) return 1;
        return 0;
    endfunction
    
    // Get boundary crossing count for specific address range
    function int get_crossings_in_range(bit [63:0] start_addr, bit [63:0] end_addr, int unsigned boundary_size);
        int count = 0;
        bit [63:0] current_boundary = start_addr / boundary_size;
        bit [63:0] end_boundary = end_addr / boundary_size;
        
        while (current_boundary < end_boundary) begin
            count++;
            current_boundary++;
        end
        
        return count;
    endfunction
    
    // Analyze access patterns
    function void analyze_access_patterns();
        int total_transactions = transaction_history.size();
        
        `uvm_info(get_name(), "=== Boundary Access Pattern Analysis ===", UVM_LOW)
        
        foreach (boundary_sizes[i]) begin
            int boundary = boundary_sizes[i];
            real crossing_rate = (total_transactions > 0) ? 
                                real'(boundary_crossings[boundary]) / total_transactions * 100.0 : 0.0;
            real near_rate = (total_transactions > 0) ? 
                            real'(near_boundary_accesses[boundary]) / total_transactions * 100.0 : 0.0;
            
            `uvm_info(get_name(), $sformatf("%0d-byte boundary: Crossings=%0d (%.1f%%), Near=%0d (%.1f%%)",
                                           boundary, boundary_crossings[boundary], crossing_rate,
                                           near_boundary_accesses[boundary], near_rate), UVM_LOW)
        end
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Boundary Detector Report ===", UVM_LOW)
        
        // Report all boundary statistics
        foreach (boundary_sizes[i]) begin
            int boundary = boundary_sizes[i];
            `uvm_info(get_name(), $sformatf("%0d-byte boundary crossings: %0d",
                                           boundary, boundary_crossings[boundary]), UVM_LOW)
        end
        
        // Special emphasis on 4KB
        if (boundary_crossings[4096] > 0) begin
            `uvm_error(get_name(), $sformatf("Found %0d transactions crossing 4KB boundary!",
                                           boundary_crossings[4096]))
        end
        
        // Analyze patterns
        analyze_access_patterns();
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_boundary_detector.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_unaligned_coverage(self, output_dir: str):
        """Generate unaligned address coverage model"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Unaligned Address Coverage
// Generated: {self.timestamp}
// Description: Functional coverage for unaligned address scenarios
//------------------------------------------------------------------------------

class axi4_unaligned_coverage extends uvm_subscriber #(axi4_transaction);
    
    `uvm_component_utils(axi4_unaligned_coverage)
    
    // Transaction handle
    axi4_transaction trans;
    
    // Alignment calculator
    axi4_alignment_calculator align_calc;
    
    // Coverage groups
    covergroup alignment_basic_cg;
        option.per_instance = 1;
        
        // Alignment status
        aligned_cp: coverpoint align_calc.is_naturally_aligned(trans.addr, trans.size) {
            bins aligned = {1};
            bins unaligned = {0};
        }
        
        // Alignment offset
        offset_cp: coverpoint align_calc.get_alignment_offset(trans.addr, trans.size) {
            bins zero = {0};
            bins one = {1};
            bins small = {[2:3]};
            bins medium = {[4:7]};
            bins large = {[8:15]};
            bins xlarge = {[16:$]};
        }
        
        // Transfer size
        size_cp: coverpoint trans.size {
            bins byte_1 = {0};
            bins byte_2 = {1};
            bins byte_4 = {2};
            bins byte_8 = {3};
            bins byte_16 = {4};
            bins byte_32 = {5};
            bins byte_64 = {6};
            bins byte_128 = {7};
        }
        
        // Cross coverage
        alignment_size_cross: cross aligned_cp, size_cp;
        offset_size_cross: cross offset_cp, size_cp;
    endgroup
    
    covergroup boundary_crossing_cg;
        option.per_instance = 1;
        
        // 4KB boundary crossing
        cross_4kb_cp: coverpoint align_calc.crosses_4kb_boundary(trans.addr, trans.size, trans.len) {
            bins no_cross = {0};
            bins crosses = {1};
        }
        
        // Cache line crossing (64B)
        cross_cache_cp: coverpoint crosses_cache_line() {
            bins no_cross = {0};
            bins crosses = {1};
        }
        
        // Bus width crossing
        cross_bus_cp: coverpoint crosses_bus_width() {
            bins no_cross = {0};
            bins crosses = {1};
        }
        
        // Burst type with crossing
        burst_crossing: cross trans.burst, cross_4kb_cp;
    endgroup
    
    covergroup unaligned_burst_cg;
        option.per_instance = 1;
        
        // Burst type
        burst_cp: coverpoint trans.burst {
            bins fixed = {AXI4_FIXED};
            bins incr = {AXI4_INCR};
            bins wrap = {AXI4_WRAP};
        }
        
        // Burst length
        len_cp: coverpoint trans.len {
            bins single = {0};
            bins short = {[1:3]};
            bins medium = {[4:7]};
            bins long = {[8:15]};
            bins max = {[16:$]};
        }
        
        // Unaligned burst combinations
        unaligned_burst: cross burst_cp, align_calc.is_naturally_aligned(trans.addr, trans.size);
    endgroup
    
    covergroup address_patterns_cg;
        option.per_instance = 1;
        
        // Low address bits pattern
        addr_low_cp: coverpoint trans.addr[5:0] {
            bins aligned_patterns[] = {0, 2, 4, 8, 16, 32};
            bins odd_patterns[] = {1, 3, 5, 7, 9, 11, 13, 15};
            bins high_offset = {[48:63]};
        }
        
        // Address vs size alignment
        addr_size_match_cp: coverpoint check_addr_size_alignment() {
            bins perfect = {0};  // Aligned to size
            bins off_by_1 = {1};
            bins off_by_2_3 = {[2:3]};
            bins off_by_4_7 = {[4:7]};
            bins off_by_more = {[8:$]};
        }
    endgroup
    
    covergroup special_cases_cg;
        option.per_instance = 1;
        
        // WRAP alignment
        wrap_aligned_cp: coverpoint is_wrap_aligned() iff (trans.burst == AXI4_WRAP) {
            bins aligned = {1};
            bins unaligned = {0};
        }
        
        // Exclusive alignment
        exclusive_aligned_cp: coverpoint align_calc.is_naturally_aligned(trans.addr, trans.size) 
            iff (trans.lock == 1'b1) {
            bins aligned = {1};
            bins unaligned = {0};  // Should not happen
        }
        
        // Near boundary access
        near_4kb_cp: coverpoint is_near_4kb_boundary() {
            bins far = {0};
            bins near_start = {1};  // Within 16 bytes of start
            bins near_end = {2};    // Within 16 bytes of end
        }
    endgroup
    
    // Constructor
    function new(string name = "axi4_unaligned_coverage", uvm_component parent = null);
        super.new(name, parent);
        align_calc = axi4_alignment_calculator::type_id::create("align_calc");
        
        alignment_basic_cg = new();
        boundary_crossing_cg = new();
        unaligned_burst_cg = new();
        address_patterns_cg = new();
        special_cases_cg = new();
    endfunction
    
    // Write method
    function void write(axi4_transaction t);
        trans = t;
        
        // Sample all covergroups
        alignment_basic_cg.sample();
        boundary_crossing_cg.sample();
        unaligned_burst_cg.sample();
        address_patterns_cg.sample();
        special_cases_cg.sample();
    endfunction
    
    // Helper functions
    function bit crosses_cache_line();
        bit [63:0] start_addr = trans.addr;
        bit [63:0] end_addr = trans.addr + ((trans.len + 1) * (1 << trans.size)) - 1;
        return ((start_addr >> 6) != (end_addr >> 6));
    endfunction
    
    function bit crosses_bus_width();
        int bus_bytes = cfg.data_width / 8;
        bit [63:0] start_lane = trans.addr & (bus_bytes - 1);
        bit [63:0] end_lane = start_lane + ((trans.len + 1) * (1 << trans.size)) - 1;
        return (end_lane >= bus_bytes);
    endfunction
    
    function int check_addr_size_alignment();
        int offset = trans.addr & ((1 << trans.size) - 1);
        return offset;
    endfunction
    
    function bit is_wrap_aligned();
        if (trans.burst != AXI4_WRAP) return 1;
        int total_bytes = (trans.len + 1) * (1 << trans.size);
        return ((trans.addr & (total_bytes - 1)) == 0);
    endfunction
    
    function int is_near_4kb_boundary();
        bit [11:0] offset = trans.addr[11:0];
        if (offset < 16) return 1;        // Near start
        if (offset > 12'hFF0) return 2;   // Near end
        return 0;                          // Not near
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Unaligned Address Coverage Report ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Alignment basic coverage: %.1f%%", alignment_basic_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Boundary crossing coverage: %.1f%%", boundary_crossing_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Unaligned burst coverage: %.1f%%", unaligned_burst_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Address pattern coverage: %.1f%%", address_patterns_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Special cases coverage: %.1f%%", special_cases_cg.get_coverage()), UVM_LOW)
        
        real total_coverage = (alignment_basic_cg.get_coverage() + 
                              boundary_crossing_cg.get_coverage() + 
                              unaligned_burst_cg.get_coverage() + 
                              address_patterns_cg.get_coverage() + 
                              special_cases_cg.get_coverage()) / 5.0;
                              
        `uvm_info(get_name(), $sformatf("Total unaligned coverage: %.1f%%", total_coverage), UVM_LOW)
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_unaligned_coverage.sv")
        with open(filepath, 'w') as f:
            f.write(content)

def example_unaligned_address_generation():
    """Example of generating unaligned address tests"""
    
    config = {
        'num_masters': 4,
        'num_slaves': 4,
        'data_width': 128,
        'addr_width': 64,
        'id_width': 8
    }
    
    generator = VIPUnalignedAddressTestGenerator(config)
    output_dir = "vip_output/unaligned_tests"
    os.makedirs(output_dir, exist_ok=True)
    
    print("Generating unaligned address test components...")
    generator.generate_unaligned_address_tests(output_dir)
    print("Unaligned address test generation complete!")

if __name__ == "__main__":
    example_unaligned_address_generation()