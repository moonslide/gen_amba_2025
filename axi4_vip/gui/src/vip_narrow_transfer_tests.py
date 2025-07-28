#!/usr/bin/env python3
"""
VIP Narrow Transfer Test Generator
Implements comprehensive narrow transfer test scenarios
Based on tim_axi4_vip narrow transfer and strobe handling
"""

import os
from datetime import datetime
from typing import Dict, List, Optional, Tuple

class VIPNarrowTransferTestGenerator:
    """Generate narrow transfer test sequences"""
    
    def __init__(self, config):
        self.config = config
        self.timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        # Narrow transfer scenarios based on data width
        self.narrow_scenarios = {
            32: {  # 32-bit bus
                "transfers": [
                    {"name": "8b_on_32b", "size": 0, "bus_bytes": 4},
                    {"name": "16b_on_32b", "size": 1, "bus_bytes": 4}
                ]
            },
            64: {  # 64-bit bus
                "transfers": [
                    {"name": "8b_on_64b", "size": 0, "bus_bytes": 8},
                    {"name": "16b_on_64b", "size": 1, "bus_bytes": 8},
                    {"name": "32b_on_64b", "size": 2, "bus_bytes": 8}
                ]
            },
            128: {  # 128-bit bus
                "transfers": [
                    {"name": "8b_on_128b", "size": 0, "bus_bytes": 16},
                    {"name": "16b_on_128b", "size": 1, "bus_bytes": 16},
                    {"name": "32b_on_128b", "size": 2, "bus_bytes": 16},
                    {"name": "64b_on_128b", "size": 3, "bus_bytes": 16}
                ]
            }
        }
        
        # Strobe patterns for testing
        self.strobe_patterns = {
            "single_byte": "0x01",
            "alternating": "0xAA",
            "sparse": "0x11",
            "dense": "0xFF",
            "random": "random",
            "sequential": "sequential"
        }
        
    def generate_narrow_transfer_tests(self, output_dir: str):
        """Generate all narrow transfer test components"""
        
        # Create directory structure
        narrow_dir = os.path.join(output_dir, "narrow_transfers")
        os.makedirs(narrow_dir, exist_ok=True)
        
        # Generate components
        self._generate_strobe_calculator(narrow_dir)
        self._generate_narrow_transfer_checker(narrow_dir)
        self._generate_narrow_test_sequences(narrow_dir)
        self._generate_strobe_coverage(narrow_dir)
        self._generate_narrow_transfer_monitor(narrow_dir)
        
        return True
        
    def _generate_strobe_calculator(self, output_dir: str):
        """Generate strobe calculation utilities"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Strobe Calculator
// Generated: {self.timestamp}
// Description: Calculates write strobes for narrow transfers
//------------------------------------------------------------------------------

class axi4_strobe_calculator extends uvm_object;
    
    `uvm_object_utils(axi4_strobe_calculator)
    
    // Configuration
    int unsigned data_bus_bytes;
    
    // Constructor
    function new(string name = "axi4_strobe_calculator");
        super.new(name);
    endfunction
    
    // Calculate write strobe for narrow transfer
    function bit [127:0] calculate_wstrb(
        bit [63:0] address,
        int unsigned transfer_size,
        int unsigned data_bus_bytes,
        int unsigned beat_number = 0,
        axi4_burst_e burst_type = AXI4_INCR
    );
        bit [127:0] wstrb = 0;
        int unsigned transfer_bytes = 1 << transfer_size;
        int unsigned start_byte;
        bit [63:0] beat_address;
        
        // Calculate address for this beat
        case (burst_type)
            AXI4_FIXED: begin
                beat_address = address;
            end
            
            AXI4_INCR: begin
                beat_address = address + (beat_number * transfer_bytes);
            end
            
            AXI4_WRAP: begin
                int unsigned total_bytes = transfer_bytes * (beat_number + 1);
                int unsigned wrap_boundary = (address / total_bytes) * total_bytes;
                beat_address = wrap_boundary + ((address + beat_number * transfer_bytes) % total_bytes);
            end
        endcase
        
        // Calculate starting byte lane
        start_byte = beat_address & (data_bus_bytes - 1);
        
        // Set strobe bits
        for (int i = 0; i < transfer_bytes; i++) begin
            if ((start_byte + i) < data_bus_bytes) begin
                wstrb[(start_byte + i)] = 1'b1;
            end
        end
        
        return wstrb;
    endfunction
    
    // Calculate strobe for unaligned transfer
    function bit [127:0] calculate_unaligned_wstrb(
        bit [63:0] address,
        int unsigned length,
        int unsigned data_bus_bytes
    );
        bit [127:0] wstrb = 0;
        int unsigned start_byte = address & (data_bus_bytes - 1);
        int unsigned end_byte = start_byte + length - 1;
        
        // Handle wrap-around
        if (end_byte >= data_bus_bytes) begin
            // Split transfer
            for (int i = start_byte; i < data_bus_bytes; i++) begin
                wstrb[i] = 1'b1;
            end
        end else begin
            // Single lane transfer
            for (int i = start_byte; i <= end_byte; i++) begin
                wstrb[i] = 1'b1;
            end
        end
        
        return wstrb;
    endfunction
    
    // Generate sparse strobe pattern
    function bit [127:0] generate_sparse_wstrb(
        bit [127:0] base_strb,
        int unsigned sparsity_level
    );
        bit [127:0] sparse_strb = 0;
        int active_count = 0;
        
        // Count active strobes
        for (int i = 0; i < 128; i++) begin
            if (base_strb[i]) active_count++;
        end
        
        // Apply sparsity
        case (sparsity_level)
            1: begin // 50% sparse
                for (int i = 0; i < 128; i += 2) begin
                    if (base_strb[i]) sparse_strb[i] = 1'b1;
                end
            end
            
            2: begin // 75% sparse
                for (int i = 0; i < 128; i += 4) begin
                    if (base_strb[i]) sparse_strb[i] = 1'b1;
                end
            end
            
            3: begin // Random sparse
                for (int i = 0; i < 128; i++) begin
                    if (base_strb[i] && ($urandom_range(0, 3) == 0)) begin
                        sparse_strb[i] = 1'b1;
                    end
                end
            end
            
            default: sparse_strb = base_strb;
        endcase
        
        return sparse_strb;
    endfunction
    
    // Verify strobe validity
    function bit verify_wstrb_validity(
        bit [127:0] wstrb,
        bit [63:0] address,
        int unsigned transfer_size,
        int unsigned data_bus_bytes,
        axi4_burst_e burst_type
    );
        int unsigned transfer_bytes = 1 << transfer_size;
        int unsigned expected_ones = 0;
        int unsigned actual_ones = 0;
        
        // Count expected strobe bits
        if (burst_type == AXI4_FIXED) begin
            expected_ones = transfer_bytes;
        end else begin
            int unsigned start_byte = address & (data_bus_bytes - 1);
            expected_ones = (start_byte + transfer_bytes <= data_bus_bytes) ? 
                           transfer_bytes : (data_bus_bytes - start_byte);
        end
        
        // Count actual strobe bits
        for (int i = 0; i < data_bus_bytes; i++) begin
            if (wstrb[i]) actual_ones++;
        end
        
        // Check contiguous for non-sparse
        if (actual_ones == expected_ones) begin
            int first_one = -1;
            int last_one = -1;
            
            for (int i = 0; i < data_bus_bytes; i++) begin
                if (wstrb[i]) begin
                    if (first_one == -1) first_one = i;
                    last_one = i;
                end
            end
            
            // Check contiguous
            for (int i = first_one; i <= last_one; i++) begin
                if (!wstrb[i]) return 0; // Gap found
            end
            
            return 1;
        end
        
        return (actual_ones <= expected_ones); // Allow sparse
    endfunction
    
    // Convert strobe to byte enables
    function void strobe_to_byte_enables(
        bit [127:0] wstrb,
        int unsigned data_bus_bytes,
        output bit byte_enable[]
    );
        byte_enable = new[data_bus_bytes];
        
        for (int i = 0; i < data_bus_bytes; i++) begin
            byte_enable[i] = wstrb[i];
        end
    endfunction
    
    // Calculate data alignment
    function bit [1023:0] align_write_data(
        bit [1023:0] original_data,
        bit [63:0] address,
        int unsigned transfer_size,
        int unsigned data_bus_bytes
    );
        bit [1023:0] aligned_data = 0;
        int unsigned transfer_bytes = 1 << transfer_size;
        int unsigned start_byte = address & (data_bus_bytes - 1);
        
        // Shift data to correct byte lanes
        for (int i = 0; i < transfer_bytes; i++) begin
            if ((start_byte + i) < data_bus_bytes) begin
                aligned_data[(start_byte + i) * 8 +: 8] = original_data[i * 8 +: 8];
            end
        end
        
        return aligned_data;
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_strobe_calculator.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_narrow_transfer_checker(self, output_dir: str):
        """Generate narrow transfer checker"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Narrow Transfer Checker
// Generated: {self.timestamp}
// Description: Validates narrow transfer behavior and data integrity
//------------------------------------------------------------------------------

class axi4_narrow_transfer_checker extends uvm_component;
    
    `uvm_component_utils(axi4_narrow_transfer_checker)
    
    // Analysis port
    uvm_analysis_imp #(axi4_transaction, axi4_narrow_transfer_checker) analysis_export;
    
    // Configuration
    axi4_config cfg;
    axi4_strobe_calculator strobe_calc;
    
    // Memory model for checking
    bit [7:0] reference_memory[bit[63:0]];
    
    // Statistics
    int unsigned narrow_write_count;
    int unsigned narrow_read_count;
    int unsigned strobe_errors;
    int unsigned data_integrity_errors;
    int unsigned alignment_errors;
    
    // Transfer tracking
    typedef struct {
        bit [63:0] start_addr;
        bit [63:0] end_addr;
        int transfer_size;
        int burst_len;
        bit [127:0] wstrb_pattern[];
        bit [1023:0] write_data[];
        time timestamp;
    } narrow_transfer_t;
    
    narrow_transfer_t active_transfers[bit[7:0]];
    
    // Constructor
    function new(string name = "axi4_narrow_transfer_checker", uvm_component parent = null);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(axi4_config)::get(this, "", "axi4_config", cfg)) begin
            `uvm_fatal("CONFIG", "Failed to get axi4_config")
        end
        
        strobe_calc = axi4_strobe_calculator::type_id::create("strobe_calc");
        strobe_calc.data_bus_bytes = cfg.data_width / 8;
    endfunction
    
    // Write method
    function void write(axi4_transaction trans);
        if (is_narrow_transfer(trans)) begin
            check_narrow_transfer(trans);
        end
    endfunction
    
    // Check if transfer is narrow
    function bit is_narrow_transfer(axi4_transaction trans);
        int transfer_bytes = 1 << trans.size;
        int bus_bytes = cfg.data_width / 8;
        return (transfer_bytes < bus_bytes);
    endfunction
    
    // Check narrow transfer
    function void check_narrow_transfer(axi4_transaction trans);
        if (trans.trans_type == AXI4_WRITE) begin
            check_narrow_write(trans);
            narrow_write_count++;
        end else begin
            check_narrow_read(trans);
            narrow_read_count++;
        end
    endfunction
    
    // Check narrow write
    function void check_narrow_write(axi4_transaction trans);
        narrow_transfer_t transfer;
        bit [127:0] expected_strb;
        int bus_bytes = cfg.data_width / 8;
        
        // Store transfer info
        transfer.start_addr = trans.addr;
        transfer.transfer_size = trans.size;
        transfer.burst_len = trans.len;
        transfer.timestamp = $time;
        transfer.wstrb_pattern = new[trans.len + 1];
        transfer.write_data = new[trans.len + 1];
        
        // Check each beat
        for (int beat = 0; beat <= trans.len; beat++) begin
            bit [63:0] beat_addr;
            
            // Calculate beat address
            case (trans.burst)
                AXI4_FIXED: beat_addr = trans.addr;
                AXI4_INCR: beat_addr = trans.addr + beat * (1 << trans.size);
                AXI4_WRAP: begin
                    int wrap_size = (trans.len + 1) * (1 << trans.size);
                    int wrap_boundary = (trans.addr / wrap_size) * wrap_size;
                    beat_addr = wrap_boundary + ((trans.addr + beat * (1 << trans.size)) % wrap_size);
                end
            endcase
            
            // Calculate expected strobe
            expected_strb = strobe_calc.calculate_wstrb(
                beat_addr,
                trans.size,
                bus_bytes,
                beat,
                trans.burst
            );
            
            // Verify strobe
            if (trans.strb[beat] != expected_strb[bus_bytes-1:0]) begin
                // Check if sparse strobe (subset of expected)
                bit is_sparse = 1;
                for (int i = 0; i < bus_bytes; i++) begin
                    if (trans.strb[beat][i] && !expected_strb[i]) begin
                        is_sparse = 0;
                        break;
                    end
                end
                
                if (!is_sparse) begin
                    `uvm_error(get_name(), $sformatf("Strobe mismatch at beat %0d: Expected=%0h, Got=%0h",
                                                    beat, expected_strb[bus_bytes-1:0], trans.strb[beat]))
                    strobe_errors++;
                end
            end
            
            // Store data with strobe
            transfer.wstrb_pattern[beat] = trans.strb[beat];
            transfer.write_data[beat] = trans.data[beat];
            
            // Update reference memory
            update_memory_with_strobe(beat_addr, trans.data[beat], trans.strb[beat]);
        end
        
        // Calculate end address
        if (trans.burst == AXI4_INCR) begin
            transfer.end_addr = trans.addr + (trans.len + 1) * (1 << trans.size) - 1;
        end else begin
            transfer.end_addr = trans.addr + (1 << trans.size) - 1;
        end
        
        active_transfers[trans.id] = transfer;
        
        // Check data integrity
        check_write_data_integrity(trans);
    endfunction
    
    // Check narrow read
    function void check_narrow_read(axi4_transaction trans);
        bit [1023:0] expected_data;
        int bus_bytes = cfg.data_width / 8;
        int transfer_bytes = 1 << trans.size;
        
        // Check each beat
        for (int beat = 0; beat <= trans.len; beat++) begin
            bit [63:0] beat_addr;
            
            // Calculate beat address
            case (trans.burst)
                AXI4_FIXED: beat_addr = trans.addr;
                AXI4_INCR: beat_addr = trans.addr + beat * (1 << trans.size);
                AXI4_WRAP: begin
                    int wrap_size = (trans.len + 1) * (1 << trans.size);
                    int wrap_boundary = (trans.addr / wrap_size) * wrap_size;
                    beat_addr = wrap_boundary + ((trans.addr + beat * (1 << trans.size)) % wrap_size);
                end
            endcase
            
            // Get expected data from reference memory
            expected_data = 0;
            for (int i = 0; i < transfer_bytes; i++) begin
                bit [63:0] byte_addr = beat_addr + i;
                if (reference_memory.exists(byte_addr)) begin
                    expected_data[i*8 +: 8] = reference_memory[byte_addr];
                end
            end
            
            // Align expected data to bus
            int start_byte = beat_addr & (bus_bytes - 1);
            bit [1023:0] aligned_expected = 0;
            for (int i = 0; i < transfer_bytes; i++) begin
                aligned_expected[(start_byte + i) * 8 +: 8] = expected_data[i * 8 +: 8];
            end
            
            // Compare relevant bytes
            for (int i = 0; i < transfer_bytes; i++) begin
                int byte_lane = start_byte + i;
                if (byte_lane < bus_bytes) begin
                    bit [7:0] expected_byte = aligned_expected[byte_lane * 8 +: 8];
                    bit [7:0] actual_byte = trans.data[beat][byte_lane * 8 +: 8];
                    
                    if (expected_byte !== actual_byte) begin
                        `uvm_error(get_name(), $sformatf("Read data mismatch at addr %0h, byte %0d: Expected=%0h, Got=%0h",
                                                        beat_addr + i, i, expected_byte, actual_byte))
                        data_integrity_errors++;
                    end
                end
            end
        end
    endfunction
    
    // Update memory with strobe
    function void update_memory_with_strobe(bit [63:0] addr, bit [1023:0] data, bit [127:0] strb);
        int bus_bytes = cfg.data_width / 8;
        
        for (int i = 0; i < bus_bytes; i++) begin
            if (strb[i]) begin
                reference_memory[addr + i] = data[i * 8 +: 8];
            end
        end
    endfunction
    
    // Check write data integrity
    function void check_write_data_integrity(axi4_transaction trans);
        int bus_bytes = cfg.data_width / 8;
        
        // Check non-strobed bytes are stable/zero
        foreach (trans.data[beat]) begin
            for (int byte_lane = 0; byte_lane < bus_bytes; byte_lane++) begin
                if (!trans.strb[beat][byte_lane]) begin
                    // Non-strobed byte should be stable or zero
                    bit [7:0] byte_val = trans.data[beat][byte_lane * 8 +: 8];
                    if (byte_val !== 8'h00 && byte_val !== 8'hXX) begin
                        `uvm_warning(get_name(), $sformatf("Non-strobed byte lane %0d has value %0h (beat %0d)",
                                                          byte_lane, byte_val, beat))
                    end
                end
            end
        end
    endfunction
    
    // Check alignment rules
    function void check_narrow_alignment(axi4_transaction trans);
        bit [63:0] addr = trans.addr;
        int size = trans.size;
        int transfer_bytes = 1 << size;
        
        // Check natural alignment for burst
        if (trans.burst == AXI4_WRAP) begin
            int total_bytes = (trans.len + 1) * transfer_bytes;
            if (addr & (total_bytes - 1)) begin
                `uvm_error(get_name(), $sformatf("WRAP burst not aligned: addr=%0h, total_bytes=%0d",
                                                addr, total_bytes))
                alignment_errors++;
            end
        end
        
        // For narrow transfers, start address determines byte lanes
        int start_lane = addr & ((cfg.data_width / 8) - 1);
        int end_lane = start_lane + transfer_bytes - 1;
        
        if (end_lane >= (cfg.data_width / 8)) begin
            `uvm_info(get_name(), $sformatf("Narrow transfer crosses data width boundary: start=%0d, end=%0d",
                                           start_lane, end_lane), UVM_MEDIUM)
        end
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Narrow Transfer Checker Report ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Narrow writes: %0d", narrow_write_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Narrow reads: %0d", narrow_read_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Strobe errors: %0d", strobe_errors), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Data integrity errors: %0d", data_integrity_errors), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Alignment errors: %0d", alignment_errors), UVM_LOW)
        
        if (strobe_errors > 0 || data_integrity_errors > 0) begin
            `uvm_error(get_name(), "Narrow transfer errors detected!")
        end
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_narrow_transfer_checker.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_narrow_test_sequences(self, output_dir: str):
        """Generate narrow transfer test sequences"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Narrow Transfer Test Sequences
// Generated: {self.timestamp}
// Description: Comprehensive narrow transfer test scenarios
//------------------------------------------------------------------------------

// Base narrow transfer sequence
class narrow_transfer_base_sequence extends axi4_base_test_sequence;
    
    `uvm_object_utils(narrow_transfer_base_sequence)
    
    // Configuration
    rand int unsigned narrow_size;
    rand bit use_sparse_strobe;
    rand int unsigned sparse_level;
    
    axi4_strobe_calculator strobe_calc;
    
    constraint narrow_c {
        narrow_size < $clog2(cfg.data_width / 8);
        sparse_level inside {[0:3]};
    }
    
    // Constructor
    function new(string name = "narrow_transfer_base_sequence");
        super.new(name);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        strobe_calc = axi4_strobe_calculator::type_id::create("strobe_calc");
        strobe_calc.data_bus_bytes = cfg.data_width / 8;
    endfunction
    
endclass

// Simple narrow write test
class narrow_write_sequence extends narrow_transfer_base_sequence;
    
    `uvm_object_utils(narrow_write_sequence)
    
    function new(string name = "narrow_write_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        `uvm_info(get_type_name(), "Starting narrow write sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            trans = axi4_transaction::type_id::create("trans");
            
            assert(trans.randomize() with {
                trans_type == AXI4_WRITE;
                size < $clog2(cfg.data_width / 8); // Narrow
                burst_type inside {AXI4_FIXED, AXI4_INCR};
                burst_len inside {[0:15]};
            });
            
            // Calculate strobes
            trans.strb = new[trans.len + 1];
            for (int beat = 0; beat <= trans.len; beat++) begin
                trans.strb[beat] = strobe_calc.calculate_wstrb(
                    trans.addr + (beat * (1 << trans.size)),
                    trans.size,
                    cfg.data_width / 8,
                    beat,
                    trans.burst
                );
            end
            
            start_item(trans);
            finish_item(trans);
            
            wait_random_delay();
        end
    endtask
    
endclass

// Narrow read sequence
class narrow_read_sequence extends narrow_transfer_base_sequence;
    
    `uvm_object_utils(narrow_read_sequence)
    
    function new(string name = "narrow_read_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        `uvm_info(get_type_name(), "Starting narrow read sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            trans = axi4_transaction::type_id::create("trans");
            
            assert(trans.randomize() with {
                trans_type == AXI4_READ;
                size < $clog2(cfg.data_width / 8); // Narrow
                burst_type inside {AXI4_FIXED, AXI4_INCR};
                burst_len inside {[0:15]};
            });
            
            start_item(trans);
            finish_item(trans);
            
            wait_random_delay();
        end
    endtask
    
endclass

// Sparse strobe pattern test
class sparse_strobe_sequence extends narrow_transfer_base_sequence;
    
    `uvm_object_utils(sparse_strobe_sequence)
    
    function new(string name = "sparse_strobe_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        `uvm_info(get_type_name(), "Starting sparse strobe sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            trans = axi4_transaction::type_id::create("trans");
            
            assert(trans.randomize() with {
                trans_type == AXI4_WRITE;
                size inside {[0:2]}; // Up to 4 bytes
                burst_type == AXI4_INCR;
                burst_len inside {[3:15]};
            });
            
            // Generate sparse strobes
            trans.strb = new[trans.len + 1];
            for (int beat = 0; beat <= trans.len; beat++) begin
                bit [127:0] base_strb = strobe_calc.calculate_wstrb(
                    trans.addr + (beat * (1 << trans.size)),
                    trans.size,
                    cfg.data_width / 8,
                    beat,
                    trans.burst
                );
                
                // Apply sparsity
                if (beat % 2 == 0) begin
                    trans.strb[beat] = base_strb[cfg.data_width/8-1:0];
                end else begin
                    // Sparse pattern
                    trans.strb[beat] = 0;
                    for (int i = 0; i < cfg.data_width/8; i += 2) begin
                        if (base_strb[i]) trans.strb[beat][i] = 1'b1;
                    end
                end
            end
            
            start_item(trans);
            finish_item(trans);
            
            wait_random_delay();
        end
    endtask
    
endclass

// Narrow wrap burst test
class narrow_wrap_sequence extends narrow_transfer_base_sequence;
    
    `uvm_object_utils(narrow_wrap_sequence)
    
    function new(string name = "narrow_wrap_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        `uvm_info(get_type_name(), "Starting narrow wrap sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            trans = axi4_transaction::type_id::create("trans");
            
            // First randomize basic fields
            assert(trans.randomize() with {
                trans_type inside {AXI4_WRITE, AXI4_READ};
                size < $clog2(cfg.data_width / 8); // Narrow
                burst_type == AXI4_WRAP;
                burst_len inside {1, 3, 7, 15}; // Valid wrap lengths
            });
            
            // Align address for wrap
            int wrap_bytes = (trans.len + 1) * (1 << trans.size);
            trans.addr = trans.addr & ~(wrap_bytes - 1);
            
            // Calculate strobes for write
            if (trans.trans_type == AXI4_WRITE) begin
                trans.strb = new[trans.len + 1];
                for (int beat = 0; beat <= trans.len; beat++) begin
                    trans.strb[beat] = strobe_calc.calculate_wstrb(
                        trans.addr,
                        trans.size,
                        cfg.data_width / 8,
                        beat,
                        AXI4_WRAP
                    );
                end
            end
            
            start_item(trans);
            finish_item(trans);
            
            wait_random_delay();
        end
    endtask
    
endclass

// Mixed size narrow transfers
class mixed_narrow_sequence extends narrow_transfer_base_sequence;
    
    `uvm_object_utils(mixed_narrow_sequence)
    
    function new(string name = "mixed_narrow_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        int size_sequence[] = '{0, 1, 2, 1, 0, 2, 0}; // Pattern of sizes
        
        `uvm_info(get_type_name(), "Starting mixed narrow sequence", UVM_LOW)
        
        foreach (size_sequence[i]) begin
            trans = axi4_transaction::type_id::create("trans");
            
            assert(trans.randomize() with {
                trans_type inside {AXI4_WRITE, AXI4_READ};
                size == size_sequence[i];
                burst_type == AXI4_INCR;
                burst_len inside {[0:7]};
            });
            
            // Calculate strobes for write
            if (trans.trans_type == AXI4_WRITE) begin
                trans.strb = new[trans.len + 1];
                for (int beat = 0; beat <= trans.len; beat++) begin
                    trans.strb[beat] = strobe_calc.calculate_wstrb(
                        trans.addr + (beat * (1 << trans.size)),
                        trans.size,
                        cfg.data_width / 8,
                        beat,
                        trans.burst
                    );
                end
            end
            
            start_item(trans);
            finish_item(trans);
            
            #10ns; // Small delay between different sizes
        end
    endtask
    
endclass

// Boundary crossing narrow transfers
class narrow_boundary_sequence extends narrow_transfer_base_sequence;
    
    `uvm_object_utils(narrow_boundary_sequence)
    
    function new(string name = "narrow_boundary_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        int bus_bytes = cfg.data_width / 8;
        
        `uvm_info(get_type_name(), "Starting narrow boundary sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            trans = axi4_transaction::type_id::create("trans");
            
            // Start near bus width boundary
            int start_offset = bus_bytes - 2;
            
            assert(trans.randomize() with {
                trans_type inside {AXI4_WRITE, AXI4_READ};
                size inside {0, 1}; // 1 or 2 byte transfers
                burst_type == AXI4_INCR;
                burst_len inside {[2:7]};
                addr[5:0] == start_offset;
            });
            
            // This will cross bus width boundary
            `uvm_info(get_type_name(), $sformatf("Narrow transfer crossing boundary at addr %0h", trans.addr), UVM_MEDIUM)
            
            // Calculate strobes
            if (trans.trans_type == AXI4_WRITE) begin
                trans.strb = new[trans.len + 1];
                for (int beat = 0; beat <= trans.len; beat++) begin
                    trans.strb[beat] = strobe_calc.calculate_wstrb(
                        trans.addr + (beat * (1 << trans.size)),
                        trans.size,
                        cfg.data_width / 8,
                        beat,
                        trans.burst
                    );
                end
            end
            
            start_item(trans);
            finish_item(trans);
            
            wait_random_delay();
        end
    endtask
    
endclass

// All byte lanes narrow test
class all_lanes_narrow_sequence extends narrow_transfer_base_sequence;
    
    `uvm_object_utils(all_lanes_narrow_sequence)
    
    function new(string name = "all_lanes_narrow_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        int bus_bytes = cfg.data_width / 8;
        
        `uvm_info(get_type_name(), "Starting all lanes narrow sequence", UVM_LOW)
        
        // Test each byte lane
        for (int lane = 0; lane < bus_bytes; lane++) begin
            trans = axi4_transaction::type_id::create("trans");
            
            assert(trans.randomize() with {
                trans_type == AXI4_WRITE;
                size == 0; // Single byte
                burst_type == AXI4_FIXED;
                burst_len == 0;
                addr[5:0] == lane;
            });
            
            // Single byte strobe
            trans.strb = new[1];
            trans.strb[0] = 1 << lane;
            
            `uvm_info(get_type_name(), $sformatf("Writing to byte lane %0d", lane), UVM_HIGH)
            
            start_item(trans);
            finish_item(trans);
            
            #1ns;
        end
        
        // Read back all lanes
        for (int lane = 0; lane < bus_bytes; lane++) begin
            trans = axi4_transaction::type_id::create("trans");
            
            assert(trans.randomize() with {
                trans_type == AXI4_READ;
                size == 0; // Single byte
                burst_type == AXI4_FIXED;
                burst_len == 0;
                addr[5:0] == lane;
            });
            
            `uvm_info(get_type_name(), $sformatf("Reading from byte lane %0d", lane), UVM_HIGH)
            
            start_item(trans);
            finish_item(trans);
            
            #1ns;
        end
    endtask
    
endclass

// Narrow exclusive access test
class narrow_exclusive_sequence extends narrow_transfer_base_sequence;
    
    `uvm_object_utils(narrow_exclusive_sequence)
    
    function new(string name = "narrow_exclusive_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction ex_read, ex_write;
        
        `uvm_info(get_type_name(), "Starting narrow exclusive sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            bit [63:0] ex_addr;
            int ex_size;
            
            // Exclusive read
            ex_read = axi4_transaction::type_id::create("ex_read");
            
            assert(ex_read.randomize() with {
                trans_type == AXI4_READ;
                size inside {[0:2]}; // 1, 2, or 4 bytes
                burst_type == AXI4_INCR;
                burst_len == 0; // Single transfer for exclusive
                lock == 1'b1; // Exclusive
            });
            
            // Align for exclusive
            ex_read.addr = ex_read.addr & ~((1 << ex_read.size) - 1);
            ex_addr = ex_read.addr;
            ex_size = ex_read.size;
            
            start_item(ex_read);
            finish_item(ex_read);
            
            // Exclusive write
            ex_write = axi4_transaction::type_id::create("ex_write");
            
            assert(ex_write.randomize() with {
                trans_type == AXI4_WRITE;
                addr == ex_addr;
                size == ex_size;
                burst_type == AXI4_INCR;
                burst_len == 0;
                lock == 1'b1; // Exclusive
                id == ex_read.id; // Same ID
            });
            
            // Calculate strobe
            ex_write.strb = new[1];
            ex_write.strb[0] = strobe_calc.calculate_wstrb(
                ex_write.addr,
                ex_write.size,
                cfg.data_width / 8,
                0,
                ex_write.burst
            );
            
            start_item(ex_write);
            finish_item(ex_write);
            
            // Check response
            if (ex_write.resp == AXI4_EXOKAY) begin
                `uvm_info(get_type_name(), $sformatf("Narrow exclusive success at addr %0h, size %0d bytes", 
                                                    ex_addr, 1 << ex_size), UVM_MEDIUM)
            end
            
            wait_random_delay();
        end
    endtask
    
endclass

// Maximum narrow transfer stress test
class narrow_stress_sequence extends narrow_transfer_base_sequence;
    
    `uvm_object_utils(narrow_stress_sequence)
    
    function new(string name = "narrow_stress_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans_q[$];
        
        `uvm_info(get_type_name(), "Starting narrow transfer stress test", UVM_LOW)
        
        // Generate many narrow transfers
        repeat (100) begin
            axi4_transaction trans = axi4_transaction::type_id::create("trans");
            
            assert(trans.randomize() with {
                trans_type inside {AXI4_WRITE, AXI4_READ};
                size < $clog2(cfg.data_width / 8); // Narrow
                burst_type inside {AXI4_FIXED, AXI4_INCR, AXI4_WRAP};
                burst_len inside {[0:15]};
            });
            
            // Fix wrap alignment
            if (trans.burst == AXI4_WRAP) begin
                int wrap_bytes = (trans.len + 1) * (1 << trans.size);
                trans.addr = trans.addr & ~(wrap_bytes - 1);
            end
            
            // Calculate strobes for writes
            if (trans.trans_type == AXI4_WRITE) begin
                trans.strb = new[trans.len + 1];
                for (int beat = 0; beat <= trans.len; beat++) begin
                    trans.strb[beat] = strobe_calc.calculate_wstrb(
                        trans.addr,
                        trans.size,
                        cfg.data_width / 8,
                        beat,
                        trans.burst
                    );
                    
                    // Randomly make some sparse
                    if ($urandom_range(0, 9) < 3) begin
                        trans.strb[beat] = strobe_calc.generate_sparse_wstrb(trans.strb[beat], 1);
                    end
                end
            end
            
            trans_q.push_back(trans);
        end
        
        // Send all transactions rapidly
        foreach (trans_q[i]) begin
            fork
                automatic int idx = i;
                begin
                    #(idx * 0.1ns); // Slight offset
                    start_item(trans_q[idx]);
                    finish_item(trans_q[idx]);
                end
            join_none
        end
        
        wait fork;
        
        `uvm_info(get_type_name(), "Narrow stress test complete", UVM_LOW)
    endtask
    
endclass
'''
        
        filepath = os.path.join(output_dir, "narrow_transfer_test_sequences.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_strobe_coverage(self, output_dir: str):
        """Generate strobe pattern coverage"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Strobe Pattern Coverage
// Generated: {self.timestamp}
// Description: Functional coverage for write strobe patterns
//------------------------------------------------------------------------------

class axi4_strobe_coverage extends uvm_subscriber #(axi4_transaction);
    
    `uvm_component_utils(axi4_strobe_coverage)
    
    // Transaction handle
    axi4_transaction trans;
    
    // Configuration
    int unsigned data_bus_bytes;
    
    // Coverage groups
    covergroup strobe_pattern_cg;
        option.per_instance = 1;
        
        // Basic strobe patterns
        strobe_pattern_cp: coverpoint get_strobe_pattern(trans.strb[0]) {
            bins all_zeros = {STRB_ALL_ZEROS};
            bins all_ones = {STRB_ALL_ONES};
            bins single_byte = {STRB_SINGLE_BYTE};
            bins contiguous = {STRB_CONTIGUOUS};
            bins sparse = {STRB_SPARSE};
            bins alternating = {STRB_ALTERNATING};
            bins custom = {STRB_CUSTOM};
        }
        
        // Strobe count (number of active bytes)
        strobe_count_cp: coverpoint count_strobe_bits(trans.strb[0]) {
            bins zero = {0};
            bins one = {1};
            bins few = {[2:4]};
            bins half = {[data_bus_bytes/2-1:data_bus_bytes/2+1]};
            bins most = {[data_bus_bytes-2:data_bus_bytes-1]};
            bins all = {data_bus_bytes};
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
        strobe_size_cross: cross strobe_pattern_cp, size_cp;
    endgroup
    
    covergroup strobe_position_cg;
        option.per_instance = 1;
        
        // First active byte position
        first_byte_cp: coverpoint get_first_strobe_position(trans.strb[0]) {
            bins low = {[0:data_bus_bytes/4-1]};
            bins mid_low = {[data_bus_bytes/4:data_bus_bytes/2-1]};
            bins mid_high = {[data_bus_bytes/2:3*data_bus_bytes/4-1]};
            bins high = {[3*data_bus_bytes/4:data_bus_bytes-1]};
            bins none = {-1};
        }
        
        // Last active byte position
        last_byte_cp: coverpoint get_last_strobe_position(trans.strb[0]) {
            bins low = {[0:data_bus_bytes/4-1]};
            bins mid_low = {[data_bus_bytes/4:data_bus_bytes/2-1]};
            bins mid_high = {[data_bus_bytes/2:3*data_bus_bytes/4-1]};
            bins high = {[3*data_bus_bytes/4:data_bus_bytes-1]};
            bins none = {-1};
        }
        
        // Span (last - first)
        span_cp: coverpoint get_strobe_span(trans.strb[0]) {
            bins single = {0};
            bins narrow = {[1:3]};
            bins medium = {[4:7]};
            bins wide = {[8:15]};
            bins full = {[16:$]};
        }
    endgroup
    
    covergroup strobe_burst_cg;
        option.per_instance = 1;
        
        // Burst type with strobe
        burst_type_cp: coverpoint trans.burst {
            bins fixed = {AXI4_FIXED};
            bins incr = {AXI4_INCR};
            bins wrap = {AXI4_WRAP};
        }
        
        // Burst length
        burst_len_cp: coverpoint trans.len {
            bins single = {0};
            bins short = {[1:3]};
            bins medium = {[4:7]};
            bins long = {[8:15]};
            bins max = {[16:255]};
        }
        
        // Strobe consistency across burst
        strobe_consistency_cp: coverpoint check_strobe_consistency() {
            bins consistent = {1};
            bins varying = {0};
        }
        
        // Cross coverage
        burst_strobe_cross: cross burst_type_cp, strobe_consistency_cp;
    endgroup
    
    covergroup strobe_alignment_cg;
        option.per_instance = 1;
        
        // Address alignment vs strobe
        addr_alignment_cp: coverpoint trans.addr[5:0] {
            bins aligned_1 = {0};
            bins aligned_2 = {0, 2, 4, 6, 8, 10, 12, 14};
            bins aligned_4 = {0, 4, 8, 12};
            bins aligned_8 = {0, 8};
            bins aligned_16 = {0, 16, 32, 48};
            bins unaligned = default;
        }
        
        // Natural strobe alignment
        natural_alignment_cp: coverpoint check_natural_alignment() {
            bins aligned = {1};
            bins unaligned = {0};
        }
        
        // Cross coverage
        alignment_cross: cross addr_alignment_cp, natural_alignment_cp;
    endgroup
    
    // Strobe pattern enumeration
    typedef enum {
        STRB_ALL_ZEROS,
        STRB_ALL_ONES,
        STRB_SINGLE_BYTE,
        STRB_CONTIGUOUS,
        STRB_SPARSE,
        STRB_ALTERNATING,
        STRB_CUSTOM
    } strobe_pattern_e;
    
    // Constructor
    function new(string name = "axi4_strobe_coverage", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        axi4_config cfg;
        if (!uvm_config_db#(axi4_config)::get(this, "", "axi4_config", cfg)) begin
            `uvm_fatal("CONFIG", "Failed to get axi4_config")
        end
        
        data_bus_bytes = cfg.data_width / 8;
        
        // Create coverage groups
        strobe_pattern_cg = new();
        strobe_position_cg = new();
        strobe_burst_cg = new();
        strobe_alignment_cg = new();
    endfunction
    
    // Write method
    function void write(axi4_transaction t);
        trans = t;
        
        // Sample coverage for write transactions
        if (trans.trans_type == AXI4_WRITE) begin
            // Sample for each beat
            foreach (trans.strb[i]) begin
                strobe_pattern_cg.sample();
                strobe_position_cg.sample();
            end
            
            strobe_burst_cg.sample();
            strobe_alignment_cg.sample();
        end
    endfunction
    
    // Helper functions
    function strobe_pattern_e get_strobe_pattern(bit [127:0] strb);
        int ones = count_strobe_bits(strb);
        bit [127:0] mask = (1 << data_bus_bytes) - 1;
        strb = strb & mask;
        
        if (ones == 0) return STRB_ALL_ZEROS;
        if (ones == data_bus_bytes) return STRB_ALL_ONES;
        if (ones == 1) return STRB_SINGLE_BYTE;
        
        // Check contiguous
        int first = get_first_strobe_position(strb);
        int last = get_last_strobe_position(strb);
        bit is_contiguous = 1;
        
        for (int i = first; i <= last; i++) begin
            if (!strb[i]) is_contiguous = 0;
        end
        
        if (is_contiguous) return STRB_CONTIGUOUS;
        
        // Check alternating
        bit is_alternating = 1;
        for (int i = 0; i < data_bus_bytes-1; i++) begin
            if (strb[i] == strb[i+1]) is_alternating = 0;
        end
        
        if (is_alternating && ones > 1) return STRB_ALTERNATING;
        
        // Check sparse (less than half active)
        if (ones < data_bus_bytes/2) return STRB_SPARSE;
        
        return STRB_CUSTOM;
    endfunction
    
    function int count_strobe_bits(bit [127:0] strb);
        int count = 0;
        for (int i = 0; i < data_bus_bytes; i++) begin
            if (strb[i]) count++;
        end
        return count;
    endfunction
    
    function int get_first_strobe_position(bit [127:0] strb);
        for (int i = 0; i < data_bus_bytes; i++) begin
            if (strb[i]) return i;
        end
        return -1;
    endfunction
    
    function int get_last_strobe_position(bit [127:0] strb);
        for (int i = data_bus_bytes-1; i >= 0; i--) begin
            if (strb[i]) return i;
        end
        return -1;
    endfunction
    
    function int get_strobe_span(bit [127:0] strb);
        int first = get_first_strobe_position(strb);
        int last = get_last_strobe_position(strb);
        if (first == -1 || last == -1) return 0;
        return last - first;
    endfunction
    
    function bit check_strobe_consistency();
        if (trans.strb.size() <= 1) return 1;
        
        bit [127:0] first_strb = trans.strb[0];
        foreach (trans.strb[i]) begin
            if (trans.strb[i] != first_strb) return 0;
        end
        return 1;
    endfunction
    
    function bit check_natural_alignment();
        int transfer_size = 1 << trans.size;
        int addr_offset = trans.addr & (data_bus_bytes - 1);
        
        // Check if strobe matches expected position
        bit [127:0] expected_strb = 0;
        for (int i = 0; i < transfer_size; i++) begin
            if ((addr_offset + i) < data_bus_bytes) begin
                expected_strb[addr_offset + i] = 1;
            end
        end
        
        return (trans.strb[0] == expected_strb[data_bus_bytes-1:0]);
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Strobe Coverage Report ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Pattern coverage: %.1f%%", strobe_pattern_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Position coverage: %.1f%%", strobe_position_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Burst coverage: %.1f%%", strobe_burst_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Alignment coverage: %.1f%%", strobe_alignment_cg.get_coverage()), UVM_LOW)
        
        real total_coverage = (strobe_pattern_cg.get_coverage() + 
                              strobe_position_cg.get_coverage() + 
                              strobe_burst_cg.get_coverage() + 
                              strobe_alignment_cg.get_coverage()) / 4.0;
                              
        `uvm_info(get_name(), $sformatf("Total strobe coverage: %.1f%%", total_coverage), UVM_LOW)
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_strobe_coverage.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_narrow_transfer_monitor(self, output_dir: str):
        """Generate narrow transfer monitor"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Narrow Transfer Monitor
// Generated: {self.timestamp}
// Description: Monitors narrow transfers and extracts relevant data
//------------------------------------------------------------------------------

class axi4_narrow_transfer_monitor extends uvm_monitor;
    
    `uvm_component_utils(axi4_narrow_transfer_monitor)
    
    // Virtual interface
    virtual axi4_if vif;
    
    // Analysis ports
    uvm_analysis_port #(axi4_narrow_transaction) narrow_ap;
    uvm_analysis_port #(axi4_transaction) normal_ap;
    
    // Configuration
    axi4_config cfg;
    
    // Statistics
    int unsigned narrow_write_count;
    int unsigned narrow_read_count;
    int unsigned sparse_strobe_count;
    int unsigned unaligned_narrow_count;
    
    // Constructor
    function new(string name = "axi4_narrow_transfer_monitor", uvm_component parent = null);
        super.new(name, parent);
        narrow_ap = new("narrow_ap", this);
        normal_ap = new("normal_ap", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("NOVIF", "Virtual interface not found")
        end
        
        if (!uvm_config_db#(axi4_config)::get(this, "", "axi4_config", cfg)) begin
            `uvm_fatal("CONFIG", "Failed to get axi4_config")
        end
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        fork
            monitor_write_channel();
            monitor_read_channel();
        join
    endtask
    
    // Monitor write channel
    task monitor_write_channel();
        forever begin
            axi4_transaction trans;
            axi4_narrow_transaction narrow_trans;
            
            @(posedge vif.aclk);
            
            if (vif.awvalid && vif.awready) begin
                trans = capture_write_transaction();
                
                if (is_narrow_transfer(trans)) begin
                    narrow_trans = convert_to_narrow(trans);
                    analyze_narrow_write(narrow_trans);
                    narrow_ap.write(narrow_trans);
                    narrow_write_count++;
                end else begin
                    normal_ap.write(trans);
                end
            end
        end
    endtask
    
    // Monitor read channel
    task monitor_read_channel();
        forever begin
            axi4_transaction trans;
            axi4_narrow_transaction narrow_trans;
            
            @(posedge vif.aclk);
            
            if (vif.arvalid && vif.arready) begin
                trans = capture_read_transaction();
                
                if (is_narrow_transfer(trans)) begin
                    narrow_trans = convert_to_narrow(trans);
                    analyze_narrow_read(narrow_trans);
                    narrow_ap.write(narrow_trans);
                    narrow_read_count++;
                end else begin
                    normal_ap.write(trans);
                end
            end
        end
    endtask
    
    // Check if transfer is narrow
    function bit is_narrow_transfer(axi4_transaction trans);
        int transfer_bytes = 1 << trans.size;
        int bus_bytes = cfg.data_width / 8;
        return (transfer_bytes < bus_bytes);
    endfunction
    
    // Capture write transaction
    function axi4_transaction capture_write_transaction();
        axi4_transaction trans = axi4_transaction::type_id::create("trans");
        
        // Capture address phase
        trans.trans_type = AXI4_WRITE;
        trans.addr = vif.awaddr;
        trans.id = vif.awid;
        trans.len = vif.awlen;
        trans.size = vif.awsize;
        trans.burst = vif.awburst;
        trans.lock = vif.awlock;
        trans.cache = vif.awcache;
        trans.prot = vif.awprot;
        trans.qos = vif.awqos;
        trans.region = vif.awregion;
        trans.user = vif.awuser;
        
        // Capture data phase
        capture_write_data(trans);
        
        // Capture response
        capture_write_response(trans);
        
        return trans;
    endfunction
    
    // Capture read transaction
    function axi4_transaction capture_read_transaction();
        axi4_transaction trans = axi4_transaction::type_id::create("trans");
        
        // Capture address phase
        trans.trans_type = AXI4_READ;
        trans.addr = vif.araddr;
        trans.id = vif.arid;
        trans.len = vif.arlen;
        trans.size = vif.arsize;
        trans.burst = vif.arburst;
        trans.lock = vif.arlock;
        trans.cache = vif.arcache;
        trans.prot = vif.arprot;
        trans.qos = vif.arqos;
        trans.region = vif.arregion;
        trans.user = vif.aruser;
        
        // Capture data phase
        capture_read_data(trans);
        
        return trans;
    endfunction
    
    // Capture write data
    task capture_write_data(axi4_transaction trans);
        int beat_count = 0;
        
        trans.data = new[trans.len + 1];
        trans.strb = new[trans.len + 1];
        
        while (beat_count <= trans.len) begin
            @(posedge vif.aclk);
            if (vif.wvalid && vif.wready) begin
                trans.data[beat_count] = vif.wdata;
                trans.strb[beat_count] = vif.wstrb;
                
                if (vif.wlast) break;
                beat_count++;
            end
        end
    endtask
    
    // Capture write response
    task capture_write_response(axi4_transaction trans);
        @(posedge vif.aclk);
        while (!(vif.bvalid && vif.bready && vif.bid == trans.id)) begin
            @(posedge vif.aclk);
        end
        trans.resp = vif.bresp;
    endtask
    
    // Capture read data
    task capture_read_data(axi4_transaction trans);
        int beat_count = 0;
        
        trans.data = new[trans.len + 1];
        trans.resp = new[trans.len + 1];
        
        while (beat_count <= trans.len) begin
            @(posedge vif.aclk);
            if (vif.rvalid && vif.rready && vif.rid == trans.id) begin
                trans.data[beat_count] = vif.rdata;
                trans.resp[beat_count] = vif.rresp;
                
                if (vif.rlast) break;
                beat_count++;
            end
        end
    endtask
    
    // Convert to narrow transaction
    function axi4_narrow_transaction convert_to_narrow(axi4_transaction trans);
        axi4_narrow_transaction narrow = axi4_narrow_transaction::type_id::create("narrow");
        
        // Copy base fields
        narrow.copy_base(trans);
        
        // Calculate narrow-specific fields
        narrow.transfer_bytes = 1 << trans.size;
        narrow.bus_bytes = cfg.data_width / 8;
        narrow.start_lane = trans.addr & (narrow.bus_bytes - 1);
        narrow.end_lane = narrow.start_lane + narrow.transfer_bytes - 1;
        
        // Extract active data bytes
        if (trans.trans_type == AXI4_WRITE) begin
            narrow.active_data = new[trans.len + 1];
            foreach (trans.data[i]) begin
                narrow.active_data[i] = extract_active_bytes(
                    trans.data[i], 
                    trans.strb[i],
                    narrow.transfer_bytes
                );
            end
        end
        
        return narrow;
    endfunction
    
    // Extract active bytes based on strobe
    function bit [127:0] extract_active_bytes(bit [1023:0] data, bit [127:0] strb, int num_bytes);
        bit [127:0] active = 0;
        int active_idx = 0;
        
        for (int i = 0; i < cfg.data_width/8; i++) begin
            if (strb[i] && active_idx < num_bytes) begin
                active[active_idx*8 +: 8] = data[i*8 +: 8];
                active_idx++;
            end
        end
        
        return active;
    endfunction
    
    // Analyze narrow write
    function void analyze_narrow_write(axi4_narrow_transaction trans);
        // Check for sparse strobes
        foreach (trans.strb[i]) begin
            if (is_sparse_strobe(trans.strb[i], trans.transfer_bytes)) begin
                sparse_strobe_count++;
            end
        end
        
        // Check alignment
        if (trans.addr & ((1 << trans.size) - 1)) begin
            unaligned_narrow_count++;
        end
    endfunction
    
    // Analyze narrow read
    function void analyze_narrow_read(axi4_narrow_transaction trans);
        // Check alignment
        if (trans.addr & ((1 << trans.size) - 1)) begin
            unaligned_narrow_count++;
        end
    endfunction
    
    // Check if strobe is sparse
    function bit is_sparse_strobe(bit [127:0] strb, int expected_bytes);
        int active_count = 0;
        
        for (int i = 0; i < cfg.data_width/8; i++) begin
            if (strb[i]) active_count++;
        end
        
        return (active_count < expected_bytes);
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Narrow Transfer Monitor Report ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Narrow writes: %0d", narrow_write_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Narrow reads: %0d", narrow_read_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Sparse strobes: %0d", sparse_strobe_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Unaligned narrow: %0d", unaligned_narrow_count), UVM_LOW)
    endfunction
    
endclass

// Narrow transaction class
class axi4_narrow_transaction extends axi4_transaction;
    
    `uvm_object_utils(axi4_narrow_transaction)
    
    // Narrow-specific fields
    int transfer_bytes;
    int bus_bytes;
    int start_lane;
    int end_lane;
    bit [127:0] active_data[];
    bit is_sparse_strobe;
    bit crosses_boundary;
    
    // Constructor
    function new(string name = "axi4_narrow_transaction");
        super.new(name);
    endfunction
    
    // Copy base transaction
    function void copy_base(axi4_transaction trans);
        this.trans_type = trans.trans_type;
        this.addr = trans.addr;
        this.id = trans.id;
        this.len = trans.len;
        this.size = trans.size;
        this.burst = trans.burst;
        this.lock = trans.lock;
        this.cache = trans.cache;
        this.prot = trans.prot;
        this.qos = trans.qos;
        this.region = trans.region;
        this.user = trans.user;
        this.data = trans.data;
        this.strb = trans.strb;
        this.resp = trans.resp;
    endfunction
    
    // Convert to string
    function string convert2string();
        string str;
        str = super.convert2string();
        str = {str, $sformatf("\\n  Transfer size: %0d bytes", transfer_bytes)};
        str = {str, $sformatf("\\n  Bus width: %0d bytes", bus_bytes)};
        str = {str, $sformatf("\\n  Byte lanes: %0d-%0d", start_lane, end_lane)};
        return str;
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_narrow_transfer_monitor.sv")
        with open(filepath, 'w') as f:
            f.write(content)

def example_narrow_transfer_generation():
    """Example of generating narrow transfer tests"""
    
    config = {
        'num_masters': 4,
        'num_slaves': 4,
        'data_width': 128,  # 128-bit bus for good narrow transfer testing
        'addr_width': 64,
        'id_width': 8
    }
    
    generator = VIPNarrowTransferTestGenerator(config)
    output_dir = "vip_output/narrow_tests"
    os.makedirs(output_dir, exist_ok=True)
    
    print("Generating narrow transfer test components...")
    generator.generate_narrow_transfer_tests(output_dir)
    print("Narrow transfer test generation complete!")

if __name__ == "__main__":
    example_narrow_transfer_generation()