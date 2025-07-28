#!/usr/bin/env python3
"""
VIP Atomic Transaction Test Generator
Implements comprehensive exclusive access and atomic operation tests
Based on tim_axi4_vip exclusive access monitor and test scenarios
"""

import os
from datetime import datetime
from typing import Dict, List, Optional, Tuple

class VIPAtomicTransactionTestGenerator:
    """Generate atomic transaction test sequences"""
    
    def __init__(self, config):
        self.config = config
        self.timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        # Exclusive access constraints per AXI spec
        self.exclusive_constraints = {
            "max_size_bytes": 128,  # Maximum exclusive access size
            "valid_sizes": [1, 2, 4, 8, 16, 32, 64, 128],  # Power of 2 only
            "alignment_required": True,  # Must be aligned to size
            "single_transfer_only": True,  # Burst length must be 1
            "id_match_required": True,  # Write ID must match read ID
            "address_match_required": True  # Write addr must match read addr
        }
        
        # Test scenarios
        self.atomic_scenarios = {
            "basic": ["simple_exclusive", "multi_master_exclusive", "exclusive_timeout"],
            "size_variations": ["exclusive_1b", "exclusive_2b", "exclusive_4b", "exclusive_8b", 
                               "exclusive_16b", "exclusive_32b", "exclusive_64b", "exclusive_128b"],
            "failure_cases": ["id_mismatch", "addr_mismatch", "size_mismatch", "intervening_write",
                             "unaligned_access", "invalid_burst_len", "non_power2_size"],
            "corner_cases": ["back_to_back_exclusive", "nested_exclusive", "exclusive_to_different_addr",
                            "exclusive_across_masters", "exclusive_with_normal_traffic"],
            "stress_tests": ["multiple_exclusive_monitors", "exclusive_contention", "exclusive_livelock",
                            "exclusive_starvation", "exclusive_fairness"]
        }
        
    def generate_atomic_transaction_tests(self, output_dir: str):
        """Generate all atomic transaction test components"""
        
        # Create directory structure
        atomic_dir = os.path.join(output_dir, "atomic_transactions")
        os.makedirs(atomic_dir, exist_ok=True)
        
        # Generate components
        self._generate_exclusive_monitor(atomic_dir)
        self._generate_exclusive_tracker(atomic_dir)
        self._generate_atomic_test_sequences(atomic_dir)
        self._generate_exclusive_scoreboard(atomic_dir)
        self._generate_exclusive_coverage(atomic_dir)
        
        return True
        
    def _generate_exclusive_monitor(self, output_dir: str):
        """Generate exclusive access monitor"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Exclusive Access Monitor
// Generated: {self.timestamp}
// Description: Monitors and validates exclusive access transactions
//------------------------------------------------------------------------------

class axi4_exclusive_monitor extends uvm_monitor;
    
    `uvm_component_utils(axi4_exclusive_monitor)
    
    // Virtual interface
    virtual axi4_if vif;
    
    // Analysis ports
    uvm_analysis_port #(axi4_exclusive_transaction) exclusive_ap;
    uvm_analysis_port #(axi4_transaction) normal_ap;
    
    // Exclusive access tracking
    typedef struct {
        bit [63:0] address;
        bit [7:0] id;
        bit [2:0] size;
        bit [127:0] data;
        time timestamp;
        bit valid;
    } exclusive_entry_t;
    
    // Exclusive reservation table (per master)
    exclusive_entry_t exclusive_table[bit[7:0]];
    
    // Configuration
    axi4_config cfg;
    bit enable_timeout_check = 1;
    real exclusive_timeout_ns = 1000.0;
    
    // Statistics
    int unsigned exclusive_read_count;
    int unsigned exclusive_write_count;
    int unsigned exclusive_success_count;
    int unsigned exclusive_fail_count;
    int unsigned exclusive_timeout_count;
    int unsigned exclusive_violation_count;
    
    // Constructor
    function new(string name = "axi4_exclusive_monitor", uvm_component parent = null);
        super.new(name, parent);
        exclusive_ap = new("exclusive_ap", this);
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
            monitor_read_channel();
            monitor_write_channel();
            check_exclusive_timeouts();
        join
    endtask
    
    // Monitor read channel for exclusive accesses
    task monitor_read_channel();
        forever begin
            axi4_transaction trans;
            @(posedge vif.aclk);
            
            if (vif.arvalid && vif.arready) begin
                trans = axi4_transaction::type_id::create("trans");
                
                // Capture read address channel
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
                
                // Check if exclusive access
                if (trans.lock == 1'b1) begin // AXI4 exclusive
                    handle_exclusive_read(trans);
                end else begin
                    normal_ap.write(trans);
                end
                
                // Monitor read data
                monitor_read_data(trans);
            end
        end
    endtask
    
    // Monitor write channel for exclusive accesses
    task monitor_write_channel();
        forever begin
            axi4_transaction trans;
            @(posedge vif.aclk);
            
            if (vif.awvalid && vif.awready) begin
                trans = axi4_transaction::type_id::create("trans");
                
                // Capture write address channel
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
                
                // Monitor write data
                monitor_write_data(trans);
                
                // Check if exclusive access
                if (trans.lock == 1'b1) begin
                    handle_exclusive_write(trans);
                end else begin
                    // Normal write can clear exclusive reservations
                    check_intervening_write(trans);
                    normal_ap.write(trans);
                end
                
                // Monitor write response
                monitor_write_response(trans);
            end
        end
    endtask
    
    // Handle exclusive read
    task handle_exclusive_read(axi4_transaction trans);
        axi4_exclusive_transaction ex_trans;
        exclusive_entry_t entry;
        
        exclusive_read_count++;
        
        // Validate exclusive access constraints
        if (!validate_exclusive_constraints(trans)) begin
            `uvm_error(get_name(), "Exclusive read violates constraints")
            exclusive_violation_count++;
            return;
        end
        
        // Create exclusive entry
        entry.address = trans.addr;
        entry.id = trans.id;
        entry.size = trans.size;
        entry.timestamp = $time;
        entry.valid = 1;
        
        // Store in reservation table
        exclusive_table[trans.id] = entry;
        
        // Create exclusive transaction
        ex_trans = axi4_exclusive_transaction::type_id::create("ex_trans");
        ex_trans.copy(trans);
        ex_trans.exclusive_type = EXCLUSIVE_READ;
        ex_trans.reservation_time = $time;
        
        exclusive_ap.write(ex_trans);
        
        `uvm_info(get_name(), $sformatf("Exclusive read: ID=%0h, Addr=%0h, Size=%0d", 
                                       trans.id, trans.addr, 1 << trans.size), UVM_MEDIUM)
    endtask
    
    // Handle exclusive write
    task handle_exclusive_write(axi4_transaction trans);
        axi4_exclusive_transaction ex_trans;
        exclusive_entry_t entry;
        bit exclusive_success;
        
        exclusive_write_count++;
        
        // Check if matching exclusive read exists
        if (exclusive_table.exists(trans.id)) begin
            entry = exclusive_table[trans.id];
            
            if (entry.valid &&
                entry.address == trans.addr &&
                entry.size == trans.size) begin
                // Exclusive access success
                exclusive_success = 1;
                exclusive_success_count++;
                
                // Clear reservation
                exclusive_table[trans.id].valid = 0;
                
                `uvm_info(get_name(), $sformatf("Exclusive write SUCCESS: ID=%0h, Addr=%0h", 
                                               trans.id, trans.addr), UVM_MEDIUM)
            end else begin
                // Mismatch - exclusive fails
                exclusive_success = 0;
                exclusive_fail_count++;
                
                `uvm_info(get_name(), $sformatf("Exclusive write FAIL: ID=%0h, Addr=%0h (mismatch)", 
                                               trans.id, trans.addr), UVM_MEDIUM)
            end
        end else begin
            // No reservation - exclusive fails
            exclusive_success = 0;
            exclusive_fail_count++;
            
            `uvm_info(get_name(), $sformatf("Exclusive write FAIL: ID=%0h, Addr=%0h (no reservation)", 
                                           trans.id, trans.addr), UVM_MEDIUM)
        end
        
        // Create exclusive transaction
        ex_trans = axi4_exclusive_transaction::type_id::create("ex_trans");
        ex_trans.copy(trans);
        ex_trans.exclusive_type = EXCLUSIVE_WRITE;
        ex_trans.exclusive_success = exclusive_success;
        
        // Wait for response to update
        fork begin
            wait_for_response(trans.id);
            ex_trans.response = exclusive_success ? AXI4_EXOKAY : AXI4_OKAY;
        end join_none
        
        exclusive_ap.write(ex_trans);
    endtask
    
    // Check for intervening writes that clear exclusive reservations
    task check_intervening_write(axi4_transaction trans);
        foreach (exclusive_table[id]) begin
            if (exclusive_table[id].valid) begin
                // Check if write affects exclusive reservation
                bit [63:0] ex_start = exclusive_table[id].address;
                bit [63:0] ex_end = ex_start + (1 << exclusive_table[id].size) - 1;
                bit [63:0] wr_start = trans.addr;
                bit [63:0] wr_end = wr_start + ((trans.len + 1) * (1 << trans.size)) - 1;
                
                // Check for overlap
                if (!(wr_end < ex_start || wr_start > ex_end)) begin
                    // Overlapping write clears exclusive reservation
                    exclusive_table[id].valid = 0;
                    `uvm_info(get_name(), $sformatf("Intervening write clears exclusive: ID=%0h, Addr=%0h", 
                                                   id, exclusive_table[id].address), UVM_MEDIUM)
                end
            end
        end
    endtask
    
    // Check for exclusive access timeouts
    task check_exclusive_timeouts();
        forever begin
            #(exclusive_timeout_ns * 1ns / 10); // Check periodically
            
            if (enable_timeout_check) begin
                foreach (exclusive_table[id]) begin
                    if (exclusive_table[id].valid) begin
                        real elapsed = ($time - exclusive_table[id].timestamp) / 1ns;
                        if (elapsed > exclusive_timeout_ns) begin
                            exclusive_table[id].valid = 0;
                            exclusive_timeout_count++;
                            `uvm_info(get_name(), $sformatf("Exclusive timeout: ID=%0h, Addr=%0h", 
                                                           id, exclusive_table[id].address), UVM_MEDIUM)
                        end
                    end
                end
            end
        end
    endtask
    
    // Validate exclusive access constraints
    function bit validate_exclusive_constraints(axi4_transaction trans);
        bit valid = 1;
        
        // Check burst length (must be 1)
        if (trans.len != 0) begin
            `uvm_error(get_name(), $sformatf("Exclusive access burst length must be 1, got %0d", trans.len + 1))
            valid = 0;
        end
        
        // Check size (must be power of 2 and <= 128 bytes)
        if (!(1 << trans.size inside {{1, 2, 4, 8, 16, 32, 64, 128}})) begin
            `uvm_error(get_name(), $sformatf("Exclusive access size must be power of 2 <= 128, got %0d", 1 << trans.size))
            valid = 0;
        end
        
        // Check alignment
        if (trans.addr & ((1 << trans.size) - 1)) begin
            `uvm_error(get_name(), $sformatf("Exclusive access must be aligned, addr=%0h, size=%0d", trans.addr, 1 << trans.size))
            valid = 0;
        end
        
        // Check burst type (should be INCR)
        if (trans.burst != AXI4_INCR) begin
            `uvm_error(get_name(), "Exclusive access should use INCR burst type")
            valid = 0;
        end
        
        return valid;
    endfunction
    
    // Monitor read data
    task monitor_read_data(axi4_transaction trans);
        int beat_count = 0;
        
        trans.data = new[trans.len + 1];
        
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
    
    // Monitor write data
    task monitor_write_data(axi4_transaction trans);
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
    
    // Monitor write response
    task monitor_write_response(axi4_transaction trans);
        @(posedge vif.aclk);
        while (!(vif.bvalid && vif.bready && vif.bid == trans.id)) begin
            @(posedge vif.aclk);
        end
        trans.resp = vif.bresp;
    endtask
    
    // Wait for write response
    task wait_for_response(bit [7:0] id);
        @(posedge vif.aclk);
        while (!(vif.bvalid && vif.bready && vif.bid == id)) begin
            @(posedge vif.aclk);
        end
    endtask
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Exclusive Monitor Report ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Exclusive reads: %0d", exclusive_read_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Exclusive writes: %0d", exclusive_write_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Exclusive success: %0d", exclusive_success_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Exclusive failures: %0d", exclusive_fail_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Exclusive timeouts: %0d", exclusive_timeout_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Exclusive violations: %0d", exclusive_violation_count), UVM_LOW)
        
        if (exclusive_violation_count > 0) begin
            `uvm_error(get_name(), $sformatf("Found %0d exclusive access violations!", exclusive_violation_count))
        end
    endfunction
    
endclass

// Exclusive transaction class
class axi4_exclusive_transaction extends axi4_transaction;
    
    `uvm_object_utils(axi4_exclusive_transaction)
    
    typedef enum bit [1:0] {
        EXCLUSIVE_READ  = 2'b00,
        EXCLUSIVE_WRITE = 2'b01,
        EXCLUSIVE_CLEAR = 2'b10
    } exclusive_type_e;
    
    // Exclusive specific fields
    exclusive_type_e exclusive_type;
    bit exclusive_success;
    time reservation_time;
    time completion_time;
    bit intervening_write_detected;
    
    // Constructor
    function new(string name = "axi4_exclusive_transaction");
        super.new(name);
    endfunction
    
    // Copy method
    function void copy(axi4_transaction trans);
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
        str = {{str, $sformatf("\\n  Exclusive Type: %s", exclusive_type.name())}};
        str = {{str, $sformatf("\\n  Exclusive Success: %0b", exclusive_success)}};
        str = {{str, $sformatf("\\n  Reservation Time: %0t", reservation_time)}};
        return str;
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_exclusive_monitor.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_exclusive_tracker(self, output_dir: str):
        """Generate exclusive access tracker for multiple masters"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Exclusive Access Tracker
// Generated: {self.timestamp}
// Description: Tracks exclusive accesses across multiple masters
//------------------------------------------------------------------------------

class axi4_exclusive_tracker extends uvm_component;
    
    `uvm_component_utils(axi4_exclusive_tracker)
    
    // Analysis exports for each master
    uvm_analysis_imp_decl(_master0)
    uvm_analysis_imp_decl(_master1)
    uvm_analysis_imp_decl(_master2)
    uvm_analysis_imp_decl(_master3)
    
    uvm_analysis_imp_master0 #(axi4_exclusive_transaction, axi4_exclusive_tracker) master0_export;
    uvm_analysis_imp_master1 #(axi4_exclusive_transaction, axi4_exclusive_tracker) master1_export;
    uvm_analysis_imp_master2 #(axi4_exclusive_transaction, axi4_exclusive_tracker) master2_export;
    uvm_analysis_imp_master3 #(axi4_exclusive_transaction, axi4_exclusive_tracker) master3_export;
    
    // Global exclusive monitor table
    typedef struct {
        bit [63:0] address;
        bit [2:0] size;
        bit [3:0] master_id;
        bit [7:0] transaction_id;
        time reservation_time;
        bit valid;
    } global_exclusive_entry_t;
    
    // Global reservation table indexed by address
    global_exclusive_entry_t global_reservations[bit[63:0]];
    
    // Per-master statistics
    int exclusive_stats[4][string];
    
    // Configuration
    bit enable_global_timeout = 1;
    real global_timeout_ns = 2000.0;
    
    // Constructor
    function new(string name = "axi4_exclusive_tracker", uvm_component parent = null);
        super.new(name, parent);
        master0_export = new("master0_export", this);
        master1_export = new("master1_export", this);
        master2_export = new("master2_export", this);
        master3_export = new("master3_export", this);
    endfunction
    
    // Write methods for each master
    function void write_master0(axi4_exclusive_transaction trans);
        process_exclusive_transaction(0, trans);
    endfunction
    
    function void write_master1(axi4_exclusive_transaction trans);
        process_exclusive_transaction(1, trans);
    endfunction
    
    function void write_master2(axi4_exclusive_transaction trans);
        process_exclusive_transaction(2, trans);
    endfunction
    
    function void write_master3(axi4_exclusive_transaction trans);
        process_exclusive_transaction(3, trans);
    endfunction
    
    // Process exclusive transaction from any master
    function void process_exclusive_transaction(int master_id, axi4_exclusive_transaction trans);
        bit [63:0] aligned_addr = trans.addr & ~((1 << trans.size) - 1);
        
        case (trans.exclusive_type)
            EXCLUSIVE_READ: begin
                handle_global_exclusive_read(master_id, trans, aligned_addr);
                exclusive_stats[master_id]["exclusive_reads"]++;
            end
            
            EXCLUSIVE_WRITE: begin
                handle_global_exclusive_write(master_id, trans, aligned_addr);
                exclusive_stats[master_id]["exclusive_writes"]++;
                if (trans.exclusive_success) begin
                    exclusive_stats[master_id]["exclusive_success"]++;
                end else begin
                    exclusive_stats[master_id]["exclusive_fail"]++;
                end
            end
            
            EXCLUSIVE_CLEAR: begin
                clear_exclusive_reservation(aligned_addr);
                exclusive_stats[master_id]["exclusive_clears"]++;
            end
        endcase
    endfunction
    
    // Handle global exclusive read
    function void handle_global_exclusive_read(int master_id, axi4_exclusive_transaction trans, bit [63:0] addr);
        global_exclusive_entry_t entry;
        
        // Check if address already has reservation
        if (global_reservations.exists(addr)) begin
            entry = global_reservations[addr];
            
            if (entry.valid) begin
                `uvm_info(get_name(), $sformatf("Overwriting existing reservation: Master %0d -> Master %0d at addr %0h", 
                                               entry.master_id, master_id, addr), UVM_MEDIUM)
                exclusive_stats[entry.master_id]["reservations_lost"]++;
            end
        end
        
        // Create new reservation
        entry.address = addr;
        entry.size = trans.size;
        entry.master_id = master_id;
        entry.transaction_id = trans.id;
        entry.reservation_time = $time;
        entry.valid = 1;
        
        global_reservations[addr] = entry;
        
        `uvm_info(get_name(), $sformatf("Master %0d exclusive read reservation at addr %0h", master_id, addr), UVM_HIGH)
    endfunction
    
    // Handle global exclusive write
    function void handle_global_exclusive_write(int master_id, axi4_exclusive_transaction trans, bit [63:0] addr);
        global_exclusive_entry_t entry;
        bit expected_success;
        
        if (global_reservations.exists(addr)) begin
            entry = global_reservations[addr];
            
            if (entry.valid &&
                entry.master_id == master_id &&
                entry.transaction_id == trans.id &&
                entry.size == trans.size) begin
                expected_success = 1;
                
                // Clear reservation
                global_reservations[addr].valid = 0;
            end
        end
        
        // Verify exclusive result matches expectation
        if (trans.exclusive_success != expected_success) begin
            `uvm_error(get_name(), $sformatf("Exclusive result mismatch: Master %0d at addr %0h, expected %0b, got %0b",
                                            master_id, addr, expected_success, trans.exclusive_success))
            exclusive_stats[master_id]["result_mismatches"]++;
        end
        
        `uvm_info(get_name(), $sformatf("Master %0d exclusive write %s at addr %0h", 
                                       master_id, trans.exclusive_success ? "SUCCESS" : "FAIL", addr), UVM_HIGH)
    endfunction
    
    // Clear exclusive reservation
    function void clear_exclusive_reservation(bit [63:0] addr);
        if (global_reservations.exists(addr)) begin
            global_reservations[addr].valid = 0;
        end
    endfunction
    
    // Check for conflicts between masters
    function void check_exclusive_conflicts();
        bit [63:0] active_addrs[$];
        int conflicts = 0;
        
        foreach (global_reservations[addr]) begin
            if (global_reservations[addr].valid) begin
                active_addrs.push_back(addr);
            end
        end
        
        // Check for overlapping reservations
        foreach (active_addrs[i]) begin
            foreach (active_addrs[j]) begin
                if (i != j) begin
                    bit [63:0] addr1 = active_addrs[i];
                    bit [63:0] addr2 = active_addrs[j];
                    int size1 = 1 << global_reservations[addr1].size;
                    int size2 = 1 << global_reservations[addr2].size;
                    
                    // Check for overlap
                    if (!((addr1 + size1 <= addr2) || (addr2 + size2 <= addr1))) begin
                        `uvm_warning(get_name(), $sformatf("Overlapping exclusive reservations: Master %0d at %0h and Master %0d at %0h",
                                                          global_reservations[addr1].master_id, addr1,
                                                          global_reservations[addr2].master_id, addr2))
                        conflicts++;
                    end
                end
            end
        end
        
        if (conflicts > 0) begin
            exclusive_stats[0]["conflicts"] += conflicts;
        end
    endfunction
    
    // Timeout check task
    task run_phase(uvm_phase phase);
        forever begin
            #(global_timeout_ns * 1ns / 10);
            
            if (enable_global_timeout) begin
                foreach (global_reservations[addr]) begin
                    if (global_reservations[addr].valid) begin
                        real elapsed = ($time - global_reservations[addr].reservation_time) / 1ns;
                        if (elapsed > global_timeout_ns) begin
                            int master_id = global_reservations[addr].master_id;
                            global_reservations[addr].valid = 0;
                            exclusive_stats[master_id]["timeouts"]++;
                            
                            `uvm_info(get_name(), $sformatf("Global exclusive timeout: Master %0d at addr %0h", 
                                                           master_id, addr), UVM_MEDIUM)
                        end
                    end
                end
            end
            
            // Periodically check for conflicts
            check_exclusive_conflicts();
        end
    endtask
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Global Exclusive Tracker Report ===", UVM_LOW)
        
        for (int i = 0; i < 4; i++) begin
            if (exclusive_stats[i].size() > 0) begin
                `uvm_info(get_name(), $sformatf("Master %0d Statistics:", i), UVM_LOW)
                foreach (exclusive_stats[i][stat]) begin
                    `uvm_info(get_name(), $sformatf("  %s: %0d", stat, exclusive_stats[i][stat]), UVM_LOW)
                end
            end
        end
        
        // Report any remaining reservations
        int active_count = 0;
        foreach (global_reservations[addr]) begin
            if (global_reservations[addr].valid) begin
                active_count++;
                `uvm_warning(get_name(), $sformatf("Active reservation at end: Master %0d at addr %0h",
                                                  global_reservations[addr].master_id, addr))
            end
        end
        
        if (active_count > 0) begin
            `uvm_warning(get_name(), $sformatf("Found %0d active reservations at end of test", active_count))
        end
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_exclusive_tracker.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_atomic_test_sequences(self, output_dir: str):
        """Generate atomic transaction test sequences"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Atomic Transaction Test Sequences
// Generated: {self.timestamp}
// Description: Comprehensive exclusive access test scenarios
//------------------------------------------------------------------------------

// Base exclusive test sequence
class exclusive_base_sequence extends axi4_base_test_sequence;
    
    `uvm_object_utils(exclusive_base_sequence)
    
    // Exclusive test configuration
    rand bit [63:0] exclusive_addr;
    rand bit [2:0] exclusive_size;
    rand bit [7:0] exclusive_id;
    rand int exclusive_delay_ns;
    
    // Constraints
    constraint exclusive_c {
        exclusive_size inside {[0:7]}; // 1 to 128 bytes
        exclusive_addr[6:0] == 0; // 128-byte aligned for simplicity
        exclusive_delay_ns inside {[0:1000]};
    }
    
    // Constructor
    function new(string name = "exclusive_base_sequence");
        super.new(name);
    endfunction
    
    // Helper to perform exclusive read
    task do_exclusive_read(output axi4_transaction trans);
        trans = axi4_transaction::type_id::create("ex_read");
        
        assert(trans.randomize() with {
            trans_type == AXI4_READ;
            addr == exclusive_addr;
            id == exclusive_id;
            len == 0; // Single transfer
            size == exclusive_size;
            burst == AXI4_INCR;
            lock == 1'b1; // Exclusive
        });
        
        start_item(trans);
        finish_item(trans);
    endtask
    
    // Helper to perform exclusive write
    task do_exclusive_write(output axi4_transaction trans, input bit [127:0] data_value = '0);
        trans = axi4_transaction::type_id::create("ex_write");
        
        assert(trans.randomize() with {
            trans_type == AXI4_WRITE;
            addr == exclusive_addr;
            id == exclusive_id;
            len == 0; // Single transfer
            size == exclusive_size;
            burst == AXI4_INCR;
            lock == 1'b1; // Exclusive
        });
        
        trans.data = new[1];
        trans.data[0] = data_value;
        trans.strb = new[1];
        trans.strb[0] = '1;
        
        start_item(trans);
        finish_item(trans);
    endtask
    
endclass

// Simple exclusive access test
class simple_exclusive_sequence extends exclusive_base_sequence;
    
    `uvm_object_utils(simple_exclusive_sequence)
    
    function new(string name = "simple_exclusive_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction read_trans, write_trans;
        
        `uvm_info(get_type_name(), "Starting simple exclusive sequence", UVM_LOW)
        
        repeat (num_transactions) begin
            // Randomize exclusive parameters
            assert(this.randomize());
            
            // Exclusive read
            do_exclusive_read(read_trans);
            
            // Small delay
            #(exclusive_delay_ns * 1ns);
            
            // Exclusive write
            do_exclusive_write(write_trans, read_trans.data[0] + 1);
            
            // Check response
            if (write_trans.resp == AXI4_EXOKAY) begin
                `uvm_info(get_type_name(), "Exclusive access successful", UVM_MEDIUM)
            end else begin
                `uvm_info(get_type_name(), "Exclusive access failed", UVM_MEDIUM)
            end
            
            wait_random_delay();
        end
    endtask
    
endclass

// Exclusive size sweep test
class exclusive_size_sweep_sequence extends exclusive_base_sequence;
    
    `uvm_object_utils(exclusive_size_sweep_sequence)
    
    function new(string name = "exclusive_size_sweep_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction read_trans, write_trans;
        bit [2:0] size_values[] = '{0, 1, 2, 3, 4, 5, 6, 7}; // 1B to 128B
        
        `uvm_info(get_type_name(), "Starting exclusive size sweep", UVM_LOW)
        
        foreach (size_values[i]) begin
            exclusive_size = size_values[i];
            exclusive_addr = 64'h1000_0000 + (i * 'h1000);
            exclusive_addr &= ~((1 << exclusive_size) - 1); // Align
            
            `uvm_info(get_type_name(), $sformatf("Testing exclusive size: %0d bytes", 1 << exclusive_size), UVM_MEDIUM)
            
            // Exclusive read
            do_exclusive_read(read_trans);
            
            // Exclusive write
            do_exclusive_write(write_trans);
            
            // Verify EXOKAY response
            if (write_trans.resp != AXI4_EXOKAY) begin
                `uvm_error(get_type_name(), $sformatf("Expected EXOKAY for size %0d, got %s", 
                                                    1 << exclusive_size, write_trans.resp.name()))
            end
        end
    endtask
    
endclass

// Multi-master exclusive contention test
class multi_master_exclusive_sequence extends exclusive_base_sequence;
    
    `uvm_object_utils(multi_master_exclusive_sequence)
    
    function new(string name = "multi_master_exclusive_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans[4];
        bit [63:0] shared_addr = 64'h2000_0000;
        
        `uvm_info(get_type_name(), "Starting multi-master exclusive contention", UVM_LOW)
        
        repeat (num_transactions) begin
            // Multiple masters try exclusive access to same address
            fork
                begin // Master 0
                    exclusive_addr = shared_addr;
                    exclusive_id = 8'h00;
                    do_exclusive_read(trans[0]);
                    #10ns;
                    do_exclusive_write(trans[0]);
                end
                
                begin // Master 1
                    #5ns; // Slight delay
                    exclusive_addr = shared_addr;
                    exclusive_id = 8'h10;
                    do_exclusive_read(trans[1]);
                    #10ns;
                    do_exclusive_write(trans[1]);
                end
                
                begin // Master 2
                    #8ns; // Different delay
                    exclusive_addr = shared_addr;
                    exclusive_id = 8'h20;
                    do_exclusive_read(trans[2]);
                    #10ns;
                    do_exclusive_write(trans[2]);
                end
                
                begin // Master 3
                    #12ns; // Later start
                    exclusive_addr = shared_addr;
                    exclusive_id = 8'h30;
                    do_exclusive_read(trans[3]);
                    #10ns;
                    do_exclusive_write(trans[3]);
                end
            join
            
            // Check that at most one succeeded
            int success_count = 0;
            foreach (trans[i]) begin
                if (trans[i] != null && trans[i].resp == AXI4_EXOKAY) begin
                    success_count++;
                    `uvm_info(get_type_name(), $sformatf("Master %0d exclusive succeeded", i), UVM_MEDIUM)
                end
            end
            
            if (success_count > 1) begin
                `uvm_error(get_type_name(), $sformatf("Multiple exclusive successes (%0d) - coherency violation!", success_count))
            end
            
            shared_addr += 'h100;
            #100ns;
        end
    endtask
    
endclass

// Exclusive failure test - intervening write
class exclusive_intervening_write_sequence extends exclusive_base_sequence;
    
    `uvm_object_utils(exclusive_intervening_write_sequence)
    
    function new(string name = "exclusive_intervening_write_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction ex_read, normal_write, ex_write;
        
        `uvm_info(get_type_name(), "Starting intervening write test", UVM_LOW)
        
        repeat (num_transactions) begin
            assert(this.randomize());
            
            // Exclusive read
            do_exclusive_read(ex_read);
            
            // Normal write to same address (clears reservation)
            normal_write = axi4_transaction::type_id::create("normal_write");
            assert(normal_write.randomize() with {
                trans_type == AXI4_WRITE;
                addr == exclusive_addr;
                id == exclusive_id + 1; // Different ID
                len == 0;
                size == exclusive_size;
                burst == AXI4_INCR;
                lock == 1'b0; // Normal access
            });
            
            start_item(normal_write);
            finish_item(normal_write);
            
            // Exclusive write (should fail)
            do_exclusive_write(ex_write);
            
            // Verify failure
            if (ex_write.resp == AXI4_EXOKAY) begin
                `uvm_error(get_type_name(), "Exclusive succeeded after intervening write!")
            end else begin
                `uvm_info(get_type_name(), "Exclusive correctly failed after intervening write", UVM_MEDIUM)
            end
        end
    endtask
    
endclass

// Exclusive address mismatch test
class exclusive_addr_mismatch_sequence extends exclusive_base_sequence;
    
    `uvm_object_utils(exclusive_addr_mismatch_sequence)
    
    function new(string name = "exclusive_addr_mismatch_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction ex_read, ex_write;
        bit [63:0] read_addr, write_addr;
        
        `uvm_info(get_type_name(), "Starting address mismatch test", UVM_LOW)
        
        repeat (num_transactions) begin
            assert(this.randomize());
            
            read_addr = exclusive_addr;
            write_addr = exclusive_addr + 'h100; // Different address
            
            // Exclusive read
            exclusive_addr = read_addr;
            do_exclusive_read(ex_read);
            
            // Exclusive write to different address
            exclusive_addr = write_addr;
            do_exclusive_write(ex_write);
            
            // Should fail
            if (ex_write.resp == AXI4_EXOKAY) begin
                `uvm_error(get_type_name(), "Exclusive succeeded with address mismatch!")
            end
        end
    endtask
    
endclass

// Exclusive timeout test
class exclusive_timeout_sequence extends exclusive_base_sequence;
    
    `uvm_object_utils(exclusive_timeout_sequence)
    
    function new(string name = "exclusive_timeout_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction ex_read, ex_write;
        int timeout_delay = 2000; // 2us - longer than typical timeout
        
        `uvm_info(get_type_name(), "Starting exclusive timeout test", UVM_LOW)
        
        repeat (num_transactions) begin
            assert(this.randomize());
            
            // Exclusive read
            do_exclusive_read(ex_read);
            
            // Long delay to trigger timeout
            #(timeout_delay * 1ns);
            
            // Exclusive write (should fail due to timeout)
            do_exclusive_write(ex_write);
            
            if (ex_write.resp == AXI4_EXOKAY) begin
                `uvm_warning(get_type_name(), "Exclusive succeeded after timeout delay - check timeout implementation")
            end else begin
                `uvm_info(get_type_name(), "Exclusive correctly failed after timeout", UVM_MEDIUM)
            end
        end
    endtask
    
endclass

// Back-to-back exclusive test
class back_to_back_exclusive_sequence extends exclusive_base_sequence;
    
    `uvm_object_utils(back_to_back_exclusive_sequence)
    
    function new(string name = "back_to_back_exclusive_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        `uvm_info(get_type_name(), "Starting back-to-back exclusive test", UVM_LOW)
        
        repeat (num_transactions) begin
            // Rapid exclusive sequences
            for (int i = 0; i < 10; i++) begin
                exclusive_addr = 64'h3000_0000 + (i * 'h100);
                exclusive_id = i[7:0];
                
                // Exclusive read
                do_exclusive_read(trans);
                
                // Immediate exclusive write
                do_exclusive_write(trans);
                
                // Verify success
                if (trans.resp != AXI4_EXOKAY) begin
                    `uvm_error(get_type_name(), $sformatf("Back-to-back exclusive %0d failed", i))
                end
            end
            
            #100ns;
        end
    endtask
    
endclass

// Exclusive constraint violation test
class exclusive_violation_sequence extends exclusive_base_sequence;
    
    `uvm_object_utils(exclusive_violation_sequence)
    
    function new(string name = "exclusive_violation_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        `uvm_info(get_type_name(), "Starting exclusive violation tests", UVM_LOW)
        
        // Test 1: Non-power-of-2 size (invalid)
        trans = axi4_transaction::type_id::create("trans");
        assert(trans.randomize() with {
            trans_type == AXI4_READ;
            addr == 64'h4000_0000;
            len == 0;
            size == 3; // 8 bytes - valid
            burst == AXI4_INCR;
            lock == 1'b1;
        });
        // Manually corrupt to invalid size
        trans.size = 3'b111; // Would be 256 bytes if valid
        
        start_item(trans);
        finish_item(trans);
        
        // Test 2: Burst length > 1 (invalid)
        trans = axi4_transaction::type_id::create("trans");
        assert(trans.randomize() with {
            trans_type == AXI4_READ;
            addr == 64'h4000_1000;
            len == 3; // 4 beats - invalid for exclusive
            size == 2;
            burst == AXI4_INCR;
            lock == 1'b1;
        });
        
        start_item(trans);
        finish_item(trans);
        
        // Test 3: Unaligned address
        trans = axi4_transaction::type_id::create("trans");
        assert(trans.randomize() with {
            trans_type == AXI4_READ;
            addr == 64'h4000_2003; // Unaligned for any size > 0
            len == 0;
            size == 2; // 4 bytes
            burst == AXI4_INCR;
            lock == 1'b1;
        });
        
        start_item(trans);
        finish_item(trans);
        
        `uvm_info(get_type_name(), "Violation tests complete - check monitor for errors", UVM_LOW)
    endtask
    
endclass
'''
        
        filepath = os.path.join(output_dir, "atomic_test_sequences.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_exclusive_scoreboard(self, output_dir: str):
        """Generate exclusive access scoreboard"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Exclusive Access Scoreboard
// Generated: {self.timestamp}
// Description: Tracks and verifies exclusive access behavior
//------------------------------------------------------------------------------

class exclusive_access_scoreboard extends uvm_scoreboard;
    
    `uvm_component_utils(exclusive_access_scoreboard)
    
    // Analysis exports
    uvm_analysis_imp_decl(_monitor)
    uvm_analysis_imp_decl(_predictor)
    
    uvm_analysis_imp_monitor #(axi4_exclusive_transaction, exclusive_access_scoreboard) monitor_export;
    uvm_analysis_imp_predictor #(axi4_transaction, exclusive_access_scoreboard) predictor_export;
    
    // Exclusive reservation tracking
    typedef struct {
        bit [63:0] address;
        bit [7:0] id;
        bit [2:0] size;
        bit [127:0] data;
        time timestamp;
        bit valid;
        int master_id;
    } reservation_entry_t;
    
    // Reservation table
    reservation_entry_t reservations[bit[7:0]][bit[63:0]]; // [ID][Address]
    
    // Expected responses
    axi4_resp_e expected_responses[bit[7:0]][$];
    
    // Statistics
    int exclusive_predictions_correct;
    int exclusive_predictions_wrong;
    int unexpected_exclusive_success;
    int unexpected_exclusive_fail;
    
    // Constructor
    function new(string name = "exclusive_access_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        monitor_export = new("monitor_export", this);
        predictor_export = new("predictor_export", this);
    endfunction
    
    // Monitor write method
    function void write_monitor(axi4_exclusive_transaction trans);
        check_exclusive_result(trans);
    endfunction
    
    // Predictor write method
    function void write_predictor(axi4_transaction trans);
        predict_exclusive_behavior(trans);
    endfunction
    
    // Predict exclusive behavior
    function void predict_exclusive_behavior(axi4_transaction trans);
        bit [63:0] aligned_addr = trans.addr & ~((1 << trans.size) - 1);
        axi4_resp_e predicted_resp;
        
        if (trans.lock != 1'b1) begin
            // Normal transaction - may clear exclusive reservations
            if (trans.trans_type == AXI4_WRITE) begin
                clear_overlapping_reservations(trans);
            end
            return;
        end
        
        // Exclusive transaction
        if (trans.trans_type == AXI4_READ) begin
            // Exclusive read - create reservation
            reservation_entry_t entry;
            entry.address = aligned_addr;
            entry.id = trans.id;
            entry.size = trans.size;
            entry.timestamp = $time;
            entry.valid = 1;
            entry.master_id = trans.id[7:4];
            
            reservations[trans.id][aligned_addr] = entry;
            
        end else if (trans.trans_type == AXI4_WRITE) begin
            // Exclusive write - check reservation
            if (reservations[trans.id].exists(aligned_addr) &&
                reservations[trans.id][aligned_addr].valid &&
                reservations[trans.id][aligned_addr].size == trans.size) begin
                // Should succeed
                predicted_resp = AXI4_EXOKAY;
                reservations[trans.id][aligned_addr].valid = 0;
            end else begin
                // Should fail
                predicted_resp = AXI4_OKAY;
            end
            
            // Store prediction
            expected_responses[trans.id].push_back(predicted_resp);
        end
    endfunction
    
    // Clear overlapping reservations
    function void clear_overlapping_reservations(axi4_transaction trans);
        bit [63:0] wr_start = trans.addr;
        bit [63:0] wr_end = wr_start + ((trans.len + 1) * (1 << trans.size)) - 1;
        
        foreach (reservations[id]) begin
            foreach (reservations[id][addr]) begin
                if (reservations[id][addr].valid) begin
                    bit [63:0] res_start = addr;
                    bit [63:0] res_end = res_start + (1 << reservations[id][addr].size) - 1;
                    
                    // Check overlap
                    if (!(wr_end < res_start || wr_start > res_end)) begin
                        reservations[id][addr].valid = 0;
                        `uvm_info(get_name(), $sformatf("Cleared reservation ID=%0h, Addr=%0h due to write", id, addr), UVM_HIGH)
                    end
                end
            end
        end
    endfunction
    
    // Check exclusive result
    function void check_exclusive_result(axi4_exclusive_transaction trans);
        axi4_resp_e expected_resp;
        
        if (trans.exclusive_type == EXCLUSIVE_WRITE) begin
            // Get expected response
            if (expected_responses[trans.id].size() > 0) begin
                expected_resp = expected_responses[trans.id].pop_front();
                
                // Compare with actual
                if (trans.resp == expected_resp) begin
                    exclusive_predictions_correct++;
                    `uvm_info(get_name(), $sformatf("Exclusive prediction correct: ID=%0h, Addr=%0h, Resp=%s",
                                                   trans.id, trans.addr, trans.resp.name()), UVM_HIGH)
                end else begin
                    exclusive_predictions_wrong++;
                    `uvm_error(get_name(), $sformatf("Exclusive prediction wrong: ID=%0h, Addr=%0h, Expected=%s, Got=%s",
                                                    trans.id, trans.addr, expected_resp.name(), trans.resp.name()))
                end
            end else begin
                // No prediction available
                if (trans.resp == AXI4_EXOKAY) begin
                    unexpected_exclusive_success++;
                    `uvm_warning(get_name(), $sformatf("Unexpected exclusive success: ID=%0h, Addr=%0h", trans.id, trans.addr))
                end else begin
                    unexpected_exclusive_fail++;
                end
            end
            
            // Additional checks
            check_exclusive_constraints(trans);
        end
    endfunction
    
    // Check exclusive constraints
    function void check_exclusive_constraints(axi4_exclusive_transaction trans);
        // Size must be power of 2
        if (!(1 << trans.size inside {{1, 2, 4, 8, 16, 32, 64, 128}})) begin
            `uvm_error(get_name(), $sformatf("Invalid exclusive size: %0d bytes", 1 << trans.size))
        end
        
        // Must be aligned
        if (trans.addr & ((1 << trans.size) - 1)) begin
            `uvm_error(get_name(), $sformatf("Unaligned exclusive access: addr=%0h, size=%0d", trans.addr, 1 << trans.size))
        end
        
        // Burst length must be 1
        if (trans.len != 0) begin
            `uvm_error(get_name(), $sformatf("Invalid exclusive burst length: %0d", trans.len + 1))
        end
    endfunction
    
    // Check phase - look for hanging reservations
    function void check_phase(uvm_phase phase);
        int hanging_count = 0;
        
        foreach (reservations[id]) begin
            foreach (reservations[id][addr]) begin
                if (reservations[id][addr].valid) begin
                    hanging_count++;
                    `uvm_warning(get_name(), $sformatf("Hanging reservation: ID=%0h, Addr=%0h", id, addr))
                end
            end
        end
        
        if (hanging_count > 0) begin
            `uvm_warning(get_name(), $sformatf("Found %0d hanging exclusive reservations", hanging_count))
        end
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Exclusive Access Scoreboard Report ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Predictions correct: %0d", exclusive_predictions_correct), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Predictions wrong: %0d", exclusive_predictions_wrong), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Unexpected successes: %0d", unexpected_exclusive_success), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Unexpected failures: %0d", unexpected_exclusive_fail), UVM_LOW)
        
        if (exclusive_predictions_wrong > 0) begin
            `uvm_error(get_name(), $sformatf("Found %0d exclusive prediction mismatches!", exclusive_predictions_wrong))
        end
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "exclusive_access_scoreboard.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_exclusive_coverage(self, output_dir: str):
        """Generate exclusive access coverage model"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Exclusive Access Coverage Model
// Generated: {self.timestamp}
// Description: Functional coverage for exclusive access features
//------------------------------------------------------------------------------

class exclusive_access_coverage extends uvm_subscriber #(axi4_exclusive_transaction);
    
    `uvm_component_utils(exclusive_access_coverage)
    
    // Transaction handle
    axi4_exclusive_transaction trans;
    
    // Coverage groups
    covergroup exclusive_basic_cg;
        // Exclusive type
        exclusive_type_cp: coverpoint trans.exclusive_type {
            bins read = {EXCLUSIVE_READ};
            bins write = {EXCLUSIVE_WRITE};
            bins clear = {EXCLUSIVE_CLEAR};
        }
        
        // Exclusive result
        exclusive_result_cp: coverpoint trans.exclusive_success iff (trans.exclusive_type == EXCLUSIVE_WRITE) {
            bins success = {1};
            bins fail = {0};
        }
        
        // Response type
        response_cp: coverpoint trans.resp iff (trans.exclusive_type == EXCLUSIVE_WRITE) {
            bins exokay = {AXI4_EXOKAY};
            bins okay = {AXI4_OKAY};
            bins slverr = {AXI4_SLVERR};
            bins decerr = {AXI4_DECERR};
        }
        
        // Cross coverage
        exclusive_cross: cross exclusive_type_cp, exclusive_result_cp;
    endgroup
    
    covergroup exclusive_size_cg;
        // Size variations
        size_cp: coverpoint trans.size {
            bins size_1b = {0};
            bins size_2b = {1};
            bins size_4b = {2};
            bins size_8b = {3};
            bins size_16b = {4};
            bins size_32b = {5};
            bins size_64b = {6};
            bins size_128b = {7};
        }
        
        // Size with result
        size_result_cross: cross size_cp, trans.exclusive_success 
            iff (trans.exclusive_type == EXCLUSIVE_WRITE);
    endgroup
    
    covergroup exclusive_alignment_cg;
        // Address alignment
        alignment_cp: coverpoint trans.addr[6:0] {
            bins aligned_1b = {0};
            bins aligned_2b = {0, 2, 4, 6, 8, 10, 12, 14};
            bins aligned_4b = {0, 4, 8, 12, 16, 20, 24, 28};
            bins aligned_8b = {0, 8, 16, 24, 32, 40, 48, 56};
            bins aligned_16b = {0, 16, 32, 48, 64, 80, 96, 112};
            bins aligned_32b = {0, 32, 64, 96};
            bins aligned_64b = {0, 64};
            bins aligned_128b = {0};
            bins unaligned = default;
        }
        
        // Alignment with size
        alignment_size_cross: cross alignment_cp, trans.size;
    endgroup
    
    covergroup exclusive_id_cg;
        // ID distribution
        id_cp: coverpoint trans.id {
            bins id_low = {[0:63]};
            bins id_mid = {[64:127]};
            bins id_high = {[128:191]};
            bins id_max = {[192:255]};
        }
        
        // Master ID (upper 4 bits)
        master_id_cp: coverpoint trans.id[7:4] {
            bins master[16] = {[0:15]};
        }
    endgroup
    
    covergroup exclusive_timing_cg;
        // Time between exclusive read and write
        reservation_time_cp: coverpoint (trans.completion_time - trans.reservation_time) 
            iff (trans.exclusive_type == EXCLUSIVE_WRITE) {
            bins immediate = {[0:10]};
            bins fast = {[11:100]};
            bins normal = {[101:1000]};
            bins slow = {[1001:10000]};
            bins very_slow = {[10001:$]};
        }
        
        // Intervening write detection
        intervening_write_cp: coverpoint trans.intervening_write_detected 
            iff (trans.exclusive_type == EXCLUSIVE_WRITE);
    endgroup
    
    covergroup exclusive_scenarios_cg;
        // Special scenarios
        scenario_cp: coverpoint trans.exclusive_type {
            bins read_write_sequence = (EXCLUSIVE_READ => EXCLUSIVE_WRITE);
            bins read_clear_sequence = (EXCLUSIVE_READ => EXCLUSIVE_CLEAR);
            bins back_to_back_read = (EXCLUSIVE_READ => EXCLUSIVE_READ);
            bins write_after_clear = (EXCLUSIVE_CLEAR => EXCLUSIVE_WRITE);
        }
    endgroup
    
    // Constructor
    function new(string name = "exclusive_access_coverage", uvm_component parent = null);
        super.new(name, parent);
        exclusive_basic_cg = new();
        exclusive_size_cg = new();
        exclusive_alignment_cg = new();
        exclusive_id_cg = new();
        exclusive_timing_cg = new();
        exclusive_scenarios_cg = new();
    endfunction
    
    // Write method
    function void write(axi4_exclusive_transaction t);
        trans = t;
        
        // Sample all covergroups
        exclusive_basic_cg.sample();
        exclusive_size_cg.sample();
        exclusive_alignment_cg.sample();
        exclusive_id_cg.sample();
        exclusive_timing_cg.sample();
        exclusive_scenarios_cg.sample();
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Exclusive Access Coverage Report ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Basic coverage: %.1f%%", exclusive_basic_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Size coverage: %.1f%%", exclusive_size_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Alignment coverage: %.1f%%", exclusive_alignment_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("ID coverage: %.1f%%", exclusive_id_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Timing coverage: %.1f%%", exclusive_timing_cg.get_coverage()), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Scenario coverage: %.1f%%", exclusive_scenarios_cg.get_coverage()), UVM_LOW)
        
        real total_coverage = (exclusive_basic_cg.get_coverage() + 
                              exclusive_size_cg.get_coverage() + 
                              exclusive_alignment_cg.get_coverage() + 
                              exclusive_id_cg.get_coverage() + 
                              exclusive_timing_cg.get_coverage() + 
                              exclusive_scenarios_cg.get_coverage()) / 6.0;
                              
        `uvm_info(get_name(), $sformatf("Total exclusive coverage: %.1f%%", total_coverage), UVM_LOW)
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "exclusive_access_coverage.sv")
        with open(filepath, 'w') as f:
            f.write(content)

def example_atomic_transaction_generation():
    """Example of generating atomic transaction tests"""
    
    config = {
        'num_masters': 4,
        'num_slaves': 4,
        'data_width': 128,
        'addr_width': 64,
        'id_width': 8,
        'support_exclusive': True
    }
    
    generator = VIPAtomicTransactionTestGenerator(config)
    output_dir = "vip_output/atomic_tests"
    os.makedirs(output_dir, exist_ok=True)
    
    print("Generating atomic transaction test components...")
    generator.generate_atomic_transaction_tests(output_dir)
    print("Atomic transaction test generation complete!")

if __name__ == "__main__":
    example_atomic_transaction_generation()