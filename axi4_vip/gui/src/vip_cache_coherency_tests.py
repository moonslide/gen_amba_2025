#!/usr/bin/env python3
"""
VIP Cache Coherency Test Generator
Implements comprehensive cache coherency test scenarios
Based on tim_axi4_vip ACE-Lite and cache attribute testing
"""

import os
from datetime import datetime
from typing import Dict, List, Optional, Tuple

class VIPCacheCoherencyTestGenerator:
    """Generate cache coherency test sequences"""
    
    def __init__(self, config):
        self.config = config
        self.timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        # AxCACHE encoding based on AXI4 spec
        self.cache_encodings = {
            # [3:0] = [Other_Allocate, Allocate, Modifiable, Bufferable]
            "device_non_bufferable": "0000",      # Device Non-bufferable
            "device_bufferable": "0001",           # Device Bufferable
            "normal_non_cacheable_non_bufferable": "0010",  # Normal Non-cacheable Non-bufferable
            "normal_non_cacheable_bufferable": "0011",      # Normal Non-cacheable Bufferable
            "write_through_no_allocate": "1010",   # Write-through No-allocate
            "write_through_read_allocate": "1110", # Write-through Read-allocate
            "write_through_write_allocate": "1010", # Write-through Write-allocate
            "write_through_read_write_allocate": "1110", # Write-through Read and Write-allocate
            "write_back_no_allocate": "1011",      # Write-back No-allocate
            "write_back_read_allocate": "1111",    # Write-back Read-allocate
            "write_back_write_allocate": "1011",   # Write-back Write-allocate
            "write_back_read_write_allocate": "1111" # Write-back Read and Write-allocate
        }
        
        # Memory types and domains
        self.memory_types = {
            "strongly_ordered": {"cacheable": False, "bufferable": False, "domain": "system"},
            "device": {"cacheable": False, "bufferable": True, "domain": "system"},
            "normal_uncached": {"cacheable": False, "bufferable": True, "domain": "inner"},
            "normal_cached_wt": {"cacheable": True, "bufferable": True, "domain": "inner", "policy": "write_through"},
            "normal_cached_wb": {"cacheable": True, "bufferable": True, "domain": "inner", "policy": "write_back"}
        }
        
    def generate_cache_coherency_tests(self, output_dir: str):
        """Generate all cache coherency test components"""
        
        # Create directory structure
        cache_dir = os.path.join(output_dir, "cache_coherency")
        os.makedirs(cache_dir, exist_ok=True)
        
        # Generate components
        self._generate_cache_attribute_checker(cache_dir)
        self._generate_ace_lite_monitor(cache_dir)
        self._generate_cache_test_sequences(cache_dir)
        self._generate_coherency_scoreboard(cache_dir)
        self._generate_cache_state_machine(cache_dir)
        
        return True
        
    def _generate_cache_attribute_checker(self, output_dir: str):
        """Generate cache attribute checker"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Cache Attribute Checker
// Generated: {self.timestamp}
// Description: Checks cache attribute compliance and consistency
//------------------------------------------------------------------------------

class axi4_cache_attribute_checker extends uvm_component;
    
    `uvm_component_utils(axi4_cache_attribute_checker)
    
    // Configuration
    axi4_config cfg;
    
    // Analysis ports
    uvm_analysis_port #(axi4_transaction) write_ap;
    uvm_analysis_port #(axi4_transaction) read_ap;
    
    // Statistics
    int unsigned device_access_count;
    int unsigned normal_access_count;
    int unsigned cacheable_access_count;
    int unsigned bufferable_access_count;
    int unsigned allocate_hint_count;
    int unsigned modifiable_access_count;
    
    // Error counters
    int unsigned cache_attr_errors;
    int unsigned coherency_errors;
    int unsigned ordering_errors;
    
    // Constructor
    function new(string name = "axi4_cache_attribute_checker", uvm_component parent = null);
        super.new(name, parent);
        write_ap = new("write_ap", this);
        read_ap = new("read_ap", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(axi4_config)::get(this, "", "axi4_config", cfg)) begin
            `uvm_fatal("CONFIG", "Failed to get axi4_config")
        end
    endfunction
    
    // Write monitor
    function void write(axi4_transaction trans);
        check_cache_attributes(trans);
        check_coherency_rules(trans);
        update_statistics(trans);
    endfunction
    
    // Check cache attributes
    function void check_cache_attributes(axi4_transaction trans);
        bit [3:0] cache_val;
        bit bufferable, modifiable, allocate, other_allocate;
        
        cache_val = (trans.trans_type == AXI4_WRITE) ? trans.awcache : trans.arcache;
        
        // Decode cache attributes
        bufferable = cache_val[0];
        modifiable = cache_val[1];
        allocate = cache_val[2];
        other_allocate = cache_val[3];
        
        // Check for invalid combinations
        if (!bufferable && modifiable) begin
            `uvm_error(get_name(), "Invalid cache attribute: Modifiable requires Bufferable")
            cache_attr_errors++;
        end
        
        // Device memory checks
        if (is_device_memory(trans.addr)) begin
            if (cache_val[1]) begin
                `uvm_error(get_name(), "Device memory must not be Cacheable")
                cache_attr_errors++;
            end
            device_access_count++;
        end
        // Normal memory checks
        else begin
            normal_access_count++;
            if (cache_val[1]) cacheable_access_count++;
        end
        
        if (bufferable) bufferable_access_count++;
        if (allocate || other_allocate) allocate_hint_count++;
        if (modifiable) modifiable_access_count++;
    endfunction
    
    // Check coherency rules
    function void check_coherency_rules(axi4_transaction trans);
        static bit [63:0] exclusive_monitors[bit[63:0]];
        
        // Check exclusive access coherency
        if (trans.lock_type == AXI4_EXCLUSIVE) begin
            if (trans.trans_type == AXI4_READ) begin
                // Mark exclusive monitor
                exclusive_monitors[trans.addr] = 1;
            end
            else if (trans.trans_type == AXI4_WRITE) begin
                // Check exclusive monitor
                if (!exclusive_monitors.exists(trans.addr)) begin
                    `uvm_warning(get_name(), "Exclusive write without prior exclusive read")
                    coherency_errors++;
                end
                exclusive_monitors.delete(trans.addr);
            end
        end
        
        // Check memory ordering based on cache attributes
        check_memory_ordering(trans);
    endfunction
    
    // Check memory ordering rules
    function void check_memory_ordering(axi4_transaction trans);
        static axi4_transaction pending_trans[$];
        bit [3:0] cache_val;
        bit modifiable;
        
        cache_val = (trans.trans_type == AXI4_WRITE) ? trans.awcache : trans.arcache;
        modifiable = cache_val[1];
        
        // Non-modifiable transactions must maintain order
        if (!modifiable) begin
            foreach (pending_trans[i]) begin
                if (pending_trans[i].id == trans.id && 
                    pending_trans[i].trans_type == trans.trans_type) begin
                    if (trans.addr < pending_trans[i].addr) begin
                        `uvm_warning(get_name(), "Non-modifiable transaction ordering violation")
                        ordering_errors++;
                    end
                end
            end
        end
        
        // Add to pending list
        pending_trans.push_back(trans);
        
        // Clean old transactions
        if (pending_trans.size() > 100) begin
            void'(pending_trans.pop_front());
        end
    endfunction
    
    // Check if address is in device memory region
    function bit is_device_memory(bit [63:0] addr);
        // Example: Device memory from 0x4000_0000 to 0x4FFF_FFFF
        return (addr >= 64'h4000_0000 && addr <= 64'h4FFF_FFFF);
    endfunction
    
    // Update statistics
    function void update_statistics(axi4_transaction trans);
        // Additional statistics tracking
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Cache Attribute Checker Report ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Device accesses: %0d", device_access_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Normal accesses: %0d", normal_access_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Cacheable accesses: %0d", cacheable_access_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Bufferable accesses: %0d", bufferable_access_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Allocate hints: %0d", allocate_hint_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Modifiable accesses: %0d", modifiable_access_count), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Cache attribute errors: %0d", cache_attr_errors), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Coherency errors: %0d", coherency_errors), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Ordering errors: %0d", ordering_errors), UVM_LOW)
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_cache_attribute_checker.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_ace_lite_monitor(self, output_dir: str):
        """Generate ACE-Lite protocol monitor"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// ACE-Lite Monitor
// Generated: {self.timestamp}
// Description: Monitors ACE-Lite cache maintenance operations
//------------------------------------------------------------------------------

class ace_lite_monitor extends uvm_monitor;
    
    `uvm_component_utils(ace_lite_monitor)
    
    // Virtual interface
    virtual axi4_if vif;
    
    // Analysis port
    uvm_analysis_port #(ace_lite_transaction) ap;
    
    // Configuration
    axi4_config cfg;
    
    // ACE-Lite specific signals
    typedef enum bit [3:0] {{
        READNOSNOOP     = 4'h0,
        READSHARED      = 4'h1,
        READCLEAN       = 4'h2,
        READUNIQUE      = 4'h7,
        CLEANUNIQUE     = 4'hB,
        MAKEUNIQUE      = 4'hC,
        CLEANSHARED     = 4'h8,
        CLEANINVALID    = 4'h9,
        MAKEINVALID     = 4'hD,
        WRITENOSNOOP    = 4'h0,
        WRITEUNIQUE     = 4'h0,
        WRITELINEUNIQUE = 4'h1
    }} ace_transaction_type_e;
    
    // Constructor
    function new(string name = "ace_lite_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
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
        ace_lite_transaction trans;
        
        forever begin
            // Monitor read channel for ACE-Lite transactions
            monitor_read_channel(trans);
            
            // Monitor write channel for ACE-Lite transactions  
            monitor_write_channel(trans);
        end
    endtask
    
    // Monitor read channel
    task monitor_read_channel(output ace_lite_transaction trans);
        @(posedge vif.aclk);
        
        if (vif.arvalid && vif.arready) begin
            trans = ace_lite_transaction::type_id::create("trans");
            
            // Capture transaction
            trans.addr = vif.araddr;
            trans.id = vif.arid;
            trans.len = vif.arlen;
            trans.size = vif.arsize;
            trans.cache = vif.arcache;
            trans.prot = vif.arprot;
            trans.domain = vif.ardomain;  // ACE-Lite specific
            trans.snoop = vif.arsnoop;    // ACE-Lite specific
            trans.bar = vif.arbar;        // ACE-Lite specific
            
            // Decode transaction type
            decode_read_transaction(trans);
            
            // Send to analysis port
            ap.write(trans);
            
            // Monitor response
            monitor_read_response(trans);
        end
    endtask
    
    // Monitor write channel
    task monitor_write_channel(output ace_lite_transaction trans);
        @(posedge vif.aclk);
        
        if (vif.awvalid && vif.awready) begin
            trans = ace_lite_transaction::type_id::create("trans");
            
            // Capture transaction
            trans.addr = vif.awaddr;
            trans.id = vif.awid;
            trans.len = vif.awlen;
            trans.size = vif.awsize;
            trans.cache = vif.awcache;
            trans.prot = vif.awprot;
            trans.domain = vif.awdomain;  // ACE-Lite specific
            trans.snoop = vif.awsnoop;    // ACE-Lite specific
            trans.bar = vif.awbar;        // ACE-Lite specific
            trans.unique = vif.awunique;  // ACE-Lite specific
            
            // Decode transaction type
            decode_write_transaction(trans);
            
            // Send to analysis port
            ap.write(trans);
            
            // Monitor data and response
            monitor_write_data(trans);
            monitor_write_response(trans);
        end
    endtask
    
    // Decode read transaction type
    function void decode_read_transaction(ace_lite_transaction trans);
        case (trans.snoop)
            4'h0: trans.ace_type = READNOSNOOP;
            4'h1: trans.ace_type = READSHARED;
            4'h2: trans.ace_type = READCLEAN;
            4'h7: trans.ace_type = READUNIQUE;
            4'hB: trans.ace_type = CLEANUNIQUE;
            4'hC: trans.ace_type = MAKEUNIQUE;
            default: trans.ace_type = READNOSNOOP;
        endcase
        
        // Check cache maintenance operation
        if (trans.ace_type inside {{CLEANUNIQUE, MAKEUNIQUE, CLEANSHARED, CLEANINVALID, MAKEINVALID}}) begin
            trans.is_cache_maintenance = 1;
            `uvm_info(get_name(), $sformatf("Cache maintenance operation detected: %s", trans.ace_type.name()), UVM_MEDIUM)
        end
    endfunction
    
    // Decode write transaction type
    function void decode_write_transaction(ace_lite_transaction trans);
        if (trans.unique) begin
            trans.ace_type = WRITELINEUNIQUE;
        end else begin
            case (trans.snoop)
                4'h0: trans.ace_type = WRITENOSNOOP;
                4'h1: trans.ace_type = WRITEUNIQUE;
                4'h2: trans.ace_type = WRITELINEUNIQUE;
                default: trans.ace_type = WRITENOSNOOP;
            endcase
        end
    endfunction
    
    // Monitor read response
    task monitor_read_response(ace_lite_transaction trans);
        bit done = 0;
        int beat_count = 0;
        
        while (!done) begin
            @(posedge vif.aclk);
            
            if (vif.rvalid && vif.rready && vif.rid == trans.id) begin
                trans.rresp[beat_count] = vif.rresp;
                trans.rdata[beat_count] = vif.rdata;
                
                if (vif.rlast) begin
                    done = 1;
                    trans.completion_time = $time;
                end
                
                beat_count++;
            end
        end
    endtask
    
    // Monitor write data
    task monitor_write_data(ace_lite_transaction trans);
        bit done = 0;
        int beat_count = 0;
        
        while (!done && beat_count <= trans.len) begin
            @(posedge vif.aclk);
            
            if (vif.wvalid && vif.wready) begin
                trans.wdata[beat_count] = vif.wdata;
                trans.wstrb[beat_count] = vif.wstrb;
                
                if (vif.wlast) begin
                    done = 1;
                end
                
                beat_count++;
            end
        end
    endtask
    
    // Monitor write response  
    task monitor_write_response(ace_lite_transaction trans);
        @(posedge vif.aclk);
        
        while (!(vif.bvalid && vif.bready && vif.bid == trans.id)) begin
            @(posedge vif.aclk);
        end
        
        trans.bresp = vif.bresp;
        trans.completion_time = $time;
    endtask
    
endclass

// ACE-Lite transaction class
class ace_lite_transaction extends axi4_transaction;
    
    `uvm_object_utils(ace_lite_transaction)
    
    // ACE-Lite specific fields
    bit [1:0] domain;
    bit [3:0] snoop;
    bit [1:0] bar;
    bit unique;
    ace_transaction_type_e ace_type;
    bit is_cache_maintenance;
    real completion_time;
    
    // Response data
    bit [1:0] rresp[];
    bit [127:0] rdata[];
    bit [127:0] wdata[];
    bit [15:0] wstrb[];
    
    // Constructor
    function new(string name = "ace_lite_transaction");
        super.new(name);
    endfunction
    
    // Convert to string
    function string convert2string();
        string str;
        str = super.convert2string();
        str = {{str, $sformatf("\\n  ACE Type: %s", ace_type.name())}};
        str = {{str, $sformatf("\\n  Domain: %0h, Snoop: %0h", domain, snoop)}};
        str = {{str, $sformatf("\\n  Cache Maintenance: %0b", is_cache_maintenance)}};
        return str;
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "ace_lite_monitor.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_cache_test_sequences(self, output_dir: str):
        """Generate cache coherency test sequences"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Cache Coherency Test Sequences
// Generated: {self.timestamp}
// Description: Comprehensive cache coherency test scenarios
//------------------------------------------------------------------------------

// Base cache test sequence
class cache_base_sequence extends axi4_base_test_sequence;
    
    `uvm_object_utils(cache_base_sequence)
    
    // Cache test configuration
    rand bit [3:0] awcache_value;
    rand bit [3:0] arcache_value;
    rand bit test_all_combinations;
    rand int unsigned cache_line_size = 64;
    
    // Constructor
    function new(string name = "cache_base_sequence");
        super.new(name);
    endfunction
    
    // Helper to get cache encoding
    function bit [3:0] get_cache_encoding(string cache_type);
        case (cache_type)
'''
        
        # Add cache encodings
        for name, encoding in self.cache_encodings.items():
            content += f'            "{name}": return 4\'b{encoding};\n'
            
        content += '''            default: return 4'b0011; // Normal non-cacheable bufferable
        endcase
    endfunction
    
endclass

// Write-through cache test
class write_through_cache_test extends cache_base_sequence;
    
    `uvm_object_utils(write_through_cache_test)
    
    function new(string name = "write_through_cache_test");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        bit [63:0] test_addr = 64'h1000_0000;
        
        `uvm_info(get_type_name(), "Starting write-through cache test", UVM_LOW)
        
        // Test write-through with no allocate
        repeat (10) begin
            // Write with write-through no allocate
            trans = axi4_transaction::type_id::create("trans");
            assert(trans.randomize() with {
                trans_type == AXI4_WRITE;
                addr == test_addr;
                burst_len == 0;
                burst_size == 3; // 8 bytes
                awcache == get_cache_encoding("write_through_no_allocate");
            });
            
            start_item(trans);
            finish_item(trans);
            
            // Read from same location
            trans = axi4_transaction::type_id::create("trans");
            assert(trans.randomize() with {
                trans_type == AXI4_READ;
                addr == test_addr;
                burst_len == 0;
                burst_size == 3;
                arcache == get_cache_encoding("write_through_read_allocate");
            });
            
            start_item(trans);
            finish_item(trans);
            
            test_addr += cache_line_size;
        end
    endtask
    
endclass

// Write-back cache test
class write_back_cache_test extends cache_base_sequence;
    
    `uvm_object_utils(write_back_cache_test)
    
    function new(string name = "write_back_cache_test");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        bit [63:0] test_addr = 64'h2000_0000;
        bit [127:0] write_data[$];
        bit [127:0] read_data;
        
        `uvm_info(get_type_name(), "Starting write-back cache test", UVM_LOW)
        
        // Fill cache with write-back data
        repeat (16) begin
            trans = axi4_transaction::type_id::create("trans");
            assert(trans.randomize() with {
                trans_type == AXI4_WRITE;
                addr == test_addr;
                burst_len == 7; // 8 beat burst
                burst_size == 4; // 16 bytes per beat
                awcache == get_cache_encoding("write_back_read_write_allocate");
            });
            
            // Store write data for verification
            foreach (trans.data[i]) begin
                write_data.push_back(trans.data[i]);
            end
            
            start_item(trans);
            finish_item(trans);
            
            test_addr += (8 * 16); // Next cache line set
        end
        
        // Force cache eviction by accessing different addresses
        test_addr = 64'h3000_0000;
        repeat (32) begin
            trans = axi4_transaction::type_id::create("trans");
            assert(trans.randomize() with {
                trans_type == AXI4_READ;
                addr == test_addr;
                burst_len == 7;
                burst_size == 4;
                arcache == get_cache_encoding("write_back_read_allocate");
            });
            
            start_item(trans);
            finish_item(trans);
            
            test_addr += (8 * 16);
        end
        
        // Verify original data was written back
        test_addr = 64'h2000_0000;
        repeat (16) begin
            trans = axi4_transaction::type_id::create("trans");
            assert(trans.randomize() with {
                trans_type == AXI4_READ;
                addr == test_addr;
                burst_len == 7;
                burst_size == 4;
                arcache == get_cache_encoding("normal_non_cacheable_bufferable");
            });
            
            start_item(trans);
            finish_item(trans);
            
            // Verify data matches
            foreach (trans.data[i]) begin
                read_data = trans.data[i];
                if (write_data.size() > 0) begin
                    bit [127:0] expected = write_data.pop_front();
                    if (read_data !== expected) begin
                        `uvm_error(get_type_name(), $sformatf("Data mismatch at addr %0h", test_addr + i*16))
                    end
                end
            end
            
            test_addr += (8 * 16);
        end
    endtask
    
endclass

// Cache line boundary test
class cache_line_boundary_test extends cache_base_sequence;
    
    `uvm_object_utils(cache_line_boundary_test)
    
    function new(string name = "cache_line_boundary_test");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        bit [63:0] test_addr;
        
        `uvm_info(get_type_name(), "Starting cache line boundary test", UVM_LOW)
        
        // Test accesses that cross cache line boundaries
        repeat (20) begin
            // Start near end of cache line
            test_addr = 64'h4000_0000 + (cache_line_size - 8);
            
            trans = axi4_transaction::type_id::create("trans");
            assert(trans.randomize() with {
                trans_type inside {AXI4_WRITE, AXI4_READ};
                addr == test_addr;
                burst_len == 3; // 4 beats
                burst_size == 3; // 8 bytes - will cross cache line
                awcache == get_cache_encoding("write_back_read_write_allocate");
                arcache == get_cache_encoding("write_back_read_write_allocate");
            });
            
            start_item(trans);
            finish_item(trans);
            
            // Increment to next boundary
            test_addr += cache_line_size;
        end
    endtask
    
endclass

// Cache coherency stress test
class cache_coherency_stress_test extends cache_base_sequence;
    
    `uvm_object_utils(cache_coherency_stress_test)
    
    function new(string name = "cache_coherency_stress_test");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        bit [63:0] shared_addresses[$];
        
        `uvm_info(get_type_name(), "Starting cache coherency stress test", UVM_LOW)
        
        // Create set of shared addresses
        for (int i = 0; i < 8; i++) begin
            shared_addresses.push_back(64'h5000_0000 + i * 'h1000);
        end
        
        // Generate mixed cacheable/non-cacheable accesses
        repeat (100) begin
            bit [63:0] addr;
            bit [3:0] cache_attr;
            string cache_types[$] = '{
                "device_non_bufferable",
                "normal_non_cacheable_bufferable", 
                "write_through_read_allocate",
                "write_back_read_write_allocate"
            };
            
            // Pick random shared address
            addr = shared_addresses[$urandom_range(0, shared_addresses.size()-1)];
            
            // Pick random cache type
            cache_attr = get_cache_encoding(cache_types[$urandom_range(0, cache_types.size()-1)]);
            
            trans = axi4_transaction::type_id::create("trans");
            assert(trans.randomize() with {
                trans_type inside {AXI4_WRITE, AXI4_READ};
                addr == local::addr;
                burst_len inside {[0:15]};
                burst_size inside {[0:3]};
                awcache == (trans_type == AXI4_WRITE) ? local::cache_attr : 4'b0000;
                arcache == (trans_type == AXI4_READ) ? local::cache_attr : 4'b0000;
            });
            
            start_item(trans);
            finish_item(trans);
            
            #($urandom_range(1, 10) * 1ns);
        end
    endtask
    
endclass

// Memory barrier test
class memory_barrier_test extends cache_base_sequence;
    
    `uvm_object_utils(memory_barrier_test)
    
    function new(string name = "memory_barrier_test");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        `uvm_info(get_type_name(), "Starting memory barrier test", UVM_LOW)
        
        // Issue writes to different memory types
        for (int i = 0; i < 10; i++) begin
            // Device write (must complete before barrier)
            trans = axi4_transaction::type_id::create("trans");
            assert(trans.randomize() with {
                trans_type == AXI4_WRITE;
                addr == 64'h4000_0000 + i * 'h100; // Device region
                burst_len == 0;
                awcache == get_cache_encoding("device_bufferable");
            });
            
            start_item(trans);
            finish_item(trans);
            
            // Normal cacheable write
            trans = axi4_transaction::type_id::create("trans");
            assert(trans.randomize() with {
                trans_type == AXI4_WRITE;
                addr == 64'h8000_0000 + i * 'h100; // Normal region
                burst_len == 0;
                awcache == get_cache_encoding("write_back_read_write_allocate");
            });
            
            start_item(trans);
            finish_item(trans);
            
            // Issue memory barrier (implementation specific)
            issue_memory_barrier();
            
            // Verify ordering with reads
            trans = axi4_transaction::type_id::create("trans");
            assert(trans.randomize() with {
                trans_type == AXI4_READ;
                addr == 64'h4000_0000 + i * 'h100;
                burst_len == 0;
                arcache == get_cache_encoding("device_non_bufferable");
            });
            
            start_item(trans);
            finish_item(trans);
        end
    endtask
    
    // Issue memory barrier
    task issue_memory_barrier();
        // Implementation specific - could be:
        // 1. Special transaction type
        // 2. Write to specific address
        // 3. Use of AxBAR signals in ACE
        #10ns; // Placeholder delay
    endtask
    
endclass
'''
        
        filepath = os.path.join(output_dir, "cache_coherency_test_sequences.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_coherency_scoreboard(self, output_dir: str):
        """Generate cache coherency scoreboard"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Cache Coherency Scoreboard
// Generated: {self.timestamp}
// Description: Tracks and verifies cache coherency across masters
//------------------------------------------------------------------------------

class cache_coherency_scoreboard extends uvm_scoreboard;
    
    `uvm_component_utils(cache_coherency_scoreboard)
    
    // Analysis imports
    uvm_analysis_imp_decl(_master)
    uvm_analysis_imp_decl(_monitor)
    
    uvm_analysis_imp_master #(axi4_transaction, cache_coherency_scoreboard) master_export;
    uvm_analysis_imp_monitor #(axi4_transaction, cache_coherency_scoreboard) monitor_export;
    
    // Memory model with cache state tracking
    typedef enum bit [1:0] {
        INVALID   = 2'b00,
        SHARED    = 2'b01,
        EXCLUSIVE = 2'b10,
        MODIFIED  = 2'b11
    } cache_state_e;
    
    typedef struct {
        bit [127:0] data;
        cache_state_e state;
        bit [7:0] owner_id;
        bit dirty;
        time last_access;
    } cache_line_t;
    
    // Cache state for each master
    cache_line_t master_caches[int][bit[63:0]]; // [master_id][address]
    
    // Main memory
    bit [7:0] main_memory[bit[63:0]];
    
    // Statistics
    int unsigned coherency_violations;
    int unsigned cache_hits;
    int unsigned cache_misses;
    int unsigned writebacks;
    int unsigned invalidations;
    
    // Constructor
    function new(string name = "cache_coherency_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        master_export = new("master_export", this);
        monitor_export = new("monitor_export", this);
    endfunction
    
    // Master write function
    function void write_master(axi4_transaction trans);
        process_master_transaction(trans);
    endfunction
    
    // Monitor write function  
    function void write_monitor(axi4_transaction trans);
        check_coherency_protocol(trans);
    endfunction
    
    // Process master transaction
    function void process_master_transaction(axi4_transaction trans);
        bit [63:0] addr = trans.addr & ~(64'h3F); // Cache line aligned
        int master_id = trans.id[7:4]; // Upper bits as master ID
        bit [3:0] cache_attr;
        
        cache_attr = (trans.trans_type == AXI4_WRITE) ? trans.awcache : trans.arcache;
        
        // Check if cacheable
        if (!is_cacheable(cache_attr)) begin
            // Direct memory access
            if (trans.trans_type == AXI4_WRITE) begin
                write_memory(trans);
            end else begin
                read_memory(trans);
            end
            return;
        end
        
        // Cache access
        if (trans.trans_type == AXI4_WRITE) begin
            handle_cache_write(master_id, addr, trans);
        end else begin
            handle_cache_read(master_id, addr, trans);
        end
    endfunction
    
    // Handle cache write
    function void handle_cache_write(int master_id, bit [63:0] addr, axi4_transaction trans);
        cache_line_t line;
        
        // Check current state
        if (master_caches[master_id].exists(addr)) begin
            line = master_caches[master_id][addr];
            
            case (line.state)
                EXCLUSIVE, MODIFIED: begin
                    // Can write directly
                    line.data = trans.data[0]; // Simplified
                    line.state = MODIFIED;
                    line.dirty = 1;
                    master_caches[master_id][addr] = line;
                    cache_hits++;
                end
                
                SHARED: begin
                    // Need to invalidate other copies
                    invalidate_other_caches(master_id, addr);
                    line.data = trans.data[0];
                    line.state = MODIFIED;
                    line.dirty = 1;
                    master_caches[master_id][addr] = line;
                    invalidations++;
                end
                
                INVALID: begin
                    // Cache miss - fetch and modify
                    cache_misses++;
                    fetch_cache_line(master_id, addr);
                    line = master_caches[master_id][addr];
                    line.data = trans.data[0];
                    line.state = MODIFIED;
                    line.dirty = 1;
                    master_caches[master_id][addr] = line;
                end
            endcase
        end else begin
            // Cache miss
            cache_misses++;
            fetch_cache_line(master_id, addr);
            line = master_caches[master_id][addr];
            line.data = trans.data[0];
            line.state = MODIFIED;
            line.dirty = 1;
            master_caches[master_id][addr] = line;
        end
        
        line.last_access = $time;
    endfunction
    
    // Handle cache read
    function void handle_cache_read(int master_id, bit [63:0] addr, axi4_transaction trans);
        cache_line_t line;
        bit other_has_modified = 0;
        
        // Check if other cache has modified copy
        foreach (master_caches[i]) begin
            if (i != master_id && master_caches[i].exists(addr)) begin
                if (master_caches[i][addr].state == MODIFIED) begin
                    other_has_modified = 1;
                    // Write back to memory
                    writeback_cache_line(i, addr);
                    master_caches[i][addr].state = SHARED;
                    master_caches[i][addr].dirty = 0;
                    writebacks++;
                    break;
                end
            end
        end
        
        // Check current cache
        if (master_caches[master_id].exists(addr)) begin
            line = master_caches[master_id][addr];
            if (line.state != INVALID) begin
                cache_hits++;
                trans.data[0] = line.data;
                
                // Update state if needed
                if (line.state == EXCLUSIVE) begin
                    line.state = SHARED;
                    master_caches[master_id][addr] = line;
                end
            end else begin
                cache_misses++;
                fetch_cache_line(master_id, addr);
            end
        end else begin
            cache_misses++;
            fetch_cache_line(master_id, addr);
        end
    endfunction
    
    // Invalidate other caches
    function void invalidate_other_caches(int master_id, bit [63:0] addr);
        foreach (master_caches[i]) begin
            if (i != master_id && master_caches[i].exists(addr)) begin
                master_caches[i][addr].state = INVALID;
            end
        end
    endfunction
    
    // Fetch cache line from memory
    function void fetch_cache_line(int master_id, bit [63:0] addr);
        cache_line_t line;
        
        line.data = read_memory_line(addr);
        line.state = EXCLUSIVE; // Assuming no other cache has it
        line.owner_id = master_id;
        line.dirty = 0;
        line.last_access = $time;
        
        master_caches[master_id][addr] = line;
    endfunction
    
    // Write back cache line to memory
    function void writeback_cache_line(int master_id, bit [63:0] addr);
        cache_line_t line = master_caches[master_id][addr];
        write_memory_line(addr, line.data);
    endfunction
    
    // Check if transaction is cacheable
    function bit is_cacheable(bit [3:0] cache_attr);
        return cache_attr[1]; // Modifiable bit indicates cacheable
    endfunction
    
    // Memory access functions
    function void write_memory(axi4_transaction trans);
        foreach (trans.data[i]) begin
            bit [63:0] byte_addr = trans.addr + i * (1 << trans.burst_size);
            for (int j = 0; j < (1 << trans.burst_size); j++) begin
                main_memory[byte_addr + j] = trans.data[i][j*8 +: 8];
            end
        end
    endfunction
    
    function void read_memory(axi4_transaction trans);
        foreach (trans.data[i]) begin
            bit [63:0] byte_addr = trans.addr + i * (1 << trans.burst_size);
            for (int j = 0; j < (1 << trans.burst_size); j++) begin
                trans.data[i][j*8 +: 8] = main_memory[byte_addr + j];
            end
        end
    endfunction
    
    function bit [127:0] read_memory_line(bit [63:0] addr);
        bit [127:0] data;
        for (int i = 0; i < 64; i++) begin
            data[i*8 +: 8] = main_memory[addr + i];
        end
        return data;
    endfunction
    
    function void write_memory_line(bit [63:0] addr, bit [127:0] data);
        for (int i = 0; i < 64; i++) begin
            main_memory[addr + i] = data[i*8 +: 8];
        end
    endfunction
    
    // Check coherency protocol compliance
    function void check_coherency_protocol(axi4_transaction trans);
        // Additional coherency checks
        // This would contain protocol-specific checks
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Cache Coherency Scoreboard Report ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Cache hits: %0d", cache_hits), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Cache misses: %0d", cache_misses), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Writebacks: %0d", writebacks), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Invalidations: %0d", invalidations), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Coherency violations: %0d", coherency_violations), UVM_LOW)
        
        if (coherency_violations > 0) begin
            `uvm_error(get_name(), $sformatf("Found %0d coherency violations!", coherency_violations))
        end
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "cache_coherency_scoreboard.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_cache_state_machine(self, output_dir: str):
        """Generate cache state machine model"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Cache State Machine Model
// Generated: {self.timestamp}
// Description: Models MESI cache coherency protocol state transitions
//------------------------------------------------------------------------------

class cache_state_machine extends uvm_object;
    
    `uvm_object_utils(cache_state_machine)
    
    // MESI states
    typedef enum bit [1:0] {
        MODIFIED   = 2'b00,  // M - Modified, exclusive, dirty
        EXCLUSIVE  = 2'b01,  // E - Exclusive, clean
        SHARED     = 2'b10,  // S - Shared, clean
        INVALID    = 2'b11   // I - Invalid
    } mesi_state_e;
    
    // Cache events
    typedef enum bit [3:0] {
        PROC_READ_HIT      = 4'b0000,
        PROC_READ_MISS     = 4'b0001,
        PROC_WRITE_HIT     = 4'b0010,
        PROC_WRITE_MISS    = 4'b0011,
        BUS_READ           = 4'b0100,
        BUS_WRITE          = 4'b0101,
        BUS_UPGRADE        = 4'b0110,
        EVICTION           = 4'b0111,
        INVALIDATE         = 4'b1000,
        INTERVENTION       = 4'b1001
    } cache_event_e;
    
    // Current state
    mesi_state_e current_state;
    
    // Statistics
    int state_transitions[mesi_state_e][mesi_state_e];
    int event_count[cache_event_e];
    
    // Constructor
    function new(string name = "cache_state_machine");
        super.new(name);
        current_state = INVALID;
    endfunction
    
    // Process event and return new state
    function mesi_state_e process_event(cache_event_e event, bit is_shared = 0);
        mesi_state_e next_state;
        
        case (current_state)
            INVALID: begin
                case (event)
                    PROC_READ_MISS: next_state = is_shared ? SHARED : EXCLUSIVE;
                    PROC_WRITE_MISS: next_state = MODIFIED;
                    default: next_state = INVALID;
                endcase
            end
            
            SHARED: begin
                case (event)
                    PROC_READ_HIT: next_state = SHARED;
                    PROC_WRITE_HIT: next_state = MODIFIED;
                    BUS_WRITE: next_state = INVALID;
                    BUS_UPGRADE: next_state = INVALID;
                    EVICTION: next_state = INVALID;
                    INVALIDATE: next_state = INVALID;
                    default: next_state = SHARED;
                endcase
            end
            
            EXCLUSIVE: begin
                case (event)
                    PROC_READ_HIT: next_state = EXCLUSIVE;
                    PROC_WRITE_HIT: next_state = MODIFIED;
                    BUS_READ: next_state = SHARED;
                    BUS_WRITE: next_state = INVALID;
                    EVICTION: next_state = INVALID;
                    INVALIDATE: next_state = INVALID;
                    default: next_state = EXCLUSIVE;
                endcase
            end
            
            MODIFIED: begin
                case (event)
                    PROC_READ_HIT: next_state = MODIFIED;
                    PROC_WRITE_HIT: next_state = MODIFIED;
                    BUS_READ: next_state = SHARED; // Write back
                    BUS_WRITE: next_state = INVALID; // Write back
                    EVICTION: next_state = INVALID; // Write back
                    INVALIDATE: next_state = INVALID; // Write back
                    INTERVENTION: next_state = SHARED; // Intervene
                    default: next_state = MODIFIED;
                endcase
            end
        endcase
        
        // Update statistics
        state_transitions[current_state][next_state]++;
        event_count[event]++;
        
        // Update current state
        current_state = next_state;
        
        return next_state;
    endfunction
    
    // Get actions required for transition
    function string get_transition_actions(mesi_state_e from_state, mesi_state_e to_state, cache_event_e event);
        string actions = "";
        
        // Determine required bus actions
        if (from_state == MODIFIED) begin
            if (to_state inside {SHARED, INVALID}) begin
                actions = {actions, "WRITE_BACK "};
            end
        end
        
        if (event == PROC_WRITE_HIT && from_state == SHARED) begin
            actions = {actions, "BUS_UPGRADE "};
        end
        
        if (event inside {PROC_READ_MISS, PROC_WRITE_MISS}) begin
            if (to_state == EXCLUSIVE || to_state == MODIFIED) begin
                actions = {actions, "BUS_READ_EXCLUSIVE "};
            end else begin
                actions = {actions, "BUS_READ_SHARED "};
            end
        end
        
        return actions;
    endfunction
    
    // Check if state transition is valid
    function bit is_valid_transition(mesi_state_e from_state, mesi_state_e to_state, cache_event_e event);
        mesi_state_e old_state = current_state;
        mesi_state_e expected_state;
        
        current_state = from_state;
        expected_state = process_event(event);
        current_state = old_state;
        
        return (expected_state == to_state);
    endfunction
    
    // Get current state string
    function string get_state_string();
        return current_state.name();
    endfunction
    
    // Reset state machine
    function void reset();
        current_state = INVALID;
        foreach (state_transitions[i,j]) begin
            state_transitions[i][j] = 0;
        end
        foreach (event_count[i]) begin
            event_count[i] = 0;
        end
    endfunction
    
    // Print statistics
    function void print_statistics();
        $display("=== Cache State Machine Statistics ===");
        $display("Current State: %s", current_state.name());
        
        $display("\\nState Transitions:");
        foreach (state_transitions[i,j]) begin
            if (state_transitions[i][j] > 0) begin
                $display("  %s -> %s: %0d", i.name(), j.name(), state_transitions[i][j]);
            end
        end
        
        $display("\\nEvent Counts:");
        foreach (event_count[i]) begin
            if (event_count[i] > 0) begin
                $display("  %s: %0d", i.name(), event_count[i]);
            end
        end
    endfunction
    
endclass

// Extended state machine for ACE protocol
class ace_cache_state_machine extends cache_state_machine;
    
    `uvm_object_utils(ace_cache_state_machine)
    
    // Additional ACE states
    typedef enum bit [2:0] {
        UNIQUE_CLEAN = 3'b000,
        UNIQUE_DIRTY = 3'b001,
        SHARED_CLEAN = 3'b010,
        SHARED_DIRTY = 3'b011,
        INVALID_ACE  = 3'b100
    } ace_state_e;
    
    // ACE specific events
    typedef enum bit [3:0] {
        CLEAN_UNIQUE    = 4'b0000,
        CLEAN_SHARED    = 4'b0001,
        CLEAN_INVALID   = 4'b0010,
        MAKE_UNIQUE     = 4'b0011,
        MAKE_INVALID    = 4'b0100,
        READ_UNIQUE     = 4'b0101,
        WRITE_UNIQUE    = 4'b0110,
        WRITE_LINE_UNIQUE = 4'b0111,
        EVICT_CLEAN     = 4'b1000,
        EVICT_DIRTY     = 4'b1001
    } ace_event_e;
    
    // Current ACE state
    ace_state_e ace_current_state;
    
    // Constructor
    function new(string name = "ace_cache_state_machine");
        super.new(name);
        ace_current_state = INVALID_ACE;
    endfunction
    
    // Process ACE event
    function ace_state_e process_ace_event(ace_event_e event);
        ace_state_e next_state;
        
        case (ace_current_state)
            INVALID_ACE: begin
                case (event)
                    READ_UNIQUE: next_state = UNIQUE_CLEAN;
                    WRITE_UNIQUE, WRITE_LINE_UNIQUE: next_state = UNIQUE_DIRTY;
                    default: next_state = INVALID_ACE;
                endcase
            end
            
            UNIQUE_CLEAN: begin
                case (event)
                    WRITE_UNIQUE: next_state = UNIQUE_DIRTY;
                    CLEAN_SHARED: next_state = SHARED_CLEAN;
                    CLEAN_INVALID, MAKE_INVALID: next_state = INVALID_ACE;
                    EVICT_CLEAN: next_state = INVALID_ACE;
                    default: next_state = UNIQUE_CLEAN;
                endcase
            end
            
            UNIQUE_DIRTY: begin
                case (event)
                    CLEAN_SHARED: next_state = SHARED_DIRTY;
                    CLEAN_INVALID, MAKE_INVALID: next_state = INVALID_ACE;
                    EVICT_DIRTY: next_state = INVALID_ACE;
                    default: next_state = UNIQUE_DIRTY;
                endcase
            end
            
            SHARED_CLEAN: begin
                case (event)
                    MAKE_UNIQUE: next_state = UNIQUE_CLEAN;
                    WRITE_UNIQUE: next_state = UNIQUE_DIRTY;
                    CLEAN_INVALID, MAKE_INVALID: next_state = INVALID_ACE;
                    EVICT_CLEAN: next_state = INVALID_ACE;
                    default: next_state = SHARED_CLEAN;
                endcase
            end
            
            SHARED_DIRTY: begin
                case (event)
                    MAKE_UNIQUE: next_state = UNIQUE_DIRTY;
                    CLEAN_INVALID, MAKE_INVALID: next_state = INVALID_ACE;
                    EVICT_DIRTY: next_state = INVALID_ACE;
                    default: next_state = SHARED_DIRTY;
                endcase
            end
        endcase
        
        ace_current_state = next_state;
        return next_state;
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "cache_state_machine.sv")
        with open(filepath, 'w') as f:
            f.write(content)

def example_cache_coherency_generation():
    """Example of generating cache coherency tests"""
    
    config = {
        'num_masters': 4,
        'num_slaves': 4,
        'data_width': 128,
        'addr_width': 64,
        'support_ace_lite': True
    }
    
    generator = VIPCacheCoherencyTestGenerator(config)
    output_dir = "vip_output/cache_tests"
    os.makedirs(output_dir, exist_ok=True)
    
    print("Generating cache coherency test components...")
    generator.generate_cache_coherency_tests(output_dir)
    print("Cache coherency test generation complete!")

if __name__ == "__main__":
    example_cache_coherency_generation()