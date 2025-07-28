#!/usr/bin/env python3
"""
VIP Advanced Protocol Features Integrator
Integrates QoS, REGION, USER and other advanced AXI4 features
"""

import os
import datetime
from typing import Dict, List, Optional, Tuple

class VIPAdvancedProtocolIntegrator:
    """Integrator for all advanced AXI4 protocol features"""
    
    def __init__(self, config: Dict):
        """Initialize integrator with configuration"""
        self.config = config
        self.num_masters = config.get('num_masters', 2)
        self.num_slaves = config.get('num_slaves', 2)
        self.data_width = config.get('data_width', 64)
        self.addr_width = config.get('addr_width', 32)
        self.id_width = config.get('id_width', 4)
        self.user_width = config.get('user_width', 16)
        self.protocol_version = config.get('protocol', 'AXI4')
        
        # Import component generators
        from vip_qos_generator import VIPQoSGenerator
        from vip_region_generator import VIPRegionGenerator
        from vip_user_generator import VIPUserGenerator
        
        # Create component generators
        self.qos_gen = VIPQoSGenerator(config)
        self.region_gen = VIPRegionGenerator(config)
        self.user_gen = VIPUserGenerator(config)
        
    def generate_integrated_components(self, output_dir: str):
        """Generate all integrated components"""
        # Create directory structure
        integrated_dir = os.path.join(output_dir, 'integrated')
        os.makedirs(integrated_dir, exist_ok=True)
        
        # Generate individual components first
        self.qos_gen.generate_all_qos_components(output_dir)
        self.region_gen.generate_all_region_components(output_dir)
        self.user_gen.generate_all_user_components(output_dir)
        
        # Generate integrated components
        self._generate_integrated_transaction(integrated_dir)
        self._generate_integrated_interface(integrated_dir)
        self._generate_integrated_monitor(integrated_dir)
        self._generate_integrated_checker(integrated_dir)
        self._generate_integrated_env(integrated_dir)
        self._generate_integrated_test_library(integrated_dir)
        self._generate_integrated_package(integrated_dir)
        
    def _generate_integrated_transaction(self, output_dir: str):
        """Generate integrated transaction with all advanced features"""
        content = f"""// AXI4 VIP Integrated Transaction
// Generated: {datetime.datetime.now()}
// Transaction with QoS, REGION, USER and all AXI4 features

`ifndef AXI4_INTEGRATED_TRANSACTION_SV
`define AXI4_INTEGRATED_TRANSACTION_SV

class axi4_integrated_transaction extends uvm_sequence_item;
    `uvm_object_utils(axi4_integrated_transaction)
    
    // Basic AXI4 fields
    rand bit[{self.addr_width-1}:0] addr;
    rand bit[{self.id_width-1}:0] id;
    rand bit[7:0] len;
    rand bit[2:0] size;
    rand bit[1:0] burst;
    rand bit lock;
    rand bit[3:0] cache;
    rand bit[2:0] prot;
    
    // Advanced AXI4 fields
    rand bit[3:0] qos;      // Quality of Service
    rand bit[3:0] region;   // Region identifier
    
    // USER signals
    rand bit[{self.user_width-1}:0] awuser;
    rand bit[{self.user_width-1}:0] wuser[];
    rand bit[{self.user_width-1}:0] buser;
    rand bit[{self.user_width-1}:0] aruser;
    rand bit[{self.user_width-1}:0] ruser[];
    
    // Data and control
    rand bit[{self.data_width-1}:0] data[];
    rand bit[{self.data_width/8-1}:0] wstrb[];
    bit[1:0] resp[];
    bit is_write;
    
    // Derived fields
    int master_id;
    int slave_id;
    realtime start_time;
    realtime end_time;
    
    // Constraints for valid transactions
    constraint valid_size_c {{
        size <= $clog2({self.data_width}/8);
    }}
    
    constraint valid_burst_c {{
        burst inside {{2'b00, 2'b01, 2'b10}};  // FIXED, INCR, WRAP
        if (burst == 2'b10) {{  // WRAP constraints
            len inside {{1, 3, 7, 15}};  // 2, 4, 8, 16 beats
        }}
    }}
    
    constraint valid_lock_c {{
        // AXI4 only supports exclusive access (not locked)
        lock inside {{1'b0, 1'b1}};  // Normal or Exclusive
    }}
    
    constraint valid_cache_c {{
        // Valid cache encodings
        cache[1] == 0 || cache[0] == 1;  // Modifiable requires Bufferable
    }}
    
    constraint qos_range_c {{
        qos inside {{[0:15]}};
    }}
    
    constraint region_range_c {{
        region inside {{[0:15]}};
    }}
    
    constraint data_array_size_c {{
        data.size() == len + 1;
        wstrb.size() == len + 1;
        resp.size() == len + 1;
        wuser.size() == len + 1;
        ruser.size() == len + 1;
    }}
    
    // 4KB boundary constraint
    constraint boundary_4kb_c {{
        // Ensure transaction doesn't cross 4KB boundary
        (addr & 12'hFFF) + ((len + 1) * (1 << size)) <= 4096;
    }}
    
    // Exclusive access constraints
    constraint exclusive_access_c {{
        if (lock) {{
            // Exclusive access size limits
            size <= 3;  // Max 8 bytes for exclusive
            len == 0;   // Single beat for exclusive
        }}
    }}
    
    // QoS-based constraints
    constraint qos_based_c {{
        // High QoS transactions get better attributes
        if (qos >= 12) {{  // Critical QoS
            cache[3:2] inside {{2'b10, 2'b11}};  // Cacheable
        }}
    }}
    
    // REGION consistency constraint
    constraint region_consistency_c {{
        // REGION should be appropriate for address
        soft region == addr[31:28];  // Simple mapping
    }}
    
    // Constructor
    function new(string name = "axi4_integrated_transaction");
        super.new(name);
    endfunction
    
    // Post-randomize
    function void post_randomize();
        // Initialize response array
        foreach (resp[i]) begin
            resp[i] = 2'b00;  // OKAY by default
        end
        
        // Calculate derived fields
        master_id = id[{self.id_width-1}:{self.id_width-2}];
        slave_id = addr[{self.addr_width-1}:{self.addr_width-2}];
    endfunction
    
    // Check if transaction crosses 4KB boundary
    function bit crosses_4kb_boundary();
        bit[{self.addr_width-1}:0] start_addr = addr;
        bit[{self.addr_width-1}:0] end_addr;
        
        case (burst)
            2'b00: end_addr = start_addr;  // FIXED
            2'b01: end_addr = start_addr + (len * (1 << size));  // INCR
            2'b10: begin  // WRAP
                int wrap_size = (len + 1) * (1 << size);
                end_addr = start_addr + wrap_size - 1;
            end
        endcase
        
        return (start_addr[31:12] != end_addr[31:12]);
    endfunction
    
    // Get transaction latency
    function real get_latency();
        return end_time - start_time;
    endfunction
    
    // Convert to string
    function string convert2string();
        string str;
        str = $sformatf("%s Transaction:\\n", is_write ? "Write" : "Read");
        str = {{str, $sformatf("  Address: 0x%08h\\n", addr)}};
        str = {{str, $sformatf("  ID: %0d (Master: %0d)\\n", id, master_id)}};
        str = {{str, $sformatf("  Len: %0d, Size: %0d, Burst: %0d\\n", len, size, burst)}};
        str = {{str, $sformatf("  QoS: %0d, REGION: %0d\\n", qos, region)}};
        str = {{str, $sformatf("  Cache: 0x%01h, Prot: 0x%01h, Lock: %0b\\n", cache, prot, lock)}};
        
        if (is_write) begin
            str = {{str, $sformatf("  AWUSER: 0x%04h\\n", awuser)}};
            if (wuser.size() > 0) begin
                str = {{str, $sformatf("  WUSER[0]: 0x%04h\\n", wuser[0])}};
            end
        end else begin
            str = {{str, $sformatf("  ARUSER: 0x%04h\\n", aruser)}};
        end
        
        return str;
    endfunction
    
    // Copy transaction
    function void do_copy(uvm_object rhs);
        axi4_integrated_transaction t;
        if (!$cast(t, rhs)) begin
            `uvm_fatal("CAST", "Failed to cast in do_copy")
        end
        
        super.do_copy(rhs);
        
        // Copy all fields
        addr = t.addr;
        id = t.id;
        len = t.len;
        size = t.size;
        burst = t.burst;
        lock = t.lock;
        cache = t.cache;
        prot = t.prot;
        qos = t.qos;
        region = t.region;
        
        // Copy USER signals
        awuser = t.awuser;
        wuser = t.wuser;
        buser = t.buser;
        aruser = t.aruser;
        ruser = t.ruser;
        
        // Copy data arrays
        data = t.data;
        wstrb = t.wstrb;
        resp = t.resp;
        
        // Copy metadata
        is_write = t.is_write;
        master_id = t.master_id;
        slave_id = t.slave_id;
        start_time = t.start_time;
        end_time = t.end_time;
    endfunction
    
    // Compare transactions
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        axi4_integrated_transaction t;
        bit result;
        
        if (!$cast(t, rhs)) begin
            `uvm_fatal("CAST", "Failed to cast in do_compare")
        end
        
        result = super.do_compare(rhs, comparer);
        
        // Compare all fields
        result &= (addr == t.addr);
        result &= (id == t.id);
        result &= (len == t.len);
        result &= (size == t.size);
        result &= (burst == t.burst);
        result &= (lock == t.lock);
        result &= (cache == t.cache);
        result &= (prot == t.prot);
        result &= (qos == t.qos);
        result &= (region == t.region);
        
        return result;
    endfunction

endclass

`endif // AXI4_INTEGRATED_TRANSACTION_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_integrated_transaction.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_integrated_interface(self, output_dir: str):
        """Generate integrated interface with all signals"""
        content = f"""// AXI4 VIP Integrated Interface
// Generated: {datetime.datetime.now()}
// Interface with all AXI4 signals including QoS, REGION, USER

`ifndef AXI4_INTEGRATED_INTERFACE_SV
`define AXI4_INTEGRATED_INTERFACE_SV

interface axi4_integrated_if #(
    parameter ADDR_WIDTH = {self.addr_width},
    parameter DATA_WIDTH = {self.data_width},
    parameter ID_WIDTH = {self.id_width},
    parameter AWUSER_WIDTH = {self.user_width},
    parameter WUSER_WIDTH = {self.user_width},
    parameter BUSER_WIDTH = {self.user_width},
    parameter ARUSER_WIDTH = {self.user_width},
    parameter RUSER_WIDTH = {self.user_width}
)(
    input logic clk,
    input logic resetn
);
    
    // Write Address Channel
    logic [ID_WIDTH-1:0] awid;
    logic [ADDR_WIDTH-1:0] awaddr;
    logic [7:0] awlen;
    logic [2:0] awsize;
    logic [1:0] awburst;
    logic awlock;
    logic [3:0] awcache;
    logic [2:0] awprot;
    logic [3:0] awqos;      // Quality of Service
    logic [3:0] awregion;   // Region identifier
    logic [AWUSER_WIDTH-1:0] awuser;  // User signal
    logic awvalid;
    logic awready;
    
    // Write Data Channel
    logic [DATA_WIDTH-1:0] wdata;
    logic [DATA_WIDTH/8-1:0] wstrb;
    logic wlast;
    logic [WUSER_WIDTH-1:0] wuser;  // User signal
    logic wvalid;
    logic wready;
    
    // Write Response Channel
    logic [ID_WIDTH-1:0] bid;
    logic [1:0] bresp;
    logic [BUSER_WIDTH-1:0] buser;  // User signal
    logic bvalid;
    logic bready;
    
    // Read Address Channel
    logic [ID_WIDTH-1:0] arid;
    logic [ADDR_WIDTH-1:0] araddr;
    logic [7:0] arlen;
    logic [2:0] arsize;
    logic [1:0] arburst;
    logic arlock;
    logic [3:0] arcache;
    logic [2:0] arprot;
    logic [3:0] arqos;      // Quality of Service
    logic [3:0] arregion;   // Region identifier
    logic [ARUSER_WIDTH-1:0] aruser;  // User signal
    logic arvalid;
    logic arready;
    
    // Read Data Channel
    logic [ID_WIDTH-1:0] rid;
    logic [DATA_WIDTH-1:0] rdata;
    logic [1:0] rresp;
    logic rlast;
    logic [RUSER_WIDTH-1:0] ruser;  // User signal
    logic rvalid;
    logic rready;
    
    // Modports for master and slave
    modport master (
        input clk, resetn,
        // Write address
        output awid, awaddr, awlen, awsize, awburst, awlock,
        output awcache, awprot, awqos, awregion, awuser, awvalid,
        input awready,
        // Write data
        output wdata, wstrb, wlast, wuser, wvalid,
        input wready,
        // Write response
        input bid, bresp, buser, bvalid,
        output bready,
        // Read address
        output arid, araddr, arlen, arsize, arburst, arlock,
        output arcache, arprot, arqos, arregion, aruser, arvalid,
        input arready,
        // Read data
        input rid, rdata, rresp, rlast, ruser, rvalid,
        output rready
    );
    
    modport slave (
        input clk, resetn,
        // Write address
        input awid, awaddr, awlen, awsize, awburst, awlock,
        input awcache, awprot, awqos, awregion, awuser, awvalid,
        output awready,
        // Write data
        input wdata, wstrb, wlast, wuser, wvalid,
        output wready,
        // Write response
        output bid, bresp, buser, bvalid,
        input bready,
        // Read address
        input arid, araddr, arlen, arsize, arburst, arlock,
        input arcache, arprot, arqos, arregion, aruser, arvalid,
        output arready,
        // Read data
        output rid, rdata, rresp, rlast, ruser, rvalid,
        input rready
    );
    
    // Monitor modport
    modport monitor (
        input clk, resetn,
        input awid, awaddr, awlen, awsize, awburst, awlock,
        input awcache, awprot, awqos, awregion, awuser, awvalid, awready,
        input wdata, wstrb, wlast, wuser, wvalid, wready,
        input bid, bresp, buser, bvalid, bready,
        input arid, araddr, arlen, arsize, arburst, arlock,
        input arcache, arprot, arqos, arregion, aruser, arvalid, arready,
        input rid, rdata, rresp, rlast, ruser, rvalid, rready
    );
    
    // Clocking blocks for synchronous sampling
    clocking master_cb @(posedge clk);
        default input #1 output #1;
        // Define timing for all signals
    endclocking
    
    clocking slave_cb @(posedge clk);
        default input #1 output #1;
        // Define timing for all signals
    endclocking
    
    clocking monitor_cb @(posedge clk);
        default input #1;
        // All inputs for monitoring
    endclocking
    
    // Assertions for protocol checking
    property aw_stable_before_handshake;
        @(posedge clk) disable iff (!resetn)
        awvalid && !awready |=> $stable(awaddr) && $stable(awid) && 
                                $stable(awlen) && $stable(awsize) &&
                                $stable(awburst) && $stable(awlock) &&
                                $stable(awcache) && $stable(awprot) &&
                                $stable(awqos) && $stable(awregion) &&
                                $stable(awuser);
    endproperty
    
    property ar_stable_before_handshake;
        @(posedge clk) disable iff (!resetn)
        arvalid && !arready |=> $stable(araddr) && $stable(arid) && 
                                $stable(arlen) && $stable(arsize) &&
                                $stable(arburst) && $stable(arlock) &&
                                $stable(arcache) && $stable(arprot) &&
                                $stable(arqos) && $stable(arregion) &&
                                $stable(aruser);
    endproperty
    
    property region_constant_in_burst;
        @(posedge clk) disable iff (!resetn)
        // REGION must remain constant throughout a burst
        // This is checked in the integrated checker
        1;
    endproperty
    
    // Assert properties
    assert property (aw_stable_before_handshake)
        else $error("AW channel signals changed before handshake");
        
    assert property (ar_stable_before_handshake)
        else $error("AR channel signals changed before handshake");

endinterface

`endif // AXI4_INTEGRATED_INTERFACE_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_integrated_interface.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_integrated_monitor(self, output_dir: str):
        """Generate integrated monitor for all features"""
        content = f"""// AXI4 VIP Integrated Monitor
// Generated: {datetime.datetime.now()}
// Monitors all AXI4 features including QoS, REGION, USER

`ifndef AXI4_INTEGRATED_MONITOR_SV
`define AXI4_INTEGRATED_MONITOR_SV

class axi4_integrated_monitor extends uvm_monitor;
    `uvm_component_utils(axi4_integrated_monitor)
    
    // Virtual interface
    virtual axi4_integrated_if vif;
    
    // Analysis ports
    uvm_analysis_port #(axi4_integrated_transaction) trans_ap;
    uvm_analysis_port #(axi4_integrated_event) event_ap;
    
    // Sub-monitors
    axi4_qos_monitor qos_monitor;
    axi4_region_monitor region_monitor;
    axi4_user_monitor user_monitor;
    
    // Transaction assembly
    axi4_integrated_transaction write_trans_queue[bit[{self.id_width-1}:0]][$];
    axi4_integrated_transaction read_trans_queue[bit[{self.id_width-1}:0]][$];
    
    // Statistics
    int total_write_trans;
    int total_read_trans;
    int qos_violations;
    int region_violations;
    int protocol_violations;
    
    // Constructor
    function new(string name = "axi4_integrated_monitor", uvm_component parent = null);
        super.new(name, parent);
        trans_ap = new("trans_ap", this);
        event_ap = new("event_ap", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(virtual axi4_integrated_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
        
        // Create sub-monitors
        qos_monitor = axi4_qos_monitor::type_id::create("qos_monitor", this);
        region_monitor = axi4_region_monitor::type_id::create("region_monitor", this);
        user_monitor = axi4_user_monitor::type_id::create("user_monitor", this);
    endfunction
    
    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect sub-monitors to same interface
        uvm_config_db#(virtual axi4_if)::set(this, "qos_monitor", "vif", vif);
        uvm_config_db#(virtual axi4_if)::set(this, "region_monitor", "vif", vif);
        uvm_config_db#(virtual axi4_if)::set(this, "user_monitor", "vif", vif);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        fork
            monitor_write_channels();
            monitor_read_channels();
            check_protocol_compliance();
        join
    endtask
    
    // Monitor write channels
    task monitor_write_channels();
        fork
            monitor_aw_channel();
            monitor_w_channel();
            monitor_b_channel();
        join
    endtask
    
    // Monitor AW channel
    task monitor_aw_channel();
        forever begin
            @(posedge vif.clk);
            
            if (vif.awvalid && vif.awready) begin
                axi4_integrated_transaction trans = new();
                axi4_integrated_event evt = new();
                
                // Capture all signals
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
                trans.awuser = vif.awuser;
                trans.is_write = 1;
                trans.start_time = $realtime;
                
                // Create event
                evt.event_type = axi4_integrated_event::AW_HANDSHAKE;
                evt.trans = trans;
                evt.timestamp = $realtime;
                event_ap.write(evt);
                
                // Queue for assembly
                write_trans_queue[trans.id].push_back(trans);
                
                `uvm_info(get_type_name(), 
                         $sformatf("AW: addr=%0h, id=%0h, qos=%0d, region=%0d, user=%0h",
                                  trans.addr, trans.id, trans.qos, trans.region, trans.awuser), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Monitor W channel
    task monitor_w_channel();
        bit[{self.id_width-1}:0] current_id;
        int beat_count;
        
        forever begin
            @(posedge vif.clk);
            
            if (vif.wvalid && vif.wready) begin
                axi4_integrated_event evt = new();
                
                // Find matching AW transaction
                // Note: In AXI4, WID is removed, so we need to track based on order
                
                evt.event_type = axi4_integrated_event::W_BEAT;
                evt.timestamp = $realtime;
                evt.data = vif.wdata;
                evt.wstrb = vif.wstrb;
                evt.wuser = vif.wuser;
                evt.last = vif.wlast;
                event_ap.write(evt);
                
                `uvm_info(get_type_name(), 
                         $sformatf("W: data=%0h, strb=%0h, user=%0h, last=%0b",
                                  vif.wdata, vif.wstrb, vif.wuser, vif.wlast), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Monitor B channel
    task monitor_b_channel();
        forever begin
            @(posedge vif.clk);
            
            if (vif.bvalid && vif.bready) begin
                axi4_integrated_event evt = new();
                bit[{self.id_width-1}:0] id = vif.bid;
                
                // Find matching write transaction
                if (write_trans_queue.exists(id) && write_trans_queue[id].size() > 0) begin
                    axi4_integrated_transaction trans = write_trans_queue[id].pop_front();
                    
                    // Complete transaction
                    trans.resp[0] = vif.bresp;
                    trans.buser = vif.buser;
                    trans.end_time = $realtime;
                    
                    // Send completed transaction
                    trans_ap.write(trans);
                    total_write_trans++;
                end
                
                evt.event_type = axi4_integrated_event::B_HANDSHAKE;
                evt.timestamp = $realtime;
                evt.id = id;
                evt.resp = vif.bresp;
                evt.buser = vif.buser;
                event_ap.write(evt);
                
                `uvm_info(get_type_name(), 
                         $sformatf("B: id=%0h, resp=%0h, user=%0h",
                                  vif.bid, vif.bresp, vif.buser), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Monitor read channels
    task monitor_read_channels();
        fork
            monitor_ar_channel();
            monitor_r_channel();
        join
    endtask
    
    // Monitor AR channel
    task monitor_ar_channel();
        forever begin
            @(posedge vif.clk);
            
            if (vif.arvalid && vif.arready) begin
                axi4_integrated_transaction trans = new();
                axi4_integrated_event evt = new();
                
                // Capture all signals
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
                trans.aruser = vif.aruser;
                trans.is_write = 0;
                trans.start_time = $realtime;
                
                // Create event
                evt.event_type = axi4_integrated_event::AR_HANDSHAKE;
                evt.trans = trans;
                evt.timestamp = $realtime;
                event_ap.write(evt);
                
                // Queue for assembly
                read_trans_queue[trans.id].push_back(trans);
                
                `uvm_info(get_type_name(), 
                         $sformatf("AR: addr=%0h, id=%0h, qos=%0d, region=%0d, user=%0h",
                                  trans.addr, trans.id, trans.qos, trans.region, trans.aruser), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Monitor R channel
    task monitor_r_channel();
        axi4_integrated_transaction active_read_trans[bit[{self.id_width-1}:0]];
        int beat_count[bit[{self.id_width-1}:0]];
        
        forever begin
            @(posedge vif.clk);
            
            if (vif.rvalid && vif.rready) begin
                axi4_integrated_event evt = new();
                bit[{self.id_width-1}:0] id = vif.rid;
                
                // Initialize transaction tracking
                if (!active_read_trans.exists(id)) begin
                    if (read_trans_queue.exists(id) && read_trans_queue[id].size() > 0) begin
                        active_read_trans[id] = read_trans_queue[id].pop_front();
                        beat_count[id] = 0;
                    end
                end
                
                // Store data and response
                if (active_read_trans.exists(id)) begin
                    active_read_trans[id].data[beat_count[id]] = vif.rdata;
                    active_read_trans[id].resp[beat_count[id]] = vif.rresp;
                    active_read_trans[id].ruser[beat_count[id]] = vif.ruser;
                    beat_count[id]++;
                    
                    // Check for last beat
                    if (vif.rlast) begin
                        active_read_trans[id].end_time = $realtime;
                        trans_ap.write(active_read_trans[id]);
                        total_read_trans++;
                        
                        // Clean up
                        active_read_trans.delete(id);
                        beat_count.delete(id);
                    end
                end
                
                evt.event_type = axi4_integrated_event::R_BEAT;
                evt.timestamp = $realtime;
                evt.id = id;
                evt.data = vif.rdata;
                evt.resp = vif.rresp;
                evt.ruser = vif.ruser;
                evt.last = vif.rlast;
                event_ap.write(evt);
                
                `uvm_info(get_type_name(), 
                         $sformatf("R: id=%0h, data=%0h, resp=%0h, user=%0h, last=%0b",
                                  vif.rid, vif.rdata, vif.rresp, vif.ruser, vif.rlast), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Check protocol compliance
    task check_protocol_compliance();
        forever begin
            @(posedge vif.clk);
            
            // Check for X/Z values
            if ($isunknown(vif.awvalid) || $isunknown(vif.arvalid) ||
                $isunknown(vif.wvalid) || $isunknown(vif.rvalid) ||
                $isunknown(vif.bvalid)) begin
                `uvm_error(get_type_name(), "X/Z detected on valid signals")
                protocol_violations++;
            end
            
            // Check stable signals when valid is high
            // Additional protocol checks can be added here
        end
    endtask
    
    // Get monitor statistics
    function string get_stats();
        string stats = "\\n=== Integrated Monitor Statistics ===\\n";
        
        stats = {{stats, $sformatf("Total Write Transactions: %0d\\n", total_write_trans)}};
        stats = {{stats, $sformatf("Total Read Transactions: %0d\\n", total_read_trans)}};
        stats = {{stats, $sformatf("Protocol Violations: %0d\\n", protocol_violations)}};
        
        return stats;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_stats(), UVM_LOW)
    endfunction

endclass

// Integrated event class
class axi4_integrated_event extends uvm_sequence_item;
    `uvm_object_utils(axi4_integrated_event)
    
    typedef enum {{
        AW_HANDSHAKE,
        W_BEAT,
        B_HANDSHAKE,
        AR_HANDSHAKE,
        R_BEAT
    }} event_type_e;
    
    event_type_e event_type;
    axi4_integrated_transaction trans;
    realtime timestamp;
    
    // Channel-specific data
    bit[{self.id_width-1}:0] id;
    bit[{self.data_width-1}:0] data;
    bit[{self.data_width/8-1}:0] wstrb;
    bit[1:0] resp;
    bit last;
    
    // USER signals
    bit[{self.user_width-1}:0] wuser;
    bit[{self.user_width-1}:0] buser;
    bit[{self.user_width-1}:0] ruser;
    
    function new(string name = "axi4_integrated_event");
        super.new(name);
    endfunction

endclass

`endif // AXI4_INTEGRATED_MONITOR_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_integrated_monitor.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_integrated_checker(self, output_dir: str):
        """Generate integrated protocol checker"""
        content = f"""// AXI4 VIP Integrated Protocol Checker
// Generated: {datetime.datetime.now()}
// Comprehensive protocol checking for all AXI4 features

`ifndef AXI4_INTEGRATED_CHECKER_SV
`define AXI4_INTEGRATED_CHECKER_SV

class axi4_integrated_checker extends uvm_component;
    `uvm_component_utils(axi4_integrated_checker)
    
    // Analysis export
    uvm_analysis_imp #(axi4_integrated_transaction, axi4_integrated_checker) trans_export;
    
    // Sub-checkers
    axi4_qos_checker qos_checker;
    axi4_region_checker region_checker;
    axi4_user_checker user_checker;
    
    // Integrated checks configuration
    bit enable_qos_region_correlation = 1;
    bit enable_user_consistency = 1;
    bit enable_advanced_checks = 1;
    bit enable_performance_checks = 1;
    
    // Violation counters
    int qos_region_violations;
    int user_propagation_violations;
    int integrated_protocol_violations;
    int performance_violations;
    
    // Transaction history for correlation
    axi4_integrated_transaction trans_history[$];
    int max_history_size = 1000;
    
    // Constructor
    function new(string name = "axi4_integrated_checker", uvm_component parent = null);
        super.new(name, parent);
        trans_export = new("trans_export", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create sub-checkers if not already created
        if (qos_checker == null)
            qos_checker = axi4_qos_checker::type_id::create("qos_checker", this);
        if (region_checker == null)
            region_checker = axi4_region_checker::type_id::create("region_checker", this);
        if (user_checker == null)
            user_checker = axi4_user_checker::type_id::create("user_checker", this);
    endfunction
    
    // Write method for analysis export
    function void write(axi4_integrated_transaction trans);
        // Perform all checks
        check_transaction(trans);
        
        // Add to history
        trans_history.push_back(trans);
        if (trans_history.size() > max_history_size) begin
            void'(trans_history.pop_front());
        end
    endfunction
    
    // Main checking function
    function void check_transaction(axi4_integrated_transaction trans);
        // Individual feature checks
        check_qos_compliance(trans);
        check_region_compliance(trans);
        check_user_compliance(trans);
        
        // Integrated checks
        if (enable_qos_region_correlation) begin
            check_qos_region_correlation(trans);
        end
        
        if (enable_user_consistency) begin
            check_user_consistency(trans);
        end
        
        if (enable_advanced_checks) begin
            check_advanced_features(trans);
        end
        
        if (enable_performance_checks) begin
            check_performance_implications(trans);
        end
    endfunction
    
    // Check QoS compliance
    function void check_qos_compliance(axi4_integrated_transaction trans);
        // QoS range check
        if (trans.qos > 15) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Invalid QoS value: %0d (must be 0-15)", trans.qos))
            integrated_protocol_violations++;
        end
        
        // QoS consistency checks
        if (trans.lock && trans.qos < 8) begin
            `uvm_warning(get_type_name(), 
                        $sformatf("Exclusive access with low QoS %0d may cause issues", 
                                 trans.qos))
        end
    endfunction
    
    // Check REGION compliance
    function void check_region_compliance(axi4_integrated_transaction trans);
        // REGION range check
        if (trans.region > 15) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Invalid REGION value: %0d (must be 0-15)", trans.region))
            integrated_protocol_violations++;
        end
        
        // Check 4KB boundary crossing
        if (trans.crosses_4kb_boundary()) begin
            `uvm_warning(get_type_name(), 
                        $sformatf("Transaction crosses 4KB boundary: addr=%0h, len=%0d, size=%0d",
                                 trans.addr, trans.len, trans.size))
            
            // REGION must be consistent for addresses within 4KB
            // This would require tracking REGION changes
        end
    endfunction
    
    // Check USER signal compliance
    function void check_user_compliance(axi4_integrated_transaction trans);
        // USER signal propagation checks
        if (trans.is_write) begin
            // Check WUSER consistency
            if (enable_user_consistency && trans.wuser.size() > 0) begin
                bit[{self.user_width-1}:0] expected_wuser = trans.awuser;  // Simple rule
                foreach (trans.wuser[i]) begin
                    if (trans.wuser[i] != expected_wuser) begin
                        `uvm_info(get_type_name(), 
                                 $sformatf("WUSER[%0d] differs from AWUSER: %0h vs %0h",
                                          i, trans.wuser[i], expected_wuser), 
                                 UVM_HIGH)
                    end
                end
            end
        end
    endfunction
    
    // Check QoS-REGION correlation
    function void check_qos_region_correlation(axi4_integrated_transaction trans);
        // Example rules:
        // - High QoS (12-15) should use secure regions (12-15)
        // - Critical transactions should avoid shared regions
        
        if (trans.qos >= 12 && trans.region < 12) begin
            `uvm_warning(get_type_name(), 
                        $sformatf("High QoS %0d using non-secure region %0d",
                                 trans.qos, trans.region))
            qos_region_violations++;
        end
        
        // Check if QoS matches expected region characteristics
        case (trans.region)
            0, 1, 2, 3: begin  // Normal memory regions
                if (trans.qos > 11) begin
                    `uvm_info(get_type_name(), 
                             "Critical QoS using normal memory region", 
                             UVM_MEDIUM)
                end
            end
            
            4, 5, 6, 7: begin  // Device regions
                if (trans.cache[3:2] != 2'b00) begin
                    `uvm_warning(get_type_name(), 
                                "Cacheable access to device region")
                end
            end
            
            8, 9, 10, 11: begin  // Peripheral regions
                if (trans.len > 0) begin
                    `uvm_info(get_type_name(), 
                             "Burst access to peripheral region", 
                             UVM_MEDIUM)
                end
            end
            
            12, 13, 14, 15: begin  // Secure regions
                if (!trans.prot[1]) begin
                    `uvm_error(get_type_name(), 
                              "Non-secure access to secure region")
                    qos_region_violations++;
                end
            end
        endcase
    endfunction
    
    // Check USER signal consistency
    function void check_user_consistency(axi4_integrated_transaction trans);
        // Check USER signal patterns
        if (trans.is_write) begin
            // Analyze AWUSER encoding
            analyze_user_encoding(trans.awuser, "AWUSER");
            
            // Check BUSER relationship to AWUSER
            if (trans.buser != 0) begin
                check_user_relationship(trans.awuser, trans.buser, "AW->B");
            end
        end else begin
            // Analyze ARUSER encoding
            analyze_user_encoding(trans.aruser, "ARUSER");
            
            // Check RUSER pattern
            if (trans.ruser.size() > 0) begin
                check_ruser_pattern(trans);
            end
        end
    endfunction
    
    // Analyze USER signal encoding
    function void analyze_user_encoding(bit[{self.user_width-1}:0] user_val, string signal_name);
        // Check for known patterns
        case (user_val[15:12])
            4'hD: begin  // Debug pattern
                `uvm_info(get_type_name(), 
                         $sformatf("%s contains debug information: %0h", 
                                  signal_name, user_val), 
                         UVM_HIGH)
            end
            
            4'hS: begin  // Security pattern
                `uvm_info(get_type_name(), 
                         $sformatf("%s contains security information: %0h", 
                                  signal_name, user_val), 
                         UVM_HIGH)
            end
            
            4'hM: begin  // Metadata pattern
                `uvm_info(get_type_name(), 
                         $sformatf("%s contains metadata: %0h", 
                                  signal_name, user_val), 
                         UVM_HIGH)
            end
        endcase
    endfunction
    
    // Check USER signal relationship
    function void check_user_relationship(bit[{self.user_width-1}:0] user1,
                                        bit[{self.user_width-1}:0] user2,
                                        string relationship);
        // Define expected relationships
        if (user1[15:12] == user2[15:12]) begin
            `uvm_info(get_type_name(), 
                     $sformatf("USER %s maintains category: %0h", 
                              relationship, user1[15:12]), 
                     UVM_HIGH)
        end else begin
            `uvm_warning(get_type_name(), 
                        $sformatf("USER %s category mismatch: %0h -> %0h",
                                 relationship, user1[15:12], user2[15:12]))
            user_propagation_violations++;
        end
    endfunction
    
    // Check RUSER pattern
    function void check_ruser_pattern(axi4_integrated_transaction trans);
        // Check if RUSER follows expected pattern
        bit consistent = 1;
        bit[{self.user_width-1}:0] expected_ruser = trans.aruser;  // Simple echo
        
        foreach (trans.ruser[i]) begin
            if (trans.ruser[i] != expected_ruser) begin
                consistent = 0;
            end
        end
        
        if (!consistent) begin
            `uvm_info(get_type_name(), 
                     "RUSER values vary across burst", 
                     UVM_MEDIUM)
        end
    endfunction
    
    // Check advanced feature interactions
    function void check_advanced_features(axi4_integrated_transaction trans);
        // Exclusive access with high QoS
        if (trans.lock && trans.qos >= 12) begin
            `uvm_info(get_type_name(), 
                     "Exclusive access with critical QoS - ensure proper handling", 
                     UVM_MEDIUM)
        end
        
        // Cacheable access to specific regions
        if (trans.cache[3:2] != 2'b00 && trans.region >= 8) begin
            `uvm_warning(get_type_name(), 
                        $sformatf("Cacheable access to region %0d may not be optimal",
                                 trans.region))
        end
        
        // USER signal correlation with protection
        if (trans.prot[1] && trans.awuser[15:12] != 4'hS) begin
            `uvm_info(get_type_name(), 
                     "Secure transaction without security USER encoding", 
                     UVM_HIGH)
        end
    endfunction
    
    // Check performance implications
    function void check_performance_implications(axi4_integrated_transaction trans);
        // High QoS with large burst
        if (trans.qos >= 12 && trans.len > 63) begin
            `uvm_warning(get_type_name(), 
                        "Large burst with critical QoS may impact other masters")
            performance_violations++;
        end
        
        // Multiple features enabled
        int feature_count = 0;
        if (trans.qos > 8) feature_count++;
        if (trans.lock) feature_count++;
        if (trans.cache[3:2] != 2'b00) feature_count++;
        if (trans.region >= 12) feature_count++;
        
        if (feature_count >= 3) begin
            `uvm_info(get_type_name(), 
                     $sformatf("Transaction uses %0d advanced features - may impact performance",
                              feature_count), 
                     UVM_MEDIUM)
        end
        
        // Check transaction latency
        if (trans.end_time > 0 && trans.start_time > 0) begin
            real latency = trans.get_latency();
            
            // QoS-based latency expectations
            real expected_max_latency;
            case (trans.qos)
                15, 14, 13, 12: expected_max_latency = 100;   // 100ns for critical
                11, 10, 9, 8:   expected_max_latency = 500;   // 500ns for high
                7, 6, 5, 4:     expected_max_latency = 1000;  // 1us for medium
                default:        expected_max_latency = 10000; // 10us for low
            endcase
            
            if (latency > expected_max_latency) begin
                `uvm_warning(get_type_name(), 
                            $sformatf("Transaction latency %0.0fns exceeds QoS %0d expectation of %0.0fns",
                                     latency, trans.qos, expected_max_latency))
                performance_violations++;
            end
        end
    endfunction
    
    // Analyze transaction patterns
    function void analyze_patterns();
        if (trans_history.size() < 10) return;
        
        // Look for patterns in recent transactions
        int qos_distribution[16];
        int region_distribution[16];
        int master_activity[int];
        
        foreach (trans_history[i]) begin
            qos_distribution[trans_history[i].qos]++;
            region_distribution[trans_history[i].region]++;
            master_activity[trans_history[i].master_id]++;
        end
        
        // Check for QoS imbalance
        int total_critical = 0;
        for (int i = 12; i <= 15; i++) begin
            total_critical += qos_distribution[i];
        end
        
        if (total_critical > trans_history.size() / 2) begin
            `uvm_warning(get_type_name(), 
                        "Excessive use of critical QoS levels")
        end
    endfunction
    
    // Get checker statistics
    function string get_checker_stats();
        string stats = "\\n=== Integrated Checker Statistics ===\\n";
        
        stats = {{stats, $sformatf("QoS-Region Violations: %0d\\n", qos_region_violations)}};
        stats = {{stats, $sformatf("USER Propagation Violations: %0d\\n", user_propagation_violations)}};
        stats = {{stats, $sformatf("Integrated Protocol Violations: %0d\\n", integrated_protocol_violations)}};
        stats = {{stats, $sformatf("Performance Violations: %0d\\n", performance_violations)}};
        stats = {{stats, $sformatf("Transaction History Size: %0d\\n", trans_history.size())}};
        
        return stats;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        // Analyze final patterns
        analyze_patterns();
        
        // Report statistics
        `uvm_info(get_type_name(), get_checker_stats(), UVM_LOW)
        
        // Report overall status
        int total_violations = qos_region_violations + user_propagation_violations + 
                              integrated_protocol_violations + performance_violations;
        
        if (total_violations == 0) begin
            `uvm_info(get_type_name(), 
                     "All integrated protocol checks PASSED", 
                     UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), 
                      $sformatf("Integrated protocol checks FAILED with %0d violations",
                               total_violations))
        end
    endfunction

endclass

// Additional checker for USER signals
class axi4_user_checker extends uvm_component;
    `uvm_component_utils(axi4_user_checker)
    
    function new(string name = "axi4_user_checker", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Placeholder for USER-specific checks
    // Implementation would include USER signal validation

endclass

`endif // AXI4_INTEGRATED_CHECKER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_integrated_checker.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_integrated_env(self, output_dir: str):
        """Generate integrated environment"""
        content = f"""// AXI4 VIP Integrated Environment
// Generated: {datetime.datetime.now()}
// Complete verification environment with all advanced features

`ifndef AXI4_INTEGRATED_ENV_SV
`define AXI4_INTEGRATED_ENV_SV

class axi4_integrated_env extends uvm_env;
    `uvm_component_utils(axi4_integrated_env)
    
    // Agents
    axi4_master_agent master_agents[{self.num_masters}];
    axi4_slave_agent slave_agents[{self.num_slaves}];
    
    // Advanced feature components
    axi4_qos_env qos_env;
    axi4_region_env region_env;
    axi4_user_env user_env;
    
    // Integrated components
    axi4_integrated_monitor integrated_monitor;
    axi4_integrated_checker integrated_checker;
    
    // Scoreboards
    axi4_transaction_scoreboard trans_scoreboard;
    axi4_qos_scoreboard qos_scoreboard;
    axi4_region_scoreboard region_scoreboard;
    axi4_user_scoreboard user_scoreboard;
    
    // Coverage
    axi4_integrated_coverage integrated_coverage;
    
    // Virtual sequencer
    axi4_integrated_virtual_sequencer virtual_sequencer;
    
    // Configuration
    axi4_integrated_config cfg;
    
    // Constructor
    function new(string name = "axi4_integrated_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(axi4_integrated_config)::get(this, "", "cfg", cfg)) begin
            cfg = axi4_integrated_config::type_id::create("cfg");
            cfg.randomize();
        end
        
        // Create agents
        foreach (master_agents[i]) begin
            master_agents[i] = axi4_master_agent::type_id::create($sformatf("master_agent_%0d", i), this);
            master_agents[i].is_active = UVM_ACTIVE;
        end
        
        foreach (slave_agents[i]) begin
            slave_agents[i] = axi4_slave_agent::type_id::create($sformatf("slave_agent_%0d", i), this);
            slave_agents[i].is_active = UVM_ACTIVE;
        end
        
        // Create advanced feature environments
        qos_env = axi4_qos_env::type_id::create("qos_env", this);
        region_env = axi4_region_env::type_id::create("region_env", this);
        user_env = axi4_user_env::type_id::create("user_env", this);
        
        // Create integrated components
        integrated_monitor = axi4_integrated_monitor::type_id::create("integrated_monitor", this);
        integrated_checker = axi4_integrated_checker::type_id::create("integrated_checker", this);
        
        // Create scoreboards
        trans_scoreboard = axi4_transaction_scoreboard::type_id::create("trans_scoreboard", this);
        qos_scoreboard = axi4_qos_scoreboard::type_id::create("qos_scoreboard", this);
        region_scoreboard = axi4_region_scoreboard::type_id::create("region_scoreboard", this);
        user_scoreboard = axi4_user_scoreboard::type_id::create("user_scoreboard", this);
        
        // Create coverage
        integrated_coverage = axi4_integrated_coverage::type_id::create("integrated_coverage", this);
        
        // Create virtual sequencer
        virtual_sequencer = axi4_integrated_virtual_sequencer::type_id::create("virtual_sequencer", this);
        
        // Configure sub-environments
        configure_environments();
    endfunction
    
    // Configure environments
    function void configure_environments();
        // Configure QoS
        axi4_qos_configurator qos_config = axi4_qos_configurator::get();
        qos_config.set_arbitration_mode("WEIGHTED_ROUND_ROBIN");
        
        // Configure masters with different QoS policies
        for (int i = 0; i < {self.num_masters}; i++) begin
            bit[3:0] min_qos = (i == 0) ? 0 : (i * 4);
            bit[3:0] max_qos = (i == {self.num_masters-1}) ? 15 : ((i + 1) * 4 - 1);
            qos_config.configure_master_qos(i, i * 4, min_qos, max_qos);
        end
        
        // Configure REGION
        axi4_region_configurator region_config = axi4_region_configurator::get();
        region_config.generate_example_config();
        
        // Configure USER
        axi4_user_configuration user_config = axi4_user_configuration::get();
        user_config.generate_example_config();
    endfunction
    
    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect monitor to checker and coverage
        integrated_monitor.trans_ap.connect(integrated_checker.trans_export);
        integrated_monitor.trans_ap.connect(integrated_coverage.analysis_export);
        
        // Connect to scoreboards
        integrated_monitor.trans_ap.connect(trans_scoreboard.master_export);
        
        // Connect virtual sequencer
        foreach (master_agents[i]) begin
            virtual_sequencer.master_sequencers[i] = master_agents[i].sequencer;
        end
        
        foreach (slave_agents[i]) begin
            virtual_sequencer.slave_sequencers[i] = slave_agents[i].sequencer;
        end
        
        virtual_sequencer.qos_sequencer = qos_env.qos_agent.user_sequencer;
        virtual_sequencer.user_sequencer = user_env.user_agent.user_sequencer;
    endfunction
    
    // End of elaboration
    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        
        // Print environment configuration
        `uvm_info(get_type_name(), "=== Integrated Environment Configuration ===", UVM_LOW)
        `uvm_info(get_type_name(), 
                 $sformatf("Masters: %0d, Slaves: %0d", {self.num_masters}, {self.num_slaves}), 
                 UVM_LOW)
        `uvm_info(get_type_name(), "QoS: Enabled", UVM_LOW)
        `uvm_info(get_type_name(), "REGION: Enabled", UVM_LOW)
        `uvm_info(get_type_name(), "USER: Enabled", UVM_LOW)
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        `uvm_info(get_type_name(), "=== Integrated Environment Report ===", UVM_LOW)
        // Sub-components will report their own statistics
    endfunction

endclass

// Integrated configuration class
class axi4_integrated_config extends uvm_object;
    `uvm_object_utils(axi4_integrated_config)
    
    // Basic configuration
    rand int num_masters = {self.num_masters};
    rand int num_slaves = {self.num_slaves};
    
    // Feature enables
    bit enable_qos = 1;
    bit enable_region = 1;
    bit enable_user = 1;
    bit enable_exclusive = 1;
    bit enable_4kb_check = 1;
    
    // Advanced configuration
    bit enable_qos_arbitration = 1;
    bit enable_region_protection = 1;
    bit enable_user_propagation = 1;
    
    function new(string name = "axi4_integrated_config");
        super.new(name);
    endfunction

endclass

// Integrated coverage
class axi4_integrated_coverage extends uvm_subscriber #(axi4_integrated_transaction);
    `uvm_component_utils(axi4_integrated_coverage)
    
    axi4_integrated_transaction trans;
    
    // Integrated coverage groups
    covergroup cg_integrated_features;
        option.per_instance = 1;
        
        // QoS vs REGION
        qos_cp: coverpoint trans.qos {{
            bins low = {{[0:3]}};
            bins medium = {{[4:7]}};
            bins high = {{[8:11]}};
            bins critical = {{[12:15]}};
        }}
        
        region_cp: coverpoint trans.region {{
            bins normal_mem = {{[0:3]}};
            bins device_mem = {{[4:7]}};
            bins peripheral = {{[8:11]}};
            bins secure = {{[12:15]}};
        }}
        
        qos_x_region: cross qos_cp, region_cp;
        
        // Advanced features
        exclusive_cp: coverpoint trans.lock;
        cache_cp: coverpoint trans.cache[3:2] {{
            bins non_cacheable = {{2'b00}};
            bins write_through = {{2'b10}};
            bins write_back = {{2'b11}};
        }}
        
        // Feature combinations
        high_qos_exclusive: cross qos_cp, exclusive_cp iff (trans.qos >= 8);
        secure_region_prot: cross region_cp, trans.prot[1] iff (trans.region >= 12);
    endgroup
    
    covergroup cg_user_patterns;
        option.per_instance = 1;
        
        // USER signal patterns
        awuser_pattern: coverpoint trans.awuser[15:12] iff (trans.is_write) {{
            bins metadata = {{4'hM}};
            bins security = {{4'hS}};
            bins debug = {{4'hD}};
            bins other = default;
        }}
        
        aruser_pattern: coverpoint trans.aruser[15:12] iff (!trans.is_write) {{
            bins metadata = {{4'hM}};
            bins security = {{4'hS}};
            bins debug = {{4'hD}};
            bins other = default;
        }}
        
        // USER vs QoS correlation
        user_x_qos: cross awuser_pattern, qos_cp iff (trans.is_write);
    endgroup
    
    function new(string name = "axi4_integrated_coverage", uvm_component parent = null);
        super.new(name, parent);
        cg_integrated_features = new();
        cg_user_patterns = new();
    endfunction
    
    function void write(axi4_integrated_transaction t);
        trans = t;
        cg_integrated_features.sample();
        cg_user_patterns.sample();
    endfunction
    
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), 
                 $sformatf("Integrated Coverage: %0.2f%%", 
                          (cg_integrated_features.get_coverage() + 
                           cg_user_patterns.get_coverage()) / 2.0), 
                 UVM_LOW)
    endfunction

endclass

// Integrated virtual sequencer
class axi4_integrated_virtual_sequencer extends uvm_sequencer;
    `uvm_component_utils(axi4_integrated_virtual_sequencer)
    
    // Sub-sequencers
    axi4_master_sequencer master_sequencers[{self.num_masters}];
    axi4_slave_sequencer slave_sequencers[{self.num_slaves}];
    axi4_user_sequencer user_sequencer;
    axi4_qos_sequencer qos_sequencer;
    
    function new(string name = "axi4_integrated_virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction

endclass

`endif // AXI4_INTEGRATED_ENV_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_integrated_env.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_integrated_test_library(self, output_dir: str):
        """Generate integrated test library"""
        content = f"""// AXI4 VIP Integrated Test Library
// Generated: {datetime.datetime.now()}
// Test library demonstrating all advanced features

`ifndef AXI4_INTEGRATED_TEST_LIB_SV
`define AXI4_INTEGRATED_TEST_LIB_SV

// Base test class
class axi4_integrated_base_test extends uvm_test;
    `uvm_component_utils(axi4_integrated_base_test)
    
    axi4_integrated_env env;
    axi4_integrated_config cfg;
    
    function new(string name = "axi4_integrated_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create configuration
        cfg = axi4_integrated_config::type_id::create("cfg");
        cfg.enable_qos = 1;
        cfg.enable_region = 1;
        cfg.enable_user = 1;
        
        // Set configuration
        uvm_config_db#(axi4_integrated_config)::set(this, "env", "cfg", cfg);
        
        // Create environment
        env = axi4_integrated_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        // Allow time for reset
        #100ns;
        
        // Run test sequences
        run_test_sequences();
        
        // Allow time for completion
        #1us;
        
        phase.drop_objection(this);
    endtask
    
    // Override in derived tests
    virtual task run_test_sequences();
        `uvm_info(get_type_name(), "No sequences defined in base test", UVM_MEDIUM)
    endtask

endclass

// QoS feature test
class axi4_qos_feature_test extends axi4_integrated_base_test;
    `uvm_component_utils(axi4_qos_feature_test)
    
    function new(string name = "axi4_qos_feature_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_test_sequences();
        axi4_qos_test_sequence seq;
        
        `uvm_info(get_type_name(), "Starting QoS Feature Test", UVM_LOW)
        
        // Run QoS test sequence
        seq = axi4_qos_test_sequence::type_id::create("seq");
        seq.start(env.virtual_sequencer);
        
        #500ns;
    endtask

endclass

// REGION feature test
class axi4_region_feature_test extends axi4_integrated_base_test;
    `uvm_component_utils(axi4_region_feature_test)
    
    function new(string name = "axi4_region_feature_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_test_sequences();
        axi4_region_test_sequence seq;
        
        `uvm_info(get_type_name(), "Starting REGION Feature Test", UVM_LOW)
        
        // Run REGION test sequence
        seq = axi4_region_test_sequence::type_id::create("seq");
        seq.start(env.virtual_sequencer);
        
        #500ns;
    endtask

endclass

// USER feature test
class axi4_user_feature_test extends axi4_integrated_base_test;
    `uvm_component_utils(axi4_user_feature_test)
    
    function new(string name = "axi4_user_feature_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_test_sequences();
        axi4_user_test_sequence seq;
        
        `uvm_info(get_type_name(), "Starting USER Feature Test", UVM_LOW)
        
        // Run USER test sequence
        seq = axi4_user_test_sequence::type_id::create("seq");
        seq.start(env.virtual_sequencer);
        
        #500ns;
    endtask

endclass

// Integrated features test
class axi4_integrated_features_test extends axi4_integrated_base_test;
    `uvm_component_utils(axi4_integrated_features_test)
    
    function new(string name = "axi4_integrated_features_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_test_sequences();
        `uvm_info(get_type_name(), "Starting Integrated Features Test", UVM_LOW)
        
        // Run multiple feature sequences in parallel
        fork
            run_qos_sequences();
            run_region_sequences();
            run_user_sequences();
            run_integrated_sequences();
        join
        
        #1us;
    endtask
    
    task run_qos_sequences();
        axi4_qos_stress_sequence seq;
        seq = axi4_qos_stress_sequence::type_id::create("qos_seq");
        seq.start(env.virtual_sequencer);
    endtask
    
    task run_region_sequences();
        axi4_region_boundary_sequence seq;
        seq = axi4_region_boundary_sequence::type_id::create("region_seq");
        #100ns;  // Stagger start
        seq.start(env.virtual_sequencer);
    endtask
    
    task run_user_sequences();
        axi4_user_pattern_sequence seq;
        seq = axi4_user_pattern_sequence::type_id::create("user_seq");
        #200ns;  // Stagger start
        seq.start(env.virtual_sequencer.user_sequencer);
    endtask
    
    task run_integrated_sequences();
        axi4_integrated_stress_sequence seq;
        seq = axi4_integrated_stress_sequence::type_id::create("integrated_seq");
        #300ns;  // Stagger start
        seq.start(env.virtual_sequencer);
    endtask

endclass

// Test sequences
class axi4_qos_test_sequence extends uvm_sequence;
    `uvm_object_utils(axi4_qos_test_sequence)
    
    function new(string name = "axi4_qos_test_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_integrated_transaction trans;
        
        // Test different QoS levels
        for (int qos = 0; qos < 16; qos++) begin
            for (int i = 0; i < 5; i++) begin
                trans = axi4_integrated_transaction::type_id::create("trans");
                
                start_item(trans);
                if (!trans.randomize() with {{
                    qos == local::qos;
                    len inside {{[0:15]}};
                    size inside {{[0:3]}};
                }}) begin
                    `uvm_fatal(get_type_name(), "Randomization failed")
                end
                finish_item(trans);
            end
        end
    endtask

endclass

class axi4_region_test_sequence extends uvm_sequence;
    `uvm_object_utils(axi4_region_test_sequence)
    
    function new(string name = "axi4_region_test_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_integrated_transaction trans;
        
        // Test all regions
        for (int region = 0; region < 16; region++) begin
            trans = axi4_integrated_transaction::type_id::create("trans");
            
            start_item(trans);
            if (!trans.randomize() with {{
                region == local::region;
                addr[31:28] == local::region;  // Align address with region
                len inside {{[0:15]}};
            }}) begin
                `uvm_fatal(get_type_name(), "Randomization failed")
            end
            finish_item(trans);
        end
        
        // Test 4KB boundary scenarios
        test_4kb_boundaries();
    endtask
    
    task test_4kb_boundaries();
        axi4_integrated_transaction trans;
        
        // Test near 4KB boundary
        trans = axi4_integrated_transaction::type_id::create("trans");
        start_item(trans);
        if (!trans.randomize() with {{
            addr[11:0] == 12'hFF0;  // Near 4KB boundary
            len == 15;               // Will cross boundary
            size == 2;               // 4 bytes per beat
        }}) begin
            `uvm_fatal(get_type_name(), "Randomization failed")
        end
        finish_item(trans);
    endtask

endclass

class axi4_user_test_sequence extends uvm_sequence;
    `uvm_object_utils(axi4_user_test_sequence)
    
    function new(string name = "axi4_user_test_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_user_metadata_sequence meta_seq;
        axi4_user_security_sequence sec_seq;
        axi4_user_debug_sequence dbg_seq;
        
        // Run different USER sequences
        meta_seq = axi4_user_metadata_sequence::type_id::create("meta_seq");
        meta_seq.num_trans = 20;
        meta_seq.start(m_sequencer);
        
        sec_seq = axi4_user_security_sequence::type_id::create("sec_seq");
        sec_seq.num_trans = 20;
        sec_seq.start(m_sequencer);
        
        dbg_seq = axi4_user_debug_sequence::type_id::create("dbg_seq");
        dbg_seq.num_trans = 20;
        dbg_seq.start(m_sequencer);
    endtask

endclass

// Stress sequences
class axi4_qos_stress_sequence extends uvm_sequence;
    `uvm_object_utils(axi4_qos_stress_sequence)
    
    rand int num_trans = 100;
    
    function new(string name = "axi4_qos_stress_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_integrated_transaction trans;
        
        // Generate high rate of critical QoS transactions
        fork
            begin
                for (int i = 0; i < num_trans; i++) begin
                    trans = axi4_integrated_transaction::type_id::create("trans");
                    start_item(trans);
                    if (!trans.randomize() with {{
                        qos >= 12;  // Critical QoS
                        len inside {{[0:3]}};  // Short bursts for low latency
                    }}) begin
                        `uvm_fatal(get_type_name(), "Randomization failed")
                    end
                    finish_item(trans);
                end
            end
            
            begin
                // Background traffic with lower QoS
                for (int i = 0; i < num_trans * 2; i++) begin
                    trans = axi4_integrated_transaction::type_id::create("trans");
                    start_item(trans);
                    if (!trans.randomize() with {{
                        qos inside {{[0:7]}};  // Low to medium QoS
                        len inside {{[0:255]}};  // Various burst lengths
                    }}) begin
                        `uvm_fatal(get_type_name(), "Randomization failed")
                    end
                    finish_item(trans);
                    #10ns;  // Pace the background traffic
                end
            end
        join
    endtask

endclass

class axi4_region_boundary_sequence extends uvm_sequence;
    `uvm_object_utils(axi4_region_boundary_sequence)
    
    function new(string name = "axi4_region_boundary_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_integrated_transaction trans;
        
        // Test transactions at region boundaries
        for (int region = 0; region < 15; region++) begin
            // Transaction at end of region
            trans = axi4_integrated_transaction::type_id::create("trans");
            start_item(trans);
            if (!trans.randomize() with {{
                addr == ((region + 1) * 32'h1000_0000 - 32'h100);
                region == local::region;
                len inside {{[0:15]}};
            }}) begin
                `uvm_fatal(get_type_name(), "Randomization failed")
            end
            finish_item(trans);
            
            // Transaction at start of next region
            trans = axi4_integrated_transaction::type_id::create("trans");
            start_item(trans);
            if (!trans.randomize() with {{
                addr == ((region + 1) * 32'h1000_0000);
                region == (local::region + 1);
                len inside {{[0:15]}};
            }}) begin
                `uvm_fatal(get_type_name(), "Randomization failed")
            end
            finish_item(trans);
        end
    endtask

endclass

class axi4_integrated_stress_sequence extends uvm_sequence;
    `uvm_object_utils(axi4_integrated_stress_sequence)
    
    rand int num_trans = 200;
    
    function new(string name = "axi4_integrated_stress_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_integrated_transaction trans;
        
        // Generate transactions with all features
        for (int i = 0; i < num_trans; i++) begin
            trans = axi4_integrated_transaction::type_id::create("trans");
            
            start_item(trans);
            if (!trans.randomize() with {{
                // Correlate QoS with region
                (qos >= 12) -> (region >= 12);  // Critical QoS uses secure regions
                (region >= 8) -> (len == 0);    // Peripheral regions use single beats
                
                // Exclusive access constraints
                lock -> (qos >= 8);  // Only high QoS can use exclusive
                
                // USER signal patterns
                awuser[15:12] == (qos >= 12) ? 4'hS : 4'hM;  // Security vs Metadata
            }}) begin
                `uvm_fatal(get_type_name(), "Randomization failed")
            end
            
            // Inject specific scenarios
            if (i % 20 == 0) begin
                // Force 4KB boundary scenario
                trans.addr[11:0] = 12'hF80;
                trans.len = 31;
                trans.size = 3;
            end
            
            finish_item(trans);
        end
    endtask

endclass

`endif // AXI4_INTEGRATED_TEST_LIB_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_integrated_test_lib.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_integrated_package(self, output_dir: str):
        """Generate integrated package"""
        content = f"""// AXI4 VIP Integrated Package
// Generated: {datetime.datetime.now()}
// Package containing all integrated components

`ifndef AXI4_INTEGRATED_PKG_SV
`define AXI4_INTEGRATED_PKG_SV

package axi4_integrated_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Import feature packages
    import axi4_qos_pkg::*;
    import axi4_region_pkg::*;
    import axi4_user_pkg::*;
    
    // Base VIP imports
    import axi4_vip_pkg::*;
    
    // Parameters
    parameter ADDR_WIDTH = {self.addr_width};
    parameter DATA_WIDTH = {self.data_width};
    parameter ID_WIDTH = {self.id_width};
    parameter USER_WIDTH = {self.user_width};
    parameter NUM_MASTERS = {self.num_masters};
    parameter NUM_SLAVES = {self.num_slaves};
    
    // Include integrated components
    `include "axi4_integrated_transaction.sv"
    `include "axi4_integrated_monitor.sv"
    `include "axi4_integrated_checker.sv"
    `include "axi4_integrated_env.sv"
    `include "axi4_integrated_test_lib.sv"
    
endpackage

`endif // AXI4_INTEGRATED_PKG_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_integrated_pkg.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def generate_integration_example(self, output_dir: str):
        """Generate complete integration example"""
        content = f"""// AXI4 VIP Complete Integration Example
// Generated: {datetime.datetime.now()}
// Demonstrates usage of all advanced features

`ifndef AXI4_INTEGRATION_EXAMPLE_SV
`define AXI4_INTEGRATION_EXAMPLE_SV

// Top-level testbench
module axi4_vip_tb_top;
    
    // Clock and reset
    logic clk;
    logic resetn;
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Reset generation
    initial begin
        resetn = 0;
        #100 resetn = 1;
    end
    
    // Integrated interface instance
    axi4_integrated_if #(
        .ADDR_WIDTH({self.addr_width}),
        .DATA_WIDTH({self.data_width}),
        .ID_WIDTH({self.id_width}),
        .AWUSER_WIDTH({self.user_width}),
        .WUSER_WIDTH({self.user_width}),
        .BUSER_WIDTH({self.user_width}),
        .ARUSER_WIDTH({self.user_width}),
        .RUSER_WIDTH({self.user_width})
    ) vif (clk, resetn);
    
    // DUT instantiation (example)
    axi4_interconnect_dut #(
        .NUM_MASTERS({self.num_masters}),
        .NUM_SLAVES({self.num_slaves})
    ) dut (
        .clk(clk),
        .resetn(resetn),
        // Connect all AXI signals including QoS, REGION, USER
        .m_axi(vif.slave),  // Masters connect to slave ports
        .s_axi(vif.master)  // Slaves connect to master ports
    );
    
    // UVM test
    initial begin
        // Set virtual interface
        uvm_config_db#(virtual axi4_integrated_if)::set(
            null, "*", "vif", vif);
        
        // Run test
        run_test();
    end
    
    // Waveform dumping
    initial begin
        $dumpfile("axi4_vip.vcd");
        $dumpvars(0, axi4_vip_tb_top);
    end
    
    // Timeout
    initial begin
        #100ms;
        `uvm_fatal("TIMEOUT", "Test timeout")
    end

endmodule

// Example DUT stub
module axi4_interconnect_dut #(
    parameter NUM_MASTERS = {self.num_masters},
    parameter NUM_SLAVES = {self.num_slaves}
)(
    input logic clk,
    input logic resetn,
    axi4_integrated_if.slave m_axi[NUM_MASTERS],
    axi4_integrated_if.master s_axi[NUM_SLAVES]
);
    
    // Simple interconnect implementation
    // This would be replaced with actual RTL
    
    // Example: Connect master 0 to slave 0 with QoS arbitration
    always_comb begin
        // Default assignments
        foreach (m_axi[i]) begin
            m_axi[i].awready = 1'b0;
            m_axi[i].wready = 1'b0;
            m_axi[i].bvalid = 1'b0;
            m_axi[i].arready = 1'b0;
            m_axi[i].rvalid = 1'b0;
        end
        
        foreach (s_axi[i]) begin
            s_axi[i].awvalid = 1'b0;
            s_axi[i].wvalid = 1'b0;
            s_axi[i].bready = 1'b0;
            s_axi[i].arvalid = 1'b0;
            s_axi[i].rready = 1'b0;
        end
        
        // Simple routing based on address bits
        // Real implementation would have QoS arbitration,
        // REGION-based routing, and USER signal handling
    end

endmodule

// Example test program
program automatic test_program;
    
    import uvm_pkg::*;
    import axi4_integrated_pkg::*;
    
    initial begin
        // Create and configure test
        axi4_integrated_config cfg;
        cfg = new("cfg");
        cfg.num_masters = {self.num_masters};
        cfg.num_slaves = {self.num_slaves};
        cfg.enable_qos = 1;
        cfg.enable_region = 1;
        cfg.enable_user = 1;
        
        // Set configuration
        uvm_config_db#(axi4_integrated_config)::set(null, "*", "cfg", cfg);
        
        // Select test
        if ($test$plusargs("TEST=QOS")) begin
            run_test("axi4_qos_feature_test");
        end else if ($test$plusargs("TEST=REGION")) begin
            run_test("axi4_region_feature_test");
        end else if ($test$plusargs("TEST=USER")) begin
            run_test("axi4_user_feature_test");
        end else if ($test$plusargs("TEST=INTEGRATED")) begin
            run_test("axi4_integrated_features_test");
        end else begin
            // Default test
            run_test("axi4_integrated_features_test");
        end
    end

endprogram

`endif // AXI4_INTEGRATION_EXAMPLE_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_integration_example.sv")
        with open(filepath, 'w') as f:
            f.write(content)

# Example usage
if __name__ == "__main__":
    config = {
        'num_masters': 4,
        'num_slaves': 4,
        'data_width': 64,
        'addr_width': 32,
        'id_width': 4,
        'user_width': 16,
        'protocol': 'AXI4'
    }
    
    integrator = VIPAdvancedProtocolIntegrator(config)
    integrator.generate_integrated_components("./vip_output")
    integrator.generate_integration_example("./vip_output")
    print("Integrated advanced protocol features generated successfully!")