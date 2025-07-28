#!/usr/bin/env python3
"""
VIP USER Signal Implementation Generator
Generates comprehensive USER signal components for AXI4 verification
"""

import os
import datetime
from typing import Dict, List, Optional, Tuple

class VIPUserGenerator:
    """Generator for AXI4 VIP USER signal implementation"""
    
    def __init__(self, config: Dict):
        """Initialize generator with configuration"""
        self.config = config
        self.num_masters = config.get('num_masters', 2)
        self.num_slaves = config.get('num_slaves', 2)
        self.data_width = config.get('data_width', 64)
        self.addr_width = config.get('addr_width', 32)
        self.id_width = config.get('id_width', 4)
        self.user_width = config.get('user_width', 16)  # Configurable USER width
        self.protocol_version = config.get('protocol', 'AXI4')
        
        # USER signal configuration
        self.awuser_width = config.get('awuser_width', self.user_width)
        self.wuser_width = config.get('wuser_width', self.user_width)
        self.buser_width = config.get('buser_width', self.user_width)
        self.aruser_width = config.get('aruser_width', self.user_width)
        self.ruser_width = config.get('ruser_width', self.user_width)
        
    def generate_all_user_components(self, output_dir: str):
        """Generate all USER signal components"""
        # Create directory structure
        user_dir = os.path.join(output_dir, 'user')
        os.makedirs(user_dir, exist_ok=True)
        
        # Generate USER components
        self._generate_user_agent(user_dir)
        self._generate_user_sequencer(user_dir)
        self._generate_user_monitor(user_dir)
        self._generate_user_scoreboard(user_dir)
        self._generate_user_coverage(user_dir)
        self._generate_user_protocol_handler(user_dir)
        self._generate_user_configuration(user_dir)
        self._generate_user_package(user_dir)
        
    def _generate_user_agent(self, output_dir: str):
        """Generate USER signal agent"""
        content = f"""// AXI4 VIP USER Signal Agent
// Generated: {datetime.datetime.now()}
// Handles USER signal generation and checking

`ifndef AXI4_USER_AGENT_SV
`define AXI4_USER_AGENT_SV

class axi4_user_agent extends uvm_agent;
    `uvm_component_utils(axi4_user_agent)
    
    // Configuration
    typedef struct {{
        bit active = 1;
        bit enable_user_checking = 1;
        bit enable_user_generation = 1;
        bit randomize_user = 1;
        bit[{self.user_width-1}:0] default_user_value = 0;
        bit propagate_user = 1;
        bit check_user_consistency = 1;
    }} user_config_t;
    
    user_config_t cfg;
    
    // Components
    axi4_user_sequencer user_sequencer;
    axi4_user_driver user_driver;
    axi4_user_monitor user_monitor;
    
    // Analysis ports
    uvm_analysis_port #(axi4_user_transaction) user_ap;
    
    // Constructor
    function new(string name = "axi4_user_agent", uvm_component parent = null);
        super.new(name, parent);
        user_ap = new("user_ap", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if (!uvm_config_db#(user_config_t)::get(this, "", "user_config", cfg)) begin
            cfg = default_user_config();
        end
        
        // Create components based on active/passive mode
        if (cfg.active && is_active == UVM_ACTIVE) begin
            user_sequencer = axi4_user_sequencer::type_id::create("user_sequencer", this);
            user_driver = axi4_user_driver::type_id::create("user_driver", this);
        end
        
        user_monitor = axi4_user_monitor::type_id::create("user_monitor", this);
    endfunction
    
    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        if (cfg.active && is_active == UVM_ACTIVE) begin
            user_driver.seq_item_port.connect(user_sequencer.seq_item_export);
        end
        
        user_monitor.user_ap.connect(user_ap);
    endfunction
    
    // Default configuration
    function user_config_t default_user_config();
        user_config_t default_cfg;
        default_cfg.active = 1;
        default_cfg.enable_user_checking = 1;
        default_cfg.enable_user_generation = 1;
        default_cfg.randomize_user = 1;
        default_cfg.default_user_value = 0;
        default_cfg.propagate_user = 1;
        default_cfg.check_user_consistency = 1;
        return default_cfg;
    endfunction

endclass

// USER transaction class
class axi4_user_transaction extends uvm_sequence_item;
    `uvm_object_utils(axi4_user_transaction)
    
    // USER signal fields
    rand bit[{self.awuser_width-1}:0] awuser;
    rand bit[{self.wuser_width-1}:0] wuser[];  // Array for each beat
    rand bit[{self.buser_width-1}:0] buser;
    rand bit[{self.aruser_width-1}:0] aruser;
    rand bit[{self.ruser_width-1}:0] ruser[];  // Array for each beat
    
    // Transaction metadata
    bit[{self.addr_width-1}:0] addr;
    bit[{self.id_width-1}:0] id;
    bit[7:0] len;
    bit is_write;
    
    // USER signal attributes
    typedef enum {{
        USER_METADATA,      // General metadata
        USER_SIDEBAND,      // Sideband information
        USER_SECURITY,      // Security attributes
        USER_DEBUG,         // Debug information
        USER_CUSTOM         // Custom application
    }} user_type_e;
    
    rand user_type_e user_type;
    
    // Constraints
    constraint user_size_c {{
        wuser.size() == len + 1;
        ruser.size() == len + 1;
    }}
    
    // Constructor
    function new(string name = "axi4_user_transaction");
        super.new(name);
    endfunction
    
    // Post-randomize
    function void post_randomize();
        // Ensure arrays are properly sized
        if (is_write) begin
            wuser = new[len + 1];
            foreach (wuser[i]) begin
                wuser[i] = $urandom();
            end
        end else begin
            ruser = new[len + 1];
            foreach (ruser[i]) begin
                ruser[i] = $urandom();
            end
        end
    endfunction
    
    // Convert to string
    function string convert2string();
        string str = $sformatf("USER Transaction: %s\\n", is_write ? "Write" : "Read");
        
        if (is_write) begin
            str = {{str, $sformatf("  AWUSER: %0h\\n", awuser)}};
            foreach (wuser[i]) begin
                str = {{str, $sformatf("  WUSER[%0d]: %0h\\n", i, wuser[i])}};
            end
            str = {{str, $sformatf("  BUSER: %0h\\n", buser)}};
        end else begin
            str = {{str, $sformatf("  ARUSER: %0h\\n", aruser)}};
            foreach (ruser[i]) begin
                str = {{str, $sformatf("  RUSER[%0d]: %0h\\n", i, ruser[i])}};
            end
        end
        
        return str;
    endfunction

endclass

// USER driver class
class axi4_user_driver extends uvm_driver #(axi4_user_transaction);
    `uvm_component_utils(axi4_user_driver)
    
    // Virtual interface
    virtual axi4_if vif;
    
    // Configuration
    axi4_user_agent::user_config_t cfg;
    
    // Constructor
    function new(string name = "axi4_user_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
            
        if (!uvm_config_db#(axi4_user_agent::user_config_t)::get(this, "", "user_config", cfg))
            cfg = axi4_user_agent::default_user_config();
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        forever begin
            axi4_user_transaction trans;
            seq_item_port.get_next_item(trans);
            drive_user_signals(trans);
            seq_item_port.item_done();
        end
    endtask
    
    // Drive USER signals
    task drive_user_signals(axi4_user_transaction trans);
        if (trans.is_write) begin
            // Drive write USER signals
            fork
                drive_awuser(trans);
                drive_wuser(trans);
                monitor_buser(trans);
            join_any
        end else begin
            // Drive read USER signals
            fork
                drive_aruser(trans);
                monitor_ruser(trans);
            join_any
        end
    endtask
    
    // Drive AWUSER
    task drive_awuser(axi4_user_transaction trans);
        @(posedge vif.clk);
        while (!vif.awvalid) @(posedge vif.clk);
        
        vif.awuser <= trans.awuser;
        
        @(posedge vif.clk);
        while (!(vif.awvalid && vif.awready)) @(posedge vif.clk);
    endtask
    
    // Drive WUSER
    task drive_wuser(axi4_user_transaction trans);
        for (int i = 0; i <= trans.len; i++) begin
            @(posedge vif.clk);
            while (!vif.wvalid) @(posedge vif.clk);
            
            vif.wuser <= trans.wuser[i];
            
            @(posedge vif.clk);
            while (!(vif.wvalid && vif.wready)) @(posedge vif.clk);
        end
    endtask
    
    // Monitor BUSER
    task monitor_buser(axi4_user_transaction trans);
        @(posedge vif.clk);
        while (!(vif.bvalid && vif.bready)) @(posedge vif.clk);
        
        trans.buser = vif.buser;
    endtask
    
    // Drive ARUSER
    task drive_aruser(axi4_user_transaction trans);
        @(posedge vif.clk);
        while (!vif.arvalid) @(posedge vif.clk);
        
        vif.aruser <= trans.aruser;
        
        @(posedge vif.clk);
        while (!(vif.arvalid && vif.arready)) @(posedge vif.clk);
    endtask
    
    // Monitor RUSER
    task monitor_ruser(axi4_user_transaction trans);
        for (int i = 0; i <= trans.len; i++) begin
            @(posedge vif.clk);
            while (!(vif.rvalid && vif.rready)) @(posedge vif.clk);
            
            trans.ruser[i] = vif.ruser;
        end
    endtask

endclass

`endif // AXI4_USER_AGENT_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_user_agent.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_user_sequencer(self, output_dir: str):
        """Generate USER signal sequencer"""
        content = f"""// AXI4 VIP USER Signal Sequencer
// Generated: {datetime.datetime.now()}
// Sequences for USER signal generation

`ifndef AXI4_USER_SEQUENCER_SV
`define AXI4_USER_SEQUENCER_SV

class axi4_user_sequencer extends uvm_sequencer #(axi4_user_transaction);
    `uvm_component_utils(axi4_user_sequencer)
    
    // Configuration
    axi4_user_agent::user_config_t cfg;
    
    // USER pattern library
    bit[{self.user_width-1}:0] user_patterns[$];
    
    // Constructor
    function new(string name = "axi4_user_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(axi4_user_agent::user_config_t)::get(this, "", "user_config", cfg))
            cfg = axi4_user_agent::default_user_config();
        
        // Initialize pattern library
        init_user_patterns();
    endfunction
    
    // Initialize USER patterns
    function void init_user_patterns();
        // Add common patterns
        user_patterns.push_back({self.user_width{{1'b0}}});  // All zeros
        user_patterns.push_back({self.user_width{{1'b1}}});  // All ones
        user_patterns.push_back({self.user_width/2{{2'b01}}});  // Alternating
        user_patterns.push_back({self.user_width/2{{2'b10}}});  // Alternating inverse
        
        // Add specific patterns based on width
        if ({self.user_width} >= 16) begin
            user_patterns.push_back(16'hDEAD);
            user_patterns.push_back(16'hBEEF);
            user_patterns.push_back(16'hCAFE);
            user_patterns.push_back(16'h5A5A);
        end
    endfunction
    
    // Get pattern by index
    function bit[{self.user_width-1}:0] get_pattern(int index);
        if (index < user_patterns.size()) begin
            return user_patterns[index];
        end else begin
            return cfg.default_user_value;
        end
    endfunction
    
    // Add custom pattern
    function void add_pattern(bit[{self.user_width-1}:0] pattern);
        user_patterns.push_back(pattern);
    endfunction

endclass

// Base USER sequence
class axi4_user_base_sequence extends uvm_sequence #(axi4_user_transaction);
    `uvm_object_utils(axi4_user_base_sequence)
    
    // Sequencer handle
    axi4_user_sequencer p_sequencer;
    
    // Number of transactions
    rand int num_trans;
    
    // Constraints
    constraint num_trans_c {{
        num_trans inside {{[1:100]}};
    }}
    
    // Constructor
    function new(string name = "axi4_user_base_sequence");
        super.new(name);
    endfunction
    
    // Pre-start
    task pre_start();
        p_sequencer = axi4_user_sequencer::type_id::cast(m_sequencer);
    endtask

endclass

// Random USER sequence
class axi4_user_random_sequence extends axi4_user_base_sequence;
    `uvm_object_utils(axi4_user_random_sequence)
    
    function new(string name = "axi4_user_random_sequence");
        super.new(name);
    endfunction
    
    task body();
        for (int i = 0; i < num_trans; i++) begin
            axi4_user_transaction trans;
            trans = axi4_user_transaction::type_id::create("trans");
            
            start_item(trans);
            if (!trans.randomize()) begin
                `uvm_fatal(get_type_name(), "Randomization failed")
            end
            finish_item(trans);
        end
    endtask

endclass

// Pattern-based USER sequence
class axi4_user_pattern_sequence extends axi4_user_base_sequence;
    `uvm_object_utils(axi4_user_pattern_sequence)
    
    // Pattern mode
    typedef enum {{
        SEQUENTIAL,     // Use patterns in order
        RANDOM_PATTERN, // Random pattern selection
        INCREMENTAL,    // Incrementing values
        CUSTOM          // Custom pattern
    }} pattern_mode_e;
    
    rand pattern_mode_e mode;
    
    function new(string name = "axi4_user_pattern_sequence");
        super.new(name);
    endfunction
    
    task body();
        int pattern_index = 0;
        
        for (int i = 0; i < num_trans; i++) begin
            axi4_user_transaction trans;
            trans = axi4_user_transaction::type_id::create("trans");
            
            start_item(trans);
            
            // Set USER values based on mode
            case (mode)
                SEQUENTIAL: begin
                    trans.awuser = p_sequencer.get_pattern(pattern_index);
                    trans.aruser = p_sequencer.get_pattern(pattern_index);
                    pattern_index = (pattern_index + 1) % p_sequencer.user_patterns.size();
                end
                
                RANDOM_PATTERN: begin
                    int idx = $urandom_range(0, p_sequencer.user_patterns.size() - 1);
                    trans.awuser = p_sequencer.get_pattern(idx);
                    trans.aruser = p_sequencer.get_pattern(idx);
                end
                
                INCREMENTAL: begin
                    trans.awuser = i;
                    trans.aruser = i;
                end
                
                CUSTOM: begin
                    trans.awuser = generate_custom_pattern(i);
                    trans.aruser = generate_custom_pattern(i);
                end
            endcase
            
            // Randomize other fields
            if (!trans.randomize() with {{
                awuser == local::trans.awuser;
                aruser == local::trans.aruser;
            }}) begin
                `uvm_fatal(get_type_name(), "Randomization failed")
            end
            
            finish_item(trans);
        end
    endtask
    
    // Generate custom pattern
    function bit[{self.user_width-1}:0] generate_custom_pattern(int index);
        // Example: Use index as seed for pattern
        return (index << 8) | (index ^ 8'hAA);
    endfunction

endclass

// Metadata USER sequence
class axi4_user_metadata_sequence extends axi4_user_base_sequence;
    `uvm_object_utils(axi4_user_metadata_sequence)
    
    // Metadata encoding structure
    typedef struct packed {{
        bit[3:0] source_id;
        bit[3:0] dest_id;
        bit[3:0] priority;
        bit[3:0] flags;
    }} metadata_t;
    
    function new(string name = "axi4_user_metadata_sequence");
        super.new(name);
    endfunction
    
    task body();
        for (int i = 0; i < num_trans; i++) begin
            axi4_user_transaction trans;
            metadata_t metadata;
            
            trans = axi4_user_transaction::type_id::create("trans");
            
            // Generate metadata
            metadata.source_id = $urandom_range(0, {self.num_masters-1});
            metadata.dest_id = $urandom_range(0, {self.num_slaves-1});
            metadata.priority = $urandom_range(0, 15);
            metadata.flags = $urandom_range(0, 15);
            
            start_item(trans);
            
            // Encode metadata in USER signals
            trans.awuser = metadata;
            trans.aruser = metadata;
            trans.user_type = axi4_user_transaction::USER_METADATA;
            
            // Set WUSER/RUSER to propagate metadata
            trans.post_randomize();
            foreach (trans.wuser[j]) begin
                trans.wuser[j] = metadata;
            end
            foreach (trans.ruser[j]) begin
                trans.ruser[j] = metadata;
            end
            
            finish_item(trans);
        end
    endtask

endclass

// Security USER sequence
class axi4_user_security_sequence extends axi4_user_base_sequence;
    `uvm_object_utils(axi4_user_security_sequence)
    
    // Security attributes
    typedef struct packed {{
        bit[7:0] security_level;
        bit[3:0] access_rights;
        bit[3:0] encryption_type;
    }} security_attr_t;
    
    function new(string name = "axi4_user_security_sequence");
        super.new(name);
    endfunction
    
    task body();
        for (int i = 0; i < num_trans; i++) begin
            axi4_user_transaction trans;
            security_attr_t sec_attr;
            
            trans = axi4_user_transaction::type_id::create("trans");
            
            // Generate security attributes
            sec_attr.security_level = $urandom_range(0, 255);
            sec_attr.access_rights = $urandom_range(0, 15);
            sec_attr.encryption_type = $urandom_range(0, 15);
            
            start_item(trans);
            
            // Encode security in USER signals
            trans.awuser = sec_attr;
            trans.aruser = sec_attr;
            trans.user_type = axi4_user_transaction::USER_SECURITY;
            
            // Propagate security through burst
            trans.post_randomize();
            foreach (trans.wuser[j]) begin
                trans.wuser[j] = sec_attr;
            end
            
            finish_item(trans);
        end
    endtask

endclass

// Debug USER sequence
class axi4_user_debug_sequence extends axi4_user_base_sequence;
    `uvm_object_utils(axi4_user_debug_sequence)
    
    // Debug information
    typedef struct packed {{
        bit[7:0] timestamp;
        bit[3:0] debug_id;
        bit[3:0] trace_level;
    }} debug_info_t;
    
    function new(string name = "axi4_user_debug_sequence");
        super.new(name);
    endfunction
    
    task body();
        for (int i = 0; i < num_trans; i++) begin
            axi4_user_transaction trans;
            debug_info_t debug_info;
            
            trans = axi4_user_transaction::type_id::create("trans");
            
            // Generate debug information
            debug_info.timestamp = $time & 8'hFF;
            debug_info.debug_id = i & 4'hF;
            debug_info.trace_level = $urandom_range(0, 15);
            
            start_item(trans);
            
            // Encode debug info in USER signals
            trans.awuser = debug_info;
            trans.aruser = debug_info;
            trans.user_type = axi4_user_transaction::USER_DEBUG;
            
            finish_item(trans);
        end
    endtask

endclass

`endif // AXI4_USER_SEQUENCER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_user_sequencer.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_user_monitor(self, output_dir: str):
        """Generate USER signal monitor"""
        content = f"""// AXI4 VIP USER Signal Monitor
// Generated: {datetime.datetime.now()}
// Monitors USER signal behavior and compliance

`ifndef AXI4_USER_MONITOR_SV
`define AXI4_USER_MONITOR_SV

class axi4_user_monitor extends uvm_monitor;
    `uvm_component_utils(axi4_user_monitor)
    
    // Virtual interface
    virtual axi4_if vif;
    
    // Analysis ports
    uvm_analysis_port #(axi4_user_transaction) user_ap;
    uvm_analysis_port #(axi4_user_event) event_ap;
    
    // Configuration
    axi4_user_agent::user_config_t cfg;
    
    // Tracking structures
    typedef struct {{
        bit[{self.awuser_width-1}:0] awuser;
        bit[{self.aruser_width-1}:0] aruser;
        realtime timestamp;
        bit valid;
    }} user_track_t;
    
    user_track_t active_writes[bit[{self.id_width-1}:0]];
    user_track_t active_reads[bit[{self.id_width-1}:0]];
    
    // Statistics
    int total_transactions;
    int user_mismatches;
    int user_violations;
    
    // USER value tracking
    int awuser_values[bit[{self.awuser_width-1}:0]];
    int wuser_values[bit[{self.wuser_width-1}:0]];
    int buser_values[bit[{self.buser_width-1}:0]];
    int aruser_values[bit[{self.aruser_width-1}:0]];
    int ruser_values[bit[{self.ruser_width-1}:0]];
    
    // Constructor
    function new(string name = "axi4_user_monitor", uvm_component parent = null);
        super.new(name, parent);
        user_ap = new("user_ap", this);
        event_ap = new("event_ap", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
            
        if (!uvm_config_db#(axi4_user_agent::user_config_t)::get(this, "", "user_config", cfg))
            cfg = axi4_user_agent::default_user_config();
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        fork
            monitor_write_channels();
            monitor_read_channels();
            check_user_consistency();
            collect_user_statistics();
        join
    endtask
    
    // Monitor write channels
    task monitor_write_channels();
        forever begin
            fork
                monitor_aw_channel();
                monitor_w_channel();
                monitor_b_channel();
            join_any
        end
    endtask
    
    // Monitor AW channel
    task monitor_aw_channel();
        forever begin
            @(posedge vif.clk);
            
            if (vif.awvalid && vif.awready) begin
                axi4_user_event evt = new();
                evt.channel = "AW";
                evt.id = vif.awid;
                evt.user_value = vif.awuser;
                evt.timestamp = $realtime;
                
                // Track for consistency checking
                user_track_t track;
                track.awuser = vif.awuser;
                track.timestamp = $realtime;
                track.valid = 1;
                active_writes[vif.awid] = track;
                
                // Update statistics
                awuser_values[vif.awuser]++;
                
                // Send event
                event_ap.write(evt);
                
                `uvm_info(get_type_name(), 
                         $sformatf("AW: ID=%0h, AWUSER=%0h", vif.awid, vif.awuser), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Monitor W channel
    task monitor_w_channel();
        forever begin
            @(posedge vif.clk);
            
            if (vif.wvalid && vif.wready) begin
                axi4_user_event evt = new();
                evt.channel = "W";
                evt.user_value = vif.wuser;
                evt.timestamp = $realtime;
                evt.last = vif.wlast;
                
                // Update statistics
                wuser_values[vif.wuser]++;
                
                // Check for consistency if configured
                if (cfg.check_user_consistency && cfg.propagate_user) begin
                    check_w_user_consistency(vif.wuser);
                end
                
                // Send event
                event_ap.write(evt);
                
                `uvm_info(get_type_name(), 
                         $sformatf("W: WUSER=%0h, LAST=%0b", vif.wuser, vif.wlast), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Monitor B channel
    task monitor_b_channel();
        forever begin
            @(posedge vif.clk);
            
            if (vif.bvalid && vif.bready) begin
                axi4_user_event evt = new();
                evt.channel = "B";
                evt.id = vif.bid;
                evt.user_value = vif.buser;
                evt.timestamp = $realtime;
                evt.resp = vif.bresp;
                
                // Update statistics
                buser_values[vif.buser]++;
                total_transactions++;
                
                // Create complete write transaction
                if (active_writes.exists(vif.bid)) begin
                    axi4_user_transaction trans = new();
                    trans.is_write = 1;
                    trans.id = vif.bid;
                    trans.awuser = active_writes[vif.bid].awuser;
                    trans.buser = vif.buser;
                    
                    // Send transaction
                    user_ap.write(trans);
                    
                    // Clear tracking
                    active_writes.delete(vif.bid);
                end
                
                // Send event
                event_ap.write(evt);
                
                `uvm_info(get_type_name(), 
                         $sformatf("B: ID=%0h, BUSER=%0h, RESP=%0h", 
                                  vif.bid, vif.buser, vif.bresp), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Monitor read channels
    task monitor_read_channels();
        forever begin
            fork
                monitor_ar_channel();
                monitor_r_channel();
            join_any
        end
    endtask
    
    // Monitor AR channel
    task monitor_ar_channel();
        forever begin
            @(posedge vif.clk);
            
            if (vif.arvalid && vif.arready) begin
                axi4_user_event evt = new();
                evt.channel = "AR";
                evt.id = vif.arid;
                evt.user_value = vif.aruser;
                evt.timestamp = $realtime;
                
                // Track for consistency checking
                user_track_t track;
                track.aruser = vif.aruser;
                track.timestamp = $realtime;
                track.valid = 1;
                active_reads[vif.arid] = track;
                
                // Update statistics
                aruser_values[vif.aruser]++;
                
                // Send event
                event_ap.write(evt);
                
                `uvm_info(get_type_name(), 
                         $sformatf("AR: ID=%0h, ARUSER=%0h", vif.arid, vif.aruser), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Monitor R channel
    task monitor_r_channel();
        bit[{self.ruser_width-1}:0] ruser_beats[$];
        bit[{self.id_width-1}:0] current_id;
        
        forever begin
            @(posedge vif.clk);
            
            if (vif.rvalid && vif.rready) begin
                axi4_user_event evt = new();
                evt.channel = "R";
                evt.id = vif.rid;
                evt.user_value = vif.ruser;
                evt.timestamp = $realtime;
                evt.last = vif.rlast;
                evt.resp = vif.rresp;
                
                // Update statistics
                ruser_values[vif.ruser]++;
                
                // Collect RUSER for complete transaction
                if (current_id != vif.rid) begin
                    ruser_beats.delete();
                    current_id = vif.rid;
                end
                ruser_beats.push_back(vif.ruser);
                
                // Send event
                event_ap.write(evt);
                
                // Create complete read transaction on last
                if (vif.rlast) begin
                    total_transactions++;
                    
                    if (active_reads.exists(vif.rid)) begin
                        axi4_user_transaction trans = new();
                        trans.is_write = 0;
                        trans.id = vif.rid;
                        trans.aruser = active_reads[vif.rid].aruser;
                        trans.len = ruser_beats.size() - 1;
                        trans.ruser = new[ruser_beats.size()];
                        foreach (ruser_beats[i]) begin
                            trans.ruser[i] = ruser_beats[i];
                        end
                        
                        // Send transaction
                        user_ap.write(trans);
                        
                        // Clear tracking
                        active_reads.delete(vif.rid);
                    end
                    
                    ruser_beats.delete();
                end
                
                `uvm_info(get_type_name(), 
                         $sformatf("R: ID=%0h, RUSER=%0h, LAST=%0b, RESP=%0h", 
                                  vif.rid, vif.ruser, vif.rlast, vif.rresp), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Check W channel USER consistency
    function void check_w_user_consistency(bit[{self.wuser_width-1}:0] wuser);
        // Simple check - could be enhanced based on requirements
        // For example, check if WUSER matches AWUSER pattern
    endfunction
    
    // Check USER signal consistency
    task check_user_consistency();
        forever begin
            #1us;  // Check periodically
            
            // Check for orphaned transactions
            foreach (active_writes[id]) begin
                if ($realtime - active_writes[id].timestamp > 10us) begin
                    `uvm_warning(get_type_name(), 
                                $sformatf("Write transaction ID=%0h incomplete after 10us", id))
                    user_violations++;
                end
            end
            
            foreach (active_reads[id]) begin
                if ($realtime - active_reads[id].timestamp > 10us) begin
                    `uvm_warning(get_type_name(), 
                                $sformatf("Read transaction ID=%0h incomplete after 10us", id))
                    user_violations++;
                end
            end
        end
    endtask
    
    // Collect USER statistics
    task collect_user_statistics();
        forever begin
            #10us;  // Update statistics periodically
            
            // Could analyze USER value patterns, frequency, etc.
        end
    endtask
    
    // Get USER statistics report
    function string get_user_stats();
        string stats = "\\n=== USER Signal Statistics ===\\n";
        
        stats = {{stats, $sformatf("Total Transactions: %0d\\n", total_transactions)}};
        stats = {{stats, $sformatf("USER Mismatches: %0d\\n", user_mismatches)}};
        stats = {{stats, $sformatf("USER Violations: %0d\\n", user_violations)}};
        
        // Most common USER values
        stats = {{stats, "\\nMost Common USER Values:\\n"}};
        
        // AWUSER
        int max_awuser_count = 0;
        bit[{self.awuser_width-1}:0] most_common_awuser;
        foreach (awuser_values[val]) begin
            if (awuser_values[val] > max_awuser_count) begin
                max_awuser_count = awuser_values[val];
                most_common_awuser = val;
            end
        end
        if (max_awuser_count > 0) begin
            stats = {{stats, $sformatf("  AWUSER: %0h (count=%0d)\\n", 
                                      most_common_awuser, max_awuser_count)}};
        end
        
        // Similar for other channels...
        
        return stats;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_user_stats(), UVM_LOW)
    endfunction

endclass

// USER event class
class axi4_user_event extends uvm_sequence_item;
    `uvm_object_utils(axi4_user_event)
    
    string channel;  // AW, W, B, AR, R
    bit[{self.id_width-1}:0] id;
    bit[{self.user_width-1}:0] user_value;
    realtime timestamp;
    bit last;
    bit[1:0] resp;
    
    function new(string name = "axi4_user_event");
        super.new(name);
    endfunction
    
    function string convert2string();
        return $sformatf("USER Event: %s channel, ID=%0h, USER=%0h, time=%0t",
                        channel, id, user_value, timestamp);
    endfunction

endclass

`endif // AXI4_USER_MONITOR_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_user_monitor.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_user_scoreboard(self, output_dir: str):
        """Generate USER signal scoreboard"""
        content = f"""// AXI4 VIP USER Signal Scoreboard
// Generated: {datetime.datetime.now()}
// Checks USER signal propagation and consistency

`ifndef AXI4_USER_SCOREBOARD_SV
`define AXI4_USER_SCOREBOARD_SV

class axi4_user_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(axi4_user_scoreboard)
    
    // Analysis exports
    uvm_analysis_imp_master #(axi4_user_transaction, axi4_user_scoreboard) master_export;
    uvm_analysis_imp_slave #(axi4_user_transaction, axi4_user_scoreboard) slave_export;
    
    // Configuration
    axi4_user_agent::user_config_t cfg;
    
    // Transaction queues
    axi4_user_transaction master_queue[bit[{self.id_width-1}:0]][$];
    axi4_user_transaction slave_queue[bit[{self.id_width-1}:0]][$];
    
    // Checking statistics
    int total_checks;
    int user_matches;
    int user_mismatches;
    int propagation_errors;
    
    // USER value correlation
    typedef struct {{
        bit[{self.user_width-1}:0] master_user;
        bit[{self.user_width-1}:0] slave_user;
        int count;
    }} user_correlation_t;
    
    user_correlation_t correlations[$];
    
    // Constructor
    function new(string name = "axi4_user_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        master_export = new("master_export", this);
        slave_export = new("slave_export", this);
        
        if (!uvm_config_db#(axi4_user_agent::user_config_t)::get(this, "", "user_config", cfg))
            cfg = axi4_user_agent::default_user_config();
    endfunction
    
    // Master write
    function void write_master(axi4_user_transaction trans);
        bit[{self.id_width-1}:0] id = trans.id;
        
        `uvm_info(get_type_name(), 
                 $sformatf("Master transaction: ID=%0h, %s", 
                          id, trans.is_write ? "Write" : "Read"), 
                 UVM_HIGH)
        
        master_queue[id].push_back(trans);
        
        // Try to match with slave transaction
        check_for_match(id);
    endfunction
    
    // Slave write
    function void write_slave(axi4_user_transaction trans);
        bit[{self.id_width-1}:0] id = trans.id;
        
        `uvm_info(get_type_name(), 
                 $sformatf("Slave transaction: ID=%0h, %s", 
                          id, trans.is_write ? "Write" : "Read"), 
                 UVM_HIGH)
        
        slave_queue[id].push_back(trans);
        
        // Try to match with master transaction
        check_for_match(id);
    endfunction
    
    // Check for matching transactions
    function void check_for_match(bit[{self.id_width-1}:0] id);
        while (master_queue[id].size() > 0 && slave_queue[id].size() > 0) begin
            axi4_user_transaction master_trans = master_queue[id].pop_front();
            axi4_user_transaction slave_trans = slave_queue[id].pop_front();
            
            compare_user_signals(master_trans, slave_trans);
        end
    endfunction
    
    // Compare USER signals
    function void compare_user_signals(axi4_user_transaction master_trans,
                                     axi4_user_transaction slave_trans);
        bit match = 1;
        total_checks++;
        
        if (master_trans.is_write != slave_trans.is_write) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Transaction type mismatch: master=%s, slave=%s",
                               master_trans.is_write ? "Write" : "Read",
                               slave_trans.is_write ? "Write" : "Read"))
            return;
        end
        
        if (master_trans.is_write) begin
            // Check write USER signals
            match &= check_write_user(master_trans, slave_trans);
        end else begin
            // Check read USER signals
            match &= check_read_user(master_trans, slave_trans);
        end
        
        if (match) begin
            user_matches++;
            `uvm_info(get_type_name(), 
                     $sformatf("USER match: ID=%0h", master_trans.id), 
                     UVM_MEDIUM)
        end else begin
            user_mismatches++;
        end
        
        // Update correlation
        update_correlation(master_trans, slave_trans);
    endfunction
    
    // Check write USER signals
    function bit check_write_user(axi4_user_transaction master_trans,
                                axi4_user_transaction slave_trans);
        bit match = 1;
        
        // Check AWUSER propagation
        if (cfg.propagate_user) begin
            if (master_trans.awuser !== slave_trans.awuser) begin
                `uvm_error(get_type_name(), 
                          $sformatf("AWUSER mismatch: master=%0h, slave=%0h",
                                   master_trans.awuser, slave_trans.awuser))
                match = 0;
                propagation_errors++;
            end
        end
        
        // Check WUSER propagation
        if (master_trans.wuser.size() != slave_trans.wuser.size()) begin
            `uvm_error(get_type_name(), 
                      $sformatf("WUSER size mismatch: master=%0d, slave=%0d",
                               master_trans.wuser.size(), slave_trans.wuser.size()))
            match = 0;
        end else if (cfg.propagate_user) begin
            foreach (master_trans.wuser[i]) begin
                if (master_trans.wuser[i] !== slave_trans.wuser[i]) begin
                    `uvm_error(get_type_name(), 
                              $sformatf("WUSER[%0d] mismatch: master=%0h, slave=%0h",
                                       i, master_trans.wuser[i], slave_trans.wuser[i]))
                    match = 0;
                    propagation_errors++;
                end
            end
        end
        
        // BUSER is typically generated by slave, so no comparison needed
        // unless there's a specific propagation requirement
        
        return match;
    endfunction
    
    // Check read USER signals
    function bit check_read_user(axi4_user_transaction master_trans,
                               axi4_user_transaction slave_trans);
        bit match = 1;
        
        // Check ARUSER propagation
        if (cfg.propagate_user) begin
            if (master_trans.aruser !== slave_trans.aruser) begin
                `uvm_error(get_type_name(), 
                          $sformatf("ARUSER mismatch: master=%0h, slave=%0h",
                                   master_trans.aruser, slave_trans.aruser))
                match = 0;
                propagation_errors++;
            end
        end
        
        // RUSER is typically generated by slave based on ARUSER
        // Check if there's a defined relationship
        if (cfg.check_user_consistency) begin
            // Example: Check if RUSER is derived from ARUSER
            foreach (slave_trans.ruser[i]) begin
                if (!check_ruser_consistency(master_trans.aruser, slave_trans.ruser[i])) begin
                    `uvm_warning(get_type_name(), 
                                $sformatf("RUSER[%0d] inconsistent with ARUSER", i))
                    // This might be a warning rather than error
                end
            end
        end
        
        return match;
    endfunction
    
    // Check RUSER consistency with ARUSER
    function bit check_ruser_consistency(bit[{self.aruser_width-1}:0] aruser,
                                       bit[{self.ruser_width-1}:0] ruser);
        // Define consistency rules based on implementation
        // Example: RUSER should contain ARUSER in lower bits
        if ({self.ruser_width} >= {self.aruser_width}) begin
            return (ruser[{self.aruser_width-1}:0] == aruser);
        end
        return 1;  // No check if RUSER is smaller
    endfunction
    
    // Update correlation statistics
    function void update_correlation(axi4_user_transaction master_trans,
                                   axi4_user_transaction slave_trans);
        user_correlation_t corr;
        bit found = 0;
        
        // Use AWUSER/ARUSER as representative
        corr.master_user = master_trans.is_write ? master_trans.awuser : master_trans.aruser;
        corr.slave_user = slave_trans.is_write ? slave_trans.awuser : slave_trans.aruser;
        
        // Check if correlation exists
        foreach (correlations[i]) begin
            if (correlations[i].master_user == corr.master_user &&
                correlations[i].slave_user == corr.slave_user) begin
                correlations[i].count++;
                found = 1;
                break;
            end
        end
        
        if (!found) begin
            corr.count = 1;
            correlations.push_back(corr);
        end
    endfunction
    
    // Get scoreboard report
    function string get_scoreboard_report();
        string report = "\\n=== USER Scoreboard Report ===\\n";
        
        report = {{report, $sformatf("Total Checks: %0d\\n", total_checks)}};
        report = {{report, $sformatf("USER Matches: %0d\\n", user_matches)}};
        report = {{report, $sformatf("USER Mismatches: %0d\\n", user_mismatches)}};
        report = {{report, $sformatf("Propagation Errors: %0d\\n", propagation_errors)}};
        
        if (total_checks > 0) begin
            real match_rate = real'(user_matches) / real'(total_checks) * 100.0;
            report = {{report, $sformatf("Match Rate: %0.1f%%\\n", match_rate)}};
        end
        
        // Top correlations
        if (correlations.size() > 0) begin
            report = {{report, "\\nTop USER Correlations:\\n"}};
            
            // Sort by count
            correlations.sort() with (item.count);
            
            for (int i = correlations.size() - 1; i >= 0 && i >= correlations.size() - 5; i--) begin
                report = {{report, $sformatf("  Master USER %0h -> Slave USER %0h: %0d times\\n",
                                            correlations[i].master_user,
                                            correlations[i].slave_user,
                                            correlations[i].count)}};
            end
        end
        
        return report;
    endfunction
    
    // Check phase
    function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        
        // Check for unmatched transactions
        foreach (master_queue[id]) begin
            if (master_queue[id].size() > 0) begin
                `uvm_error(get_type_name(), 
                          $sformatf("Unmatched master transactions for ID %0h: %0d",
                                   id, master_queue[id].size()))
            end
        end
        
        foreach (slave_queue[id]) begin
            if (slave_queue[id].size() > 0) begin
                `uvm_error(get_type_name(), 
                          $sformatf("Unmatched slave transactions for ID %0h: %0d",
                                   id, slave_queue[id].size()))
            end
        end
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_scoreboard_report(), UVM_LOW)
        
        if (user_mismatches > 0 || propagation_errors > 0) begin
            `uvm_error(get_type_name(), "USER scoreboard detected errors!")
        end
    endfunction

endclass

`endif // AXI4_USER_SCOREBOARD_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_user_scoreboard.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_user_coverage(self, output_dir: str):
        """Generate USER signal coverage"""
        content = f"""// AXI4 VIP USER Signal Coverage
// Generated: {datetime.datetime.now()}
// Coverage model for USER signal usage patterns

`ifndef AXI4_USER_COVERAGE_SV
`define AXI4_USER_COVERAGE_SV

class axi4_user_coverage extends uvm_subscriber #(axi4_user_transaction);
    `uvm_component_utils(axi4_user_coverage)
    
    // Transaction handle
    axi4_user_transaction trans;
    
    // Coverage groups
    covergroup cg_user_values;
        option.per_instance = 1;
        option.name = "user_values";
        
        // AWUSER coverage
        awuser_cp: coverpoint trans.awuser {{
            bins zero = {{0}};
            bins low = {{[1:{2**{self.awuser_width}/4-1}]}};
            bins mid_low = {{[{2**{self.awuser_width}/4}:{2**{self.awuser_width}/2-1}]}};
            bins mid_high = {{[{2**{self.awuser_width}/2}:{3*2**{self.awuser_width}/4-1}]}};
            bins high = {{[{3*2**{self.awuser_width}/4}:{2**{self.awuser_width}-2}]}};
            bins max = {{{2**{self.awuser_width}-1}}};
        }}
        
        // ARUSER coverage
        aruser_cp: coverpoint trans.aruser {{
            bins zero = {{0}};
            bins low = {{[1:{2**{self.aruser_width}/4-1}]}};
            bins mid_low = {{[{2**{self.aruser_width}/4}:{2**{self.aruser_width}/2-1}]}};
            bins mid_high = {{[{2**{self.aruser_width}/2}:{3*2**{self.aruser_width}/4-1}]}};
            bins high = {{[{3*2**{self.aruser_width}/4}:{2**{self.aruser_width}-2}]}};
            bins max = {{{2**{self.aruser_width}-1}}};
        }}
        
        // BUSER coverage (response)
        buser_cp: coverpoint trans.buser iff (trans.is_write) {{
            bins zero = {{0}};
            bins non_zero = {{[1:{2**{self.buser_width}-1}]}};
        }}
        
        // Transaction type
        trans_type: coverpoint trans.is_write {{
            bins write = {{1}};
            bins read = {{0}};
        }}
        
        // Cross coverage
        awuser_x_type: cross awuser_cp, trans_type iff (trans.is_write);
        aruser_x_type: cross aruser_cp, trans_type iff (!trans.is_write);
    endgroup
    
    covergroup cg_user_patterns;
        option.per_instance = 1;
        option.name = "user_patterns";
        
        // USER type patterns
        user_type_cp: coverpoint trans.user_type {{
            bins metadata = {{axi4_user_transaction::USER_METADATA}};
            bins sideband = {{axi4_user_transaction::USER_SIDEBAND}};
            bins security = {{axi4_user_transaction::USER_SECURITY}};
            bins debug = {{axi4_user_transaction::USER_DEBUG}};
            bins custom = {{axi4_user_transaction::USER_CUSTOM}};
        }}
        
        // Pattern detection
        pattern_cp: coverpoint detect_pattern(trans) {{
            bins constant = {{PATTERN_CONSTANT}};
            bins incremental = {{PATTERN_INCREMENTAL}};
            bins alternating = {{PATTERN_ALTERNATING}};
            bins random = {{PATTERN_RANDOM}};
        }}
        
        // USER propagation
        propagation_cp: coverpoint check_propagation(trans) {{
            bins consistent = {{1}};
            bins modified = {{0}};
        }}
        
        // Cross coverage
        type_x_pattern: cross user_type_cp, pattern_cp;
    endgroup
    
    covergroup cg_user_transitions;
        option.per_instance = 1;
        option.name = "user_transitions";
        
        // AWUSER transitions
        awuser_trans: coverpoint trans.awuser {{
            bins stable = (0 => 0);
            bins inc = ([0:{2**{self.awuser_width}-2}] => [1:{2**{self.awuser_width}-1}]);
            bins dec = ([1:{2**{self.awuser_width}-1}] => [0:{2**{self.awuser_width}-2}]);
            bins toggle = (0 => {2**{self.awuser_width}-1}), ({2**{self.awuser_width}-1} => 0);
        }}
        
        // ARUSER transitions
        aruser_trans: coverpoint trans.aruser {{
            bins stable = (0 => 0);
            bins inc = ([0:{2**{self.aruser_width}-2}] => [1:{2**{self.aruser_width}-1}]);
            bins dec = ([1:{2**{self.aruser_width}-1}] => [0:{2**{self.aruser_width}-2}]);
            bins toggle = (0 => {2**{self.aruser_width}-1}), ({2**{self.aruser_width}-1} => 0);
        }}
    endgroup
    
    covergroup cg_user_burst_patterns;
        option.per_instance = 1;
        option.name = "user_burst_patterns";
        
        // Burst length vs USER consistency
        burst_len: coverpoint trans.len {{
            bins single = {{0}};
            bins short = {{[1:3]}};
            bins medium = {{[4:15]}};
            bins long = {{[16:255]}};
        }}
        
        // WUSER consistency in burst
        wuser_consistent: coverpoint check_wuser_consistency(trans) iff (trans.is_write) {{
            bins all_same = {{1}};
            bins varying = {{0}};
        }}
        
        // RUSER consistency in burst
        ruser_consistent: coverpoint check_ruser_consistency(trans) iff (!trans.is_write) {{
            bins all_same = {{1}};
            bins varying = {{0}};
        }}
        
        // Cross coverage
        write_burst_consistency: cross burst_len, wuser_consistent iff (trans.is_write);
        read_burst_consistency: cross burst_len, ruser_consistent iff (!trans.is_write);
    endgroup
    
    covergroup cg_user_correlation;
        option.per_instance = 1;
        option.name = "user_correlation";
        
        // USER vs transaction attributes
        user_vs_id: coverpoint trans.id {{
            bins id[16] = {{[0:15]}};
        }}
        
        user_vs_addr_region: coverpoint trans.addr[31:28] {{
            bins region[16] = {{[0:15]}};
        }}
        
        // Cross coverage
        awuser_x_id: cross trans.awuser[3:0], user_vs_id iff (trans.is_write);
        aruser_x_region: cross trans.aruser[3:0], user_vs_addr_region iff (!trans.is_write);
    endgroup
    
    // Pattern types
    typedef enum {{
        PATTERN_CONSTANT,
        PATTERN_INCREMENTAL,
        PATTERN_ALTERNATING,
        PATTERN_RANDOM
    }} pattern_type_e;
    
    // Previous transaction for transition coverage
    axi4_user_transaction prev_trans;
    
    // Constructor
    function new(string name = "axi4_user_coverage", uvm_component parent = null);
        super.new(name, parent);
        cg_user_values = new();
        cg_user_patterns = new();
        cg_user_transitions = new();
        cg_user_burst_patterns = new();
        cg_user_correlation = new();
    endfunction
    
    // Write method
    function void write(axi4_user_transaction t);
        trans = t;
        
        // Sample all coverage groups
        cg_user_values.sample();
        cg_user_patterns.sample();
        cg_user_burst_patterns.sample();
        cg_user_correlation.sample();
        
        // Sample transitions if we have previous transaction
        if (prev_trans != null) begin
            cg_user_transitions.sample();
        end
        
        prev_trans = trans;
    endfunction
    
    // Detect pattern in USER signals
    function pattern_type_e detect_pattern(axi4_user_transaction trans);
        if (trans.is_write && trans.wuser.size() > 1) begin
            // Check WUSER pattern
            bit all_same = 1;
            bit incremental = 1;
            
            for (int i = 1; i < trans.wuser.size(); i++) begin
                if (trans.wuser[i] != trans.wuser[0]) all_same = 0;
                if (trans.wuser[i] != trans.wuser[i-1] + 1) incremental = 0;
            end
            
            if (all_same) return PATTERN_CONSTANT;
            if (incremental) return PATTERN_INCREMENTAL;
            
            // Check alternating
            if (trans.wuser.size() > 2) begin
                bit alternating = 1;
                for (int i = 2; i < trans.wuser.size(); i++) begin
                    if (trans.wuser[i] != trans.wuser[i-2]) alternating = 0;
                end
                if (alternating) return PATTERN_ALTERNATING;
            end
        end
        
        return PATTERN_RANDOM;
    endfunction
    
    // Check propagation consistency
    function bit check_propagation(axi4_user_transaction trans);
        // Check if USER signals are propagated consistently
        if (trans.is_write) begin
            // For writes, check if AWUSER relates to WUSER
            foreach (trans.wuser[i]) begin
                if (trans.wuser[i] != trans.awuser) return 0;
            end
        end
        return 1;
    endfunction
    
    // Check WUSER consistency
    function bit check_wuser_consistency(axi4_user_transaction trans);
        if (!trans.is_write || trans.wuser.size() == 0) return 1;
        
        bit[{self.wuser_width-1}:0] first_wuser = trans.wuser[0];
        foreach (trans.wuser[i]) begin
            if (trans.wuser[i] != first_wuser) return 0;
        end
        return 1;
    endfunction
    
    // Check RUSER consistency
    function bit check_ruser_consistency(axi4_user_transaction trans);
        if (trans.is_write || trans.ruser.size() == 0) return 1;
        
        bit[{self.ruser_width-1}:0] first_ruser = trans.ruser[0];
        foreach (trans.ruser[i]) begin
            if (trans.ruser[i] != first_ruser) return 0;
        end
        return 1;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), 
                 $sformatf("USER Coverage Summary:\\n" +
                          "  Values: %0.2f%%\\n" +
                          "  Patterns: %0.2f%%\\n" +
                          "  Transitions: %0.2f%%\\n" +
                          "  Burst Patterns: %0.2f%%\\n" +
                          "  Correlations: %0.2f%%",
                          cg_user_values.get_coverage(),
                          cg_user_patterns.get_coverage(),
                          cg_user_transitions.get_coverage(),
                          cg_user_burst_patterns.get_coverage(),
                          cg_user_correlation.get_coverage()), 
                 UVM_LOW)
    endfunction

endclass

`endif // AXI4_USER_COVERAGE_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_user_coverage.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_user_protocol_handler(self, output_dir: str):
        """Generate USER protocol handler"""
        content = f"""// AXI4 VIP USER Protocol Handler
// Generated: {datetime.datetime.now()}
// Handles USER signal protocol rules and transformations

`ifndef AXI4_USER_PROTOCOL_HANDLER_SV
`define AXI4_USER_PROTOCOL_HANDLER_SV

class axi4_user_protocol_handler extends uvm_component;
    `uvm_component_utils(axi4_user_protocol_handler)
    
    // Configuration
    axi4_user_agent::user_config_t cfg;
    
    // USER signal processing modes
    typedef enum {{
        USER_PASSTHROUGH,      // Pass USER signals unchanged
        USER_GENERATE,         // Generate USER signals
        USER_TRANSFORM,        // Transform USER signals
        USER_VALIDATE,         // Validate USER signals
        USER_ENCODE_DECODE     // Encode/decode information
    }} user_mode_e;
    
    user_mode_e mode = USER_PASSTHROUGH;
    
    // USER encoding schemes
    typedef struct {{
        bit[3:0] format_version;
        bit[3:0] encoding_type;
        bit[7:0] payload_size;
    }} user_format_t;
    
    // Transformation functions
    typedef bit[{self.user_width-1}:0] user_transform_f(bit[{self.user_width-1}:0] input);
    user_transform_f transform_functions[string];
    
    // Validation rules
    typedef bit user_validate_f(bit[{self.user_width-1}:0] user_val);
    user_validate_f validation_rules[string];
    
    // Statistics
    int transforms_applied;
    int validations_passed;
    int validations_failed;
    int encodings_performed;
    int decodings_performed;
    
    // Constructor
    function new(string name = "axi4_user_protocol_handler", uvm_component parent = null);
        super.new(name, parent);
        init_default_functions();
    endfunction
    
    // Initialize default functions
    function void init_default_functions();
        // Default transformation functions
        register_transform("identity", transform_identity);
        register_transform("invert", transform_invert);
        register_transform("rotate_left", transform_rotate_left);
        register_transform("rotate_right", transform_rotate_right);
        register_transform("xor_mask", transform_xor_mask);
        
        // Default validation rules
        register_validation("non_zero", validate_non_zero);
        register_validation("even_parity", validate_even_parity);
        register_validation("range_check", validate_range);
        register_validation("format_check", validate_format);
    endfunction
    
    // Process USER signal based on mode
    function bit[{self.user_width-1}:0] process_user_signal(
        bit[{self.user_width-1}:0] input_user,
        string context = "");
        
        bit[{self.user_width-1}:0] output_user = input_user;
        
        case (mode)
            USER_PASSTHROUGH: begin
                // No processing
            end
            
            USER_GENERATE: begin
                output_user = generate_user_value(context);
            end
            
            USER_TRANSFORM: begin
                output_user = apply_transforms(input_user);
                transforms_applied++;
            end
            
            USER_VALIDATE: begin
                if (!validate_user_value(input_user)) begin
                    `uvm_error(get_type_name(), 
                              $sformatf("USER validation failed: %0h", input_user))
                    validations_failed++;
                end else begin
                    validations_passed++;
                end
            end
            
            USER_ENCODE_DECODE: begin
                // Context determines encode or decode
                if (context == "encode") begin
                    output_user = encode_user_data(input_user);
                    encodings_performed++;
                end else begin
                    output_user = decode_user_data(input_user);
                    decodings_performed++;
                end
            end
        endcase
        
        return output_user;
    endfunction
    
    // Generate USER value
    function bit[{self.user_width-1}:0] generate_user_value(string context);
        bit[{self.user_width-1}:0] user_val;
        
        if (cfg.randomize_user) begin
            user_val = $urandom();
        end else begin
            user_val = cfg.default_user_value;
        end
        
        // Apply context-specific generation
        case (context)
            "metadata": user_val = generate_metadata_user();
            "security": user_val = generate_security_user();
            "debug": user_val = generate_debug_user();
            default: ;  // Use random/default
        endcase
        
        return user_val;
    endfunction
    
    // Generate metadata USER
    function bit[{self.user_width-1}:0] generate_metadata_user();
        typedef struct packed {{
            bit[3:0] priority;
            bit[3:0] stream_id;
            bit[7:0] sequence_num;
        }} metadata_user_t;
        
        metadata_user_t meta;
        meta.priority = $urandom_range(0, 15);
        meta.stream_id = $urandom_range(0, 15);
        meta.sequence_num = $urandom_range(0, 255);
        
        return meta;
    endfunction
    
    // Generate security USER
    function bit[{self.user_width-1}:0] generate_security_user();
        typedef struct packed {{
            bit[1:0] security_level;
            bit[1:0] access_type;
            bit[3:0] domain_id;
            bit[7:0] key_id;
        }} security_user_t;
        
        security_user_t sec;
        sec.security_level = $urandom_range(0, 3);
        sec.access_type = $urandom_range(0, 3);
        sec.domain_id = $urandom_range(0, 15);
        sec.key_id = $urandom_range(0, 255);
        
        return sec;
    endfunction
    
    // Generate debug USER
    function bit[{self.user_width-1}:0] generate_debug_user();
        typedef struct packed {{
            bit[7:0] timestamp_lsb;
            bit[3:0] trace_id;
            bit[3:0] debug_level;
        }} debug_user_t;
        
        debug_user_t dbg;
        dbg.timestamp_lsb = $time & 8'hFF;
        dbg.trace_id = $urandom_range(0, 15);
        dbg.debug_level = $urandom_range(0, 15);
        
        return dbg;
    endfunction
    
    // Apply transforms
    function bit[{self.user_width-1}:0] apply_transforms(bit[{self.user_width-1}:0] input_user);
        bit[{self.user_width-1}:0] result = input_user;
        
        // Apply all registered transforms in sequence
        foreach (transform_functions[name]) begin
            result = transform_functions[name](result);
            `uvm_info(get_type_name(), 
                     $sformatf("Applied transform %s: %0h -> %0h", 
                              name, input_user, result), 
                     UVM_HIGH)
        end
        
        return result;
    endfunction
    
    // Validate USER value
    function bit validate_user_value(bit[{self.user_width-1}:0] user_val);
        bit valid = 1;
        
        // Apply all validation rules
        foreach (validation_rules[name]) begin
            if (!validation_rules[name](user_val)) begin
                `uvm_warning(get_type_name(), 
                            $sformatf("Validation %s failed for USER=%0h", 
                                     name, user_val))
                valid = 0;
            end
        end
        
        return valid;
    endfunction
    
    // Encode USER data
    function bit[{self.user_width-1}:0] encode_user_data(bit[{self.user_width-1}:0] data);
        user_format_t format;
        bit[{self.user_width-1}:0] encoded;
        
        // Simple encoding example
        format.format_version = 4'h1;
        format.encoding_type = 4'h0;  // Raw
        format.payload_size = 8;
        
        // Add header
        encoded = {{format, data[{self.user_width-17}:0]}};
        
        // Add parity or checksum
        encoded[0] = ^encoded[{self.user_width-1}:1];  // Even parity
        
        return encoded;
    endfunction
    
    // Decode USER data
    function bit[{self.user_width-1}:0] decode_user_data(bit[{self.user_width-1}:0] encoded);
        user_format_t format;
        bit[{self.user_width-1}:0] decoded;
        
        // Extract format
        format = encoded[{self.user_width-1}:{self.user_width-16}];
        
        // Verify format
        if (format.format_version != 4'h1) begin
            `uvm_warning(get_type_name(), 
                        $sformatf("Unknown format version: %0h", format.format_version))
        end
        
        // Extract payload
        decoded = encoded[{self.user_width-17}:0];
        
        // Verify parity
        if (^encoded != 0) begin
            `uvm_warning(get_type_name(), "Parity error in USER data")
        end
        
        return decoded;
    endfunction
    
    // Register transform function
    function void register_transform(string name, user_transform_f func);
        transform_functions[name] = func;
    endfunction
    
    // Register validation rule
    function void register_validation(string name, user_validate_f func);
        validation_rules[name] = func;
    endfunction
    
    // Transform functions
    function bit[{self.user_width-1}:0] transform_identity(bit[{self.user_width-1}:0] input);
        return input;
    endfunction
    
    function bit[{self.user_width-1}:0] transform_invert(bit[{self.user_width-1}:0] input);
        return ~input;
    endfunction
    
    function bit[{self.user_width-1}:0] transform_rotate_left(bit[{self.user_width-1}:0] input);
        return {{input[{self.user_width-2}:0], input[{self.user_width-1}]}};
    endfunction
    
    function bit[{self.user_width-1}:0] transform_rotate_right(bit[{self.user_width-1}:0] input);
        return {{input[0], input[{self.user_width-1}:1]}};
    endfunction
    
    function bit[{self.user_width-1}:0] transform_xor_mask(bit[{self.user_width-1}:0] input);
        bit[{self.user_width-1}:0] mask = {{8'h5A, 8'h5A}};  // Example mask
        return input ^ mask;
    endfunction
    
    // Validation functions
    function bit validate_non_zero(bit[{self.user_width-1}:0] user_val);
        return (user_val != 0);
    endfunction
    
    function bit validate_even_parity(bit[{self.user_width-1}:0] user_val);
        return (^user_val == 0);
    endfunction
    
    function bit validate_range(bit[{self.user_width-1}:0] user_val);
        // Example: Check if in valid range
        return (user_val >= 16'h1000 && user_val <= 16'hF000);
    endfunction
    
    function bit validate_format(bit[{self.user_width-1}:0] user_val);
        // Example: Check format bits
        return (user_val[{self.user_width-1}:{self.user_width-4}] == 4'h1);
    endfunction
    
    // Get protocol handler statistics
    function string get_stats();
        string stats = "\\n=== USER Protocol Handler Statistics ===\\n";
        
        stats = {{stats, $sformatf("Mode: %s\\n", mode.name())}};
        stats = {{stats, $sformatf("Transforms Applied: %0d\\n", transforms_applied)}};
        stats = {{stats, $sformatf("Validations Passed: %0d\\n", validations_passed)}};
        stats = {{stats, $sformatf("Validations Failed: %0d\\n", validations_failed)}};
        stats = {{stats, $sformatf("Encodings: %0d\\n", encodings_performed)}};
        stats = {{stats, $sformatf("Decodings: %0d\\n", decodings_performed)}};
        
        return stats;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_stats(), UVM_LOW)
    endfunction

endclass

`endif // AXI4_USER_PROTOCOL_HANDLER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_user_protocol_handler.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_user_configuration(self, output_dir: str):
        """Generate USER configuration component"""
        content = f"""// AXI4 VIP USER Configuration
// Generated: {datetime.datetime.now()}
// Configuration interface for USER signal behavior

`ifndef AXI4_USER_CONFIGURATION_SV
`define AXI4_USER_CONFIGURATION_SV

class axi4_user_configuration extends uvm_object;
    `uvm_object_utils(axi4_user_configuration)
    
    // Singleton instance
    static axi4_user_configuration m_inst;
    
    // Global USER configuration
    typedef struct {{
        bit enable_user_signals;
        bit[{self.awuser_width-1}:0] default_awuser;
        bit[{self.wuser_width-1}:0] default_wuser;
        bit[{self.buser_width-1}:0] default_buser;
        bit[{self.aruser_width-1}:0] default_aruser;
        bit[{self.ruser_width-1}:0] default_ruser;
        bit propagate_user_through_interconnect;
        bit allow_user_modification;
        bit check_user_consistency;
        string user_policy;
    }} global_user_config_t;
    
    global_user_config_t global_config;
    
    // Per-master USER configuration
    typedef struct {{
        bit enable;
        bit[{self.user_width-1}:0] default_value;
        bit randomize;
        string generation_mode;
        bit[{self.user_width-1}:0] value_range_min;
        bit[{self.user_width-1}:0] value_range_max;
    }} master_user_config_t;
    
    master_user_config_t master_configs[int];
    
    // Per-slave USER configuration
    typedef struct {{
        bit enable;
        bit generate_response_user;
        bit echo_request_user;
        bit[{self.user_width-1}:0] response_user_mask;
        string response_policy;
    }} slave_user_config_t;
    
    slave_user_config_t slave_configs[int];
    
    // USER signal mappings
    bit[{self.user_width-1}:0] user_mappings[string];
    
    // Constructor
    function new(string name = "axi4_user_configuration");
        super.new(name);
        set_defaults();
    endfunction
    
    // Singleton getter
    static function axi4_user_configuration get();
        if (m_inst == null) begin
            m_inst = axi4_user_configuration::type_id::create("axi4_user_configuration");
        end
        return m_inst;
    endfunction
    
    // Set default configuration
    function void set_defaults();
        // Global defaults
        global_config.enable_user_signals = 1;
        global_config.default_awuser = 0;
        global_config.default_wuser = 0;
        global_config.default_buser = 0;
        global_config.default_aruser = 0;
        global_config.default_ruser = 0;
        global_config.propagate_user_through_interconnect = 1;
        global_config.allow_user_modification = 0;
        global_config.check_user_consistency = 1;
        global_config.user_policy = "PASSTHROUGH";
        
        // Default mappings
        user_mappings["IDLE"] = 16'h0000;
        user_mappings["ACTIVE"] = 16'h0001;
        user_mappings["ERROR"] = 16'hDEAD;
        user_mappings["DEBUG"] = 16'hDEBG;
    endfunction
    
    // Configure master USER behavior
    function void configure_master(int master_id, master_user_config_t config);
        master_configs[master_id] = config;
        
        `uvm_info("USER_CONFIG", 
                 $sformatf("Configured master %0d: enable=%0b, default=%0h, mode=%s",
                          master_id, config.enable, config.default_value, 
                          config.generation_mode), 
                 UVM_MEDIUM)
    endfunction
    
    // Configure slave USER behavior
    function void configure_slave(int slave_id, slave_user_config_t config);
        slave_configs[slave_id] = config;
        
        `uvm_info("USER_CONFIG", 
                 $sformatf("Configured slave %0d: enable=%0b, echo=%0b, policy=%s",
                          slave_id, config.enable, config.echo_request_user,
                          config.response_policy), 
                 UVM_MEDIUM)
    endfunction
    
    // Get master configuration
    function master_user_config_t get_master_config(int master_id);
        if (master_configs.exists(master_id)) begin
            return master_configs[master_id];
        end else begin
            master_user_config_t default_config;
            default_config.enable = 1;
            default_config.default_value = 0;
            default_config.randomize = 1;
            default_config.generation_mode = "RANDOM";
            default_config.value_range_min = 0;
            default_config.value_range_max = {self.user_width{{1'b1}}};
            return default_config;
        end
    endfunction
    
    // Get slave configuration
    function slave_user_config_t get_slave_config(int slave_id);
        if (slave_configs.exists(slave_id)) begin
            return slave_configs[slave_id];
        end else begin
            slave_user_config_t default_config;
            default_config.enable = 1;
            default_config.generate_response_user = 1;
            default_config.echo_request_user = 0;
            default_config.response_user_mask = {self.user_width{{1'b1}}};
            default_config.response_policy = "GENERATE";
            return default_config;
        end
    endfunction
    
    // Add USER mapping
    function void add_user_mapping(string name, bit[{self.user_width-1}:0] value);
        user_mappings[name] = value;
        `uvm_info("USER_CONFIG", 
                 $sformatf("Added USER mapping: %s = %0h", name, value), 
                 UVM_MEDIUM)
    endfunction
    
    // Get USER mapping
    function bit[{self.user_width-1}:0] get_user_mapping(string name);
        if (user_mappings.exists(name)) begin
            return user_mappings[name];
        end else begin
            `uvm_warning("USER_CONFIG", 
                        $sformatf("USER mapping '%s' not found, returning 0", name))
            return 0;
        end
    endfunction
    
    // Load configuration from file
    function void load_from_file(string filename);
        int fd = $fopen(filename, "r");
        string line;
        
        if (fd) begin
            while (!$feof(fd)) begin
                void'($fgets(line, fd));
                parse_config_line(line);
            end
            $fclose(fd);
            
            `uvm_info("USER_CONFIG", 
                     $sformatf("Loaded USER configuration from %s", filename), 
                     UVM_LOW)
        end else begin
            `uvm_warning("USER_CONFIG", 
                        $sformatf("Cannot open configuration file %s", filename))
        end
    endfunction
    
    // Parse configuration line
    function void parse_config_line(string line);
        string tokens[$];
        string cmd, param, value;
        
        // Skip comments and empty lines
        if (line.substr(0, 0) == "#" || line == "") return;
        
        // Simple parsing
        void'($sscanf(line, "%s %s %s", cmd, param, value));
        
        case (cmd)
            "GLOBAL": begin
                case (param)
                    "enable": global_config.enable_user_signals = value.atoi();
                    "propagate": global_config.propagate_user_through_interconnect = value.atoi();
                    "policy": global_config.user_policy = value;
                endcase
            end
            
            "MASTER": begin
                int id;
                string attr;
                void'($sscanf(param, "%d.%s", id, attr));
                
                if (!master_configs.exists(id)) begin
                    master_user_config_t new_config;
                    master_configs[id] = new_config;
                end
                
                case (attr)
                    "enable": master_configs[id].enable = value.atoi();
                    "default": master_configs[id].default_value = value.atoh();
                    "mode": master_configs[id].generation_mode = value;
                endcase
            end
            
            "SLAVE": begin
                int id;
                string attr;
                void'($sscanf(param, "%d.%s", id, attr));
                
                if (!slave_configs.exists(id)) begin
                    slave_user_config_t new_config;
                    slave_configs[id] = new_config;
                end
                
                case (attr)
                    "enable": slave_configs[id].enable = value.atoi();
                    "echo": slave_configs[id].echo_request_user = value.atoi();
                    "policy": slave_configs[id].response_policy = value;
                endcase
            end
            
            "MAPPING": begin
                add_user_mapping(param, value.atoh());
            end
        endcase
    endfunction
    
    // Save configuration to file
    function void save_to_file(string filename);
        int fd = $fopen(filename, "w");
        
        if (fd) begin
            $fwrite(fd, "# AXI4 USER Signal Configuration\\n");
            $fwrite(fd, "# Generated: %s\\n\\n", $sformatf("%0t", $time));
            
            // Global configuration
            $fwrite(fd, "# Global Settings\\n");
            $fwrite(fd, "GLOBAL enable %0d\\n", global_config.enable_user_signals);
            $fwrite(fd, "GLOBAL propagate %0d\\n", 
                   global_config.propagate_user_through_interconnect);
            $fwrite(fd, "GLOBAL policy %s\\n\\n", global_config.user_policy);
            
            // Master configurations
            $fwrite(fd, "# Master Configurations\\n");
            foreach (master_configs[id]) begin
                $fwrite(fd, "MASTER %0d.enable %0d\\n", id, master_configs[id].enable);
                $fwrite(fd, "MASTER %0d.default %0h\\n", id, master_configs[id].default_value);
                $fwrite(fd, "MASTER %0d.mode %s\\n", id, master_configs[id].generation_mode);
            end
            
            // Slave configurations
            $fwrite(fd, "\\n# Slave Configurations\\n");
            foreach (slave_configs[id]) begin
                $fwrite(fd, "SLAVE %0d.enable %0d\\n", id, slave_configs[id].enable);
                $fwrite(fd, "SLAVE %0d.echo %0d\\n", id, slave_configs[id].echo_request_user);
                $fwrite(fd, "SLAVE %0d.policy %s\\n", id, slave_configs[id].response_policy);
            end
            
            // USER mappings
            $fwrite(fd, "\\n# USER Mappings\\n");
            foreach (user_mappings[name]) begin
                $fwrite(fd, "MAPPING %s %0h\\n", name, user_mappings[name]);
            end
            
            $fclose(fd);
            
            `uvm_info("USER_CONFIG", 
                     $sformatf("Saved USER configuration to %s", filename), 
                     UVM_LOW)
        end
    endfunction
    
    // Generate example configuration
    function void generate_example_config();
        // Configure masters
        for (int i = 0; i < {self.num_masters}; i++) begin
            master_user_config_t m_cfg;
            
            case (i % 4)
                0: begin  // Metadata master
                    m_cfg.enable = 1;
                    m_cfg.default_value = i << 12;  // Master ID in upper bits
                    m_cfg.randomize = 0;
                    m_cfg.generation_mode = "METADATA";
                end
                1: begin  // Security master
                    m_cfg.enable = 1;
                    m_cfg.default_value = 16'hSEC0 | i;
                    m_cfg.randomize = 0;
                    m_cfg.generation_mode = "SECURITY";
                end
                2: begin  // Debug master
                    m_cfg.enable = 1;
                    m_cfg.default_value = 16'hDBG0 | i;
                    m_cfg.randomize = 1;
                    m_cfg.generation_mode = "DEBUG";
                end
                3: begin  // Random master
                    m_cfg.enable = 1;
                    m_cfg.default_value = 0;
                    m_cfg.randomize = 1;
                    m_cfg.generation_mode = "RANDOM";
                end
            endcase
            
            configure_master(i, m_cfg);
        end
        
        // Configure slaves
        for (int i = 0; i < {self.num_slaves}; i++) begin
            slave_user_config_t s_cfg;
            
            case (i % 3)
                0: begin  // Echo slave
                    s_cfg.enable = 1;
                    s_cfg.generate_response_user = 0;
                    s_cfg.echo_request_user = 1;
                    s_cfg.response_policy = "ECHO";
                end
                1: begin  // Transform slave
                    s_cfg.enable = 1;
                    s_cfg.generate_response_user = 1;
                    s_cfg.echo_request_user = 0;
                    s_cfg.response_user_mask = 16'hFF00;
                    s_cfg.response_policy = "TRANSFORM";
                end
                2: begin  // Generate slave
                    s_cfg.enable = 1;
                    s_cfg.generate_response_user = 1;
                    s_cfg.echo_request_user = 0;
                    s_cfg.response_policy = "GENERATE";
                end
            endcase
            
            configure_slave(i, s_cfg);
        end
        
        // Add custom mappings
        add_user_mapping("MASTER_0_IDLE", 16'h0000);
        add_user_mapping("MASTER_0_ACTIVE", 16'h0001);
        add_user_mapping("SECURE_ACCESS", 16'hSECU);
        add_user_mapping("DEBUG_TRACE", 16'hTRCE);
    endfunction
    
    // Get configuration summary
    function string get_config_summary();
        string summary = "\\n=== USER Configuration Summary ===\\n";
        
        summary = {{summary, "\\nGlobal Configuration:\\n"}};
        summary = {{summary, $sformatf("  USER Signals: %s\\n", 
                                     global_config.enable_user_signals ? "Enabled" : "Disabled")}};
        summary = {{summary, $sformatf("  Propagation: %s\\n",
                                     global_config.propagate_user_through_interconnect ? 
                                     "Enabled" : "Disabled")}};
        summary = {{summary, $sformatf("  Policy: %s\\n", global_config.user_policy)}};
        
        summary = {{summary, $sformatf("\\nMaster Configurations: %0d\\n", master_configs.size())}};
        foreach (master_configs[id]) begin
            summary = {{summary, $sformatf("  Master %0d: %s, default=%0h, mode=%s\\n",
                                         id,
                                         master_configs[id].enable ? "Enabled" : "Disabled",
                                         master_configs[id].default_value,
                                         master_configs[id].generation_mode)}};
        end
        
        summary = {{summary, $sformatf("\\nSlave Configurations: %0d\\n", slave_configs.size())}};
        foreach (slave_configs[id]) begin
            summary = {{summary, $sformatf("  Slave %0d: %s, echo=%0b, policy=%s\\n",
                                         id,
                                         slave_configs[id].enable ? "Enabled" : "Disabled",
                                         slave_configs[id].echo_request_user,
                                         slave_configs[id].response_policy)}};
        end
        
        summary = {{summary, $sformatf("\\nUSER Mappings: %0d\\n", user_mappings.size())}};
        foreach (user_mappings[name]) begin
            summary = {{summary, $sformatf("  %s = %0h\\n", name, user_mappings[name])}};
        end
        
        return summary;
    endfunction

endclass

`endif // AXI4_USER_CONFIGURATION_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_user_configuration.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_user_package(self, output_dir: str):
        """Generate USER package file"""
        content = f"""// AXI4 VIP USER Package
// Generated: {datetime.datetime.now()}
// Contains all USER signal components

`ifndef AXI4_USER_PKG_SV
`define AXI4_USER_PKG_SV

package axi4_user_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Import base VIP package
    import axi4_vip_pkg::*;
    
    // USER signal widths
    parameter AWUSER_WIDTH = {self.awuser_width};
    parameter WUSER_WIDTH = {self.wuser_width};
    parameter BUSER_WIDTH = {self.buser_width};
    parameter ARUSER_WIDTH = {self.aruser_width};
    parameter RUSER_WIDTH = {self.ruser_width};
    
    // Include USER components
    `include "axi4_user_agent.sv"
    `include "axi4_user_sequencer.sv"
    `include "axi4_user_monitor.sv"
    `include "axi4_user_scoreboard.sv"
    `include "axi4_user_coverage.sv"
    `include "axi4_user_protocol_handler.sv"
    `include "axi4_user_configuration.sv"
    
endpackage

`endif // AXI4_USER_PKG_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_user_pkg.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def generate_user_integration_example(self, output_dir: str):
        """Generate example of USER integration"""
        content = f"""// AXI4 VIP USER Integration Example
// Generated: {datetime.datetime.now()}
// Shows how to integrate USER signal components

class axi4_user_env extends uvm_env;
    `uvm_component_utils(axi4_user_env)
    
    // USER components
    axi4_user_agent user_agent;
    axi4_user_scoreboard user_scoreboard;
    axi4_user_coverage user_coverage;
    axi4_user_protocol_handler user_handler;
    
    // Constructor
    function new(string name = "axi4_user_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure USER system
        configure_user_signals();
        
        // Create components
        user_agent = axi4_user_agent::type_id::create("user_agent", this);
        user_scoreboard = axi4_user_scoreboard::type_id::create("user_scoreboard", this);
        user_coverage = axi4_user_coverage::type_id::create("user_coverage", this);
        user_handler = axi4_user_protocol_handler::type_id::create("user_handler", this);
    endfunction
    
    // Configure USER signals
    function void configure_user_signals();
        axi4_user_configuration user_config = axi4_user_configuration::get();
        axi4_user_agent::user_config_t agent_config;
        
        // Generate example configuration
        user_config.generate_example_config();
        
        // Configure agent
        agent_config.active = 1;
        agent_config.enable_user_checking = 1;
        agent_config.enable_user_generation = 1;
        agent_config.randomize_user = 1;
        agent_config.propagate_user = 1;
        agent_config.check_user_consistency = 1;
        
        // Set agent configuration
        uvm_config_db#(axi4_user_agent::user_config_t)::set(
            this, "user_agent", "user_config", agent_config);
        
        // Configure protocol handler
        user_handler.mode = axi4_user_protocol_handler::USER_VALIDATE;
        
        // Save configuration
        user_config.save_to_file("user_config.txt");
    endfunction
    
    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect monitor to scoreboard and coverage
        user_agent.user_ap.connect(user_scoreboard.master_export);
        user_agent.user_ap.connect(user_coverage.analysis_export);
    endfunction
    
    // End of elaboration
    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        
        // Print configuration
        `uvm_info(get_type_name(), 
                 axi4_user_configuration::get().get_config_summary(), 
                 UVM_LOW)
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        // Generate comprehensive USER report
        `uvm_info(get_type_name(), "=== USER System Report ===", UVM_LOW)
        // Reports are generated by individual components
    endfunction

endclass

// Example test using USER signals
class axi4_user_test extends uvm_test;
    `uvm_component_utils(axi4_user_test)
    
    axi4_user_env env;
    
    function new(string name = "axi4_user_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = axi4_user_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        axi4_user_sequence_lib seq_lib;
        
        phase.raise_objection(this);
        
        // Create sequence library
        seq_lib = axi4_user_sequence_lib::type_id::create("seq_lib");
        
        // Run different USER sequences
        run_user_sequences(seq_lib);
        
        #100us;
        
        phase.drop_objection(this);
    endtask
    
    task run_user_sequences(axi4_user_sequence_lib seq_lib);
        // Random USER sequence
        begin
            axi4_user_random_sequence seq = 
                axi4_user_random_sequence::type_id::create("random_seq");
            seq.num_trans = 100;
            seq.start(env.user_agent.user_sequencer);
        end
        
        // Pattern-based sequence
        begin
            axi4_user_pattern_sequence seq = 
                axi4_user_pattern_sequence::type_id::create("pattern_seq");
            seq.num_trans = 50;
            seq.mode = axi4_user_pattern_sequence::SEQUENTIAL;
            seq.start(env.user_agent.user_sequencer);
        end
        
        // Metadata sequence
        begin
            axi4_user_metadata_sequence seq = 
                axi4_user_metadata_sequence::type_id::create("metadata_seq");
            seq.num_trans = 50;
            seq.start(env.user_agent.user_sequencer);
        end
        
        // Security sequence
        begin
            axi4_user_security_sequence seq = 
                axi4_user_security_sequence::type_id::create("security_seq");
            seq.num_trans = 50;
            seq.start(env.user_agent.user_sequencer);
        end
        
        // Debug sequence
        begin
            axi4_user_debug_sequence seq = 
                axi4_user_debug_sequence::type_id::create("debug_seq");
            seq.num_trans = 50;
            seq.start(env.user_agent.user_sequencer);
        end
    endtask

endclass

// USER sequence library
class axi4_user_sequence_lib extends uvm_sequence_library #(axi4_user_transaction);
    `uvm_object_utils(axi4_user_sequence_lib)
    `uvm_sequence_library_utils(axi4_user_sequence_lib)
    
    function new(string name = "axi4_user_sequence_lib");
        super.new(name);
        init_sequence_library();
    endfunction
    
    function void init_sequence_library();
        add_sequence(axi4_user_random_sequence::type_id::get());
        add_sequence(axi4_user_pattern_sequence::type_id::get());
        add_sequence(axi4_user_metadata_sequence::type_id::get());
        add_sequence(axi4_user_security_sequence::type_id::get());
        add_sequence(axi4_user_debug_sequence::type_id::get());
    endfunction

endclass
"""
        
        filepath = os.path.join(output_dir, "axi4_user_integration_example.sv")
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
        'awuser_width': 16,
        'wuser_width': 16,
        'buser_width': 16,
        'aruser_width': 16,
        'ruser_width': 16,
        'protocol': 'AXI4'
    }
    
    generator = VIPUserGenerator(config)
    generator.generate_all_user_components("./vip_output")
    generator.generate_user_integration_example("./vip_output")
    print("USER components generated successfully!")