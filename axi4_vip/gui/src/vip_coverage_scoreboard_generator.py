#!/usr/bin/env python3
"""
VIP Coverage Models and Scoreboard Generator
Generates comprehensive coverage and scoreboard components for AXI4 verification
"""

import os
import datetime
from typing import Dict, List, Optional, Tuple

class VIPCoverageScoreboardGenerator:
    """Generator for AXI4 VIP coverage models and scoreboard"""
    
    def __init__(self, config: Dict):
        """Initialize generator with configuration"""
        self.config = config
        self.num_masters = config.get('num_masters', 2)
        self.num_slaves = config.get('num_slaves', 2)
        self.data_width = config.get('data_width', 64)
        self.addr_width = config.get('addr_width', 32)
        self.id_width = config.get('id_width', 4)
        self.user_width = config.get('user_width', 0)
        self.protocol_version = config.get('protocol', 'AXI4')
        
    def generate_all_components(self, output_dir: str):
        """Generate all coverage and scoreboard components"""
        # Create directory structure
        coverage_dir = os.path.join(output_dir, 'coverage')
        scoreboard_dir = os.path.join(output_dir, 'scoreboard')
        os.makedirs(coverage_dir, exist_ok=True)
        os.makedirs(scoreboard_dir, exist_ok=True)
        
        # Generate coverage models
        self._generate_functional_coverage(coverage_dir)
        self._generate_protocol_coverage(coverage_dir)
        self._generate_performance_coverage(coverage_dir)
        self._generate_error_coverage(coverage_dir)
        self._generate_cross_coverage(coverage_dir)
        
        # Generate scoreboard components
        self._generate_transaction_scoreboard(scoreboard_dir)
        self._generate_memory_scoreboard(scoreboard_dir)
        self._generate_ordering_scoreboard(scoreboard_dir)
        self._generate_performance_scoreboard(scoreboard_dir)
        
        # Generate coverage collector
        self._generate_coverage_collector(coverage_dir)
        
        # Generate report generator
        self._generate_report_generator(output_dir)
        
    def _generate_functional_coverage(self, output_dir: str):
        """Generate functional coverage model"""
        content = f"""// AXI4 VIP Functional Coverage Model
// Generated: {datetime.datetime.now()}

`ifndef AXI4_FUNCTIONAL_COVERAGE_SV
`define AXI4_FUNCTIONAL_COVERAGE_SV

class axi4_functional_coverage extends uvm_subscriber #(axi4_transaction);
    `uvm_component_utils(axi4_functional_coverage)
    
    // Transaction handle
    axi4_transaction trans;
    
    // Coverage groups
    covergroup cg_burst_types;
        option.per_instance = 1;
        option.name = "burst_types";
        
        // Burst type coverage
        burst_type: coverpoint trans.burst {
            bins fixed = {{2'b00}};
            bins incr = {{2'b01}};
            bins wrap = {{2'b10}};
            illegal_bins reserved = {{2'b11}};
        }}
        
        // Burst length coverage for different burst types
        burst_len_fixed: coverpoint trans.len iff (trans.burst == 2'b00) {
            bins single = {{8'h00}};
            bins len_2_to_16 = {{[8'h01:8'h0F]}};
            illegal_bins invalid = {{[8'h10:8'hFF]}};  // FIXED limited to 16
        }}
        
        burst_len_incr: coverpoint trans.len iff (trans.burst == 2'b01) {
            bins single = {{8'h00}};
            bins short_burst = {{[8'h01:8'h0F]}};
            bins medium_burst = {{[8'h10:8'h3F]}};
            bins long_burst = {{[8'h40:8'h7F]}};
            bins max_burst = {{[8'h80:8'hFF]}};  // AXI4 supports up to 256
        }}
        
        burst_len_wrap: coverpoint trans.len iff (trans.burst == 2'b10) {
            bins wrap_2 = {{8'h01}};
            bins wrap_4 = {{8'h03}};
            bins wrap_8 = {{8'h07}};
            bins wrap_16 = {{8'h0F}};
            illegal_bins invalid = default;
        }}
    endgroup
    
    covergroup cg_transfer_sizes;
        option.per_instance = 1;
        option.name = "transfer_sizes";
        
        // Transfer size coverage
        size: coverpoint trans.size {
            bins byte_1 = {{3'b000}};
            bins byte_2 = {{3'b001}};
            bins byte_4 = {{3'b010}};
            bins byte_8 = {{3'b011}};
            bins byte_16 = {{3'b100}};
            bins byte_32 = {{3'b101}};
            bins byte_64 = {{3'b110}};
            bins byte_128 = {{3'b111}};
        }}
        
        // Size vs data bus width
        size_vs_width: cross size, trans.data_width;
    endgroup
    
    covergroup cg_addressing;
        option.per_instance = 1;
        option.name = "addressing";
        
        // Address alignment
        addr_alignment: coverpoint trans.addr[11:0] {
            bins aligned_4k = {{12'h000}};
            bins aligned_1k = {{12'h000, 12'h400, 12'h800, 12'hC00}};
            bins near_4k_boundary = {{[12'hFF0:12'hFFF]}};
            bins unaligned = default;
        }}
        
        // Address regions (upper bits)
        addr_region: coverpoint trans.addr[{self.addr_width-1}:28] {
            bins region_0 = {{4'h0}};
            bins region_1 = {{4'h1}};
            bins region_2 = {{4'h2}};
            bins region_3 = {{4'h3}};
            bins region_high = {{[4'h4:4'hF]}};
        }}
        
        // 4KB boundary crossing detection
        boundary_cross: coverpoint trans.crosses_4k_boundary {
            bins no_cross = {{1'b0}};
            bins crosses = {{1'b1}};
        }}
    endgroup
    
    covergroup cg_exclusive_access;
        option.per_instance = 1;
        option.name = "exclusive_access";
        
        // Lock type (AXI4 only supports exclusive)
        lock: coverpoint trans.lock {
            bins normal = {{1'b0}};
            bins exclusive = {{1'b1}};
        }}
        
        // Exclusive access size
        excl_size: coverpoint trans.size iff (trans.lock == 1'b1) {
            bins valid_sizes = {{[3'b000:3'b111]}};  // All sizes valid for exclusive
        }}
        
        // Exclusive access alignment
        excl_align: coverpoint trans.addr[6:0] iff (trans.lock == 1'b1) {
            bins aligned = {{7'h00}};
            bins unaligned = default;
        }}
    endgroup
    
    covergroup cg_response_types;
        option.per_instance = 1;
        option.name = "response_types";
        
        // Response coverage
        resp: coverpoint trans.resp {
            bins okay = {{2'b00}};
            bins exokay = {{2'b01}};
            bins slverr = {{2'b10}};
            bins decerr = {{2'b11}};
        }}
        
        // Response vs transaction type
        resp_vs_type: cross resp, trans.is_write;
        
        // Response vs exclusive
        resp_vs_excl: cross resp, trans.lock;
    endgroup
    
    covergroup cg_cache_attributes;
        option.per_instance = 1;
        option.name = "cache_attributes";
        
        // Cache type
        cache: coverpoint trans.cache {
            bins device_non_buf = {{4'b0000}};
            bins device_buf = {{4'b0001}};
            bins normal_non_cache_non_buf = {{4'b0010}};
            bins normal_non_cache_buf = {{4'b0011}};
            bins write_through_no_alloc = {{4'b1010}};
            bins write_through_read_alloc = {{4'b1110}};
            bins write_through_write_alloc = {{4'b1010}};
            bins write_through_read_write_alloc = {{4'b1110}};
            bins write_back_no_alloc = {{4'b1011}};
            bins write_back_read_alloc = {{4'b1111}};
            bins write_back_write_alloc = {{4'b1011}};
            bins write_back_read_write_alloc = {{4'b1111}};
        }}
    endgroup
    
    covergroup cg_protection;
        option.per_instance = 1;
        option.name = "protection";
        
        // Protection type
        prot: coverpoint trans.prot {
            bins normal_non_secure_data = {{3'b000}};
            bins normal_non_secure_inst = {{3'b100}};
            bins normal_secure_data = {{3'b001}};
            bins normal_secure_inst = {{3'b101}};
            bins privileged_non_secure_data = {{3'b010}};
            bins privileged_non_secure_inst = {{3'b110}};
            bins privileged_secure_data = {{3'b011}};
            bins privileged_secure_inst = {{3'b111}};
        }}
    endgroup
    
    covergroup cg_qos_region;
        option.per_instance = 1;
        option.name = "qos_region";
        
        // QoS values
        qos: coverpoint trans.qos {
            bins low_priority = {{[4'h0:4'h3]}};
            bins medium_priority = {{[4'h4:4'h7]}};
            bins high_priority = {{[4'h8:4'hB]}};
            bins critical = {{[4'hC:4'hF]}};
        }}
        
        // Region identifier
        region: coverpoint trans.region {
            bins region[16] = {{[4'h0:4'hF]}};
        }}
        
        // QoS vs Region cross
        qos_vs_region: cross qos, region;
    endgroup
    
    covergroup cg_strobe_patterns;
        option.per_instance = 1;
        option.name = "strobe_patterns";
        
        // Write strobe patterns
        wstrb: coverpoint trans.wstrb[7:0] {
            bins all_lanes = {{8'hFF}};
            bins no_lanes = {{8'h00}};
            bins single_byte[8] = {{8'h01, 8'h02, 8'h04, 8'h08, 
                                   8'h10, 8'h20, 8'h40, 8'h80}};
            bins half_word = {{8'h03, 8'h0C, 8'h30, 8'hC0}};
            bins word = {{8'h0F, 8'hF0}};
            bins sparse = default;
        }}
    endgroup
    
    // Constructor
    function new(string name = "axi4_functional_coverage", uvm_component parent = null);
        super.new(name, parent);
        cg_burst_types = new();
        cg_transfer_sizes = new();
        cg_addressing = new();
        cg_exclusive_access = new();
        cg_response_types = new();
        cg_cache_attributes = new();
        cg_protection = new();
        cg_qos_region = new();
        cg_strobe_patterns = new();
    endfunction
    
    // Write method
    function void write(axi4_transaction t);
        trans = t;
        cg_burst_types.sample();
        cg_transfer_sizes.sample();
        cg_addressing.sample();
        cg_exclusive_access.sample();
        cg_response_types.sample();
        cg_cache_attributes.sample();
        cg_protection.sample();
        cg_qos_region.sample();
        if (trans.is_write) begin
            cg_strobe_patterns.sample();
        end
    endfunction
    
    // Report coverage
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), 
                  $sformatf("Functional Coverage: %0.2f%%", 
                           $get_coverage()), UVM_LOW)
    endfunction

endclass

`endif // AXI4_FUNCTIONAL_COVERAGE_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_functional_coverage.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_protocol_coverage(self, output_dir: str):
        """Generate protocol-specific coverage model"""
        content = f"""// AXI4 VIP Protocol Coverage Model
// Generated: {datetime.datetime.now()}

`ifndef AXI4_PROTOCOL_COVERAGE_SV
`define AXI4_PROTOCOL_COVERAGE_SV

class axi4_protocol_coverage extends uvm_component;
    `uvm_component_utils(axi4_protocol_coverage)
    
    // Analysis ports
    uvm_analysis_imp_aw #(axi4_aw_beat, axi4_protocol_coverage) aw_export;
    uvm_analysis_imp_w #(axi4_w_beat, axi4_protocol_coverage) w_export;
    uvm_analysis_imp_ar #(axi4_ar_beat, axi4_protocol_coverage) ar_export;
    
    // Channel handshake coverage
    covergroup cg_aw_handshake;
        option.per_instance = 1;
        option.name = "aw_handshake";
        
        // Valid before ready scenarios
        valid_ready_order: coverpoint aw_handshake_order {
            bins valid_first = {{VALID_BEFORE_READY}};
            bins ready_first = {{READY_BEFORE_VALID}};
            bins simultaneous = {{VALID_READY_SAME}};
        }}
        
        // Handshake delays
        valid_to_ready_delay: coverpoint aw_valid_to_ready_cycles {
            bins immediate = {{0}};
            bins short_delay = {{[1:5]}};
            bins medium_delay = {{[6:20]}};
            bins long_delay = {{[21:100]}};
            bins very_long = {{[101:$]}};
        }}
    endgroup
    
    covergroup cg_outstanding_transactions;
        option.per_instance = 1;
        option.name = "outstanding";
        
        // Outstanding write transactions per ID
        write_outstanding: coverpoint num_outstanding_writes {
            bins none = {{0}};
            bins single = {{1}};
            bins few = {{[2:4]}};
            bins many = {{[5:16]}};
            bins max = {{[17:$]}};
        }}
        
        // Outstanding read transactions per ID
        read_outstanding: coverpoint num_outstanding_reads {
            bins none = {{0}};
            bins single = {{1}};
            bins few = {{[2:4]}};
            bins many = {{[5:16]}};
            bins max = {{[17:$]}};
        }}
        
        // Write vs Read outstanding
        wr_vs_rd_outstanding: cross write_outstanding, read_outstanding;
    endgroup
    
    covergroup cg_interleaving;
        option.per_instance = 1;
        option.name = "interleaving";
        
        // Write data interleaving (AXI3 only)
        write_interleave_depth: coverpoint num_interleaved_writes {
            bins none = {{0}};
            bins two = {{2}};
            bins three_to_four = {{[3:4]}};
            bins many = {{[5:$]}};
        }}
        
        // Read data interleaving
        read_interleave_depth: coverpoint num_interleaved_reads {
            bins none = {{0}};
            bins two = {{2}};
            bins three_to_four = {{[3:4]}};
            bins many = {{[5:$]}};
        }}
    endgroup
    
    covergroup cg_ordering_hazards;
        option.per_instance = 1;
        option.name = "ordering_hazards";
        
        // Write after Write hazard
        waw_hazard: coverpoint has_waw_hazard {
            bins no_hazard = {{0}};
            bins hazard_detected = {{1}};
        }}
        
        // Write after Read hazard
        war_hazard: coverpoint has_war_hazard {
            bins no_hazard = {{0}};
            bins hazard_detected = {{1}};
        }}
        
        // Read after Write hazard
        raw_hazard: coverpoint has_raw_hazard {
            bins no_hazard = {{0}};
            bins hazard_detected = {{1}};
        }}
        
        // Same ID ordering
        same_id_ordering: coverpoint maintains_id_order {
            bins in_order = {{1}};
            bins out_of_order = {{0}};
        }}
    endgroup
    
    covergroup cg_channel_dependencies;
        option.per_instance = 1;
        option.name = "channel_deps";
        
        // Write address to data dependency
        aw_to_w_order: coverpoint aw_before_w {
            bins aw_first = {{1}};
            bins w_first = {{0}};
        }}
        
        // Write response dependencies
        w_to_b_complete: coverpoint w_complete_before_b {
            bins proper_order = {{1}};
            bins early_response = {{0}};
        }}
        
        // Channel backpressure
        channel_stalls: coverpoint stalled_channel {
            bins no_stall = {{NONE}};
            bins aw_stall = {{AW_CHANNEL}};
            bins w_stall = {{W_CHANNEL}};
            bins ar_stall = {{AR_CHANNEL}};
            bins multiple_stalls = {{MULTIPLE}};
        }}
    endgroup
    
    // Constructor
    function new(string name = "axi4_protocol_coverage", uvm_component parent = null);
        super.new(name, parent);
        cg_aw_handshake = new();
        cg_outstanding_transactions = new();
        cg_interleaving = new();
        cg_ordering_hazards = new();
        cg_channel_dependencies = new();
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        aw_export = new("aw_export", this);
        w_export = new("w_export", this);
        ar_export = new("ar_export", this);
    endfunction
    
    // Write methods for different channels
    function void write_aw(axi4_aw_beat beat);
        // Update handshake coverage
        update_aw_handshake_coverage(beat);
        cg_aw_handshake.sample();
    endfunction
    
    function void write_w(axi4_w_beat beat);
        // Update channel dependency coverage
        update_channel_dependencies(beat);
        cg_channel_dependencies.sample();
    endfunction
    
    function void write_ar(axi4_ar_beat beat);
        // Update outstanding transaction coverage
        update_outstanding_coverage();
        cg_outstanding_transactions.sample();
    endfunction

endclass

`endif // AXI4_PROTOCOL_COVERAGE_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_protocol_coverage.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_performance_coverage(self, output_dir: str):
        """Generate performance-related coverage"""
        content = f"""// AXI4 VIP Performance Coverage Model
// Generated: {datetime.datetime.now()}

`ifndef AXI4_PERFORMANCE_COVERAGE_SV
`define AXI4_PERFORMANCE_COVERAGE_SV

class axi4_performance_coverage extends uvm_component;
    `uvm_component_utils(axi4_performance_coverage)
    
    // Performance metrics
    int unsigned total_cycles;
    int unsigned active_cycles;
    int unsigned idle_cycles;
    real bandwidth_utilization;
    
    // Latency tracking
    int unsigned write_latencies[$];
    int unsigned read_latencies[$];
    
    covergroup cg_throughput;
        option.per_instance = 1;
        option.name = "throughput";
        
        // Write channel utilization
        write_util: coverpoint write_channel_utilization {
            bins idle = {{[0:10]}};
            bins low = {{[11:30]}};
            bins medium = {{[31:60]}};
            bins high = {{[61:85]}};
            bins saturated = {{[86:100]}};
        }}
        
        // Read channel utilization
        read_util: coverpoint read_channel_utilization {
            bins idle = {{[0:10]}};
            bins low = {{[11:30]}};
            bins medium = {{[31:60]}};
            bins high = {{[61:85]}};
            bins saturated = {{[86:100]}};
        }}
        
        // Combined utilization
        combined_util: cross write_util, read_util;
    endgroup
    
    covergroup cg_latency;
        option.per_instance = 1;
        option.name = "latency";
        
        // Write transaction latency
        write_latency: coverpoint avg_write_latency {
            bins fast = {{[0:10]}};
            bins normal = {{[11:50]}};
            bins slow = {{[51:200]}};
            bins very_slow = {{[201:$]}};
        }}
        
        // Read transaction latency
        read_latency: coverpoint avg_read_latency {
            bins fast = {{[0:10]}};
            bins normal = {{[11:50]}};
            bins slow = {{[51:200]}};
            bins very_slow = {{[201:$]}};
        }}
        
        // First word latency
        first_word_latency: coverpoint first_data_latency {
            bins immediate = {{[0:2]}};
            bins fast = {{[3:10]}};
            bins normal = {{[11:30]}};
            bins slow = {{[31:$]}};
        }}
    endgroup
    
    covergroup cg_arbitration;
        option.per_instance = 1;
        option.name = "arbitration";
        
        // Arbitration latency
        arb_latency: coverpoint arbitration_cycles {
            bins no_contention = {{0}};
            bins low_contention = {{[1:5]}};
            bins medium_contention = {{[6:20]}};
            bins high_contention = {{[21:$]}};
        }}
        
        // Grant patterns
        grant_pattern: coverpoint master_grant_sequence {
            bins round_robin = {{ROUND_ROBIN}};
            bins priority = {{PRIORITY}};
            bins weighted = {{WEIGHTED}};
            bins qos_based = {{QOS_BASED}};
        }}
        
        // Starvation detection
        starvation: coverpoint max_wait_cycles {
            bins no_starvation = {{[0:100]}};
            bins potential_starvation = {{[101:500]}};
            bins starvation = {{[501:$]}};
        }}
    endgroup
    
    covergroup cg_burst_efficiency;
        option.per_instance = 1;
        option.name = "burst_efficiency";
        
        // Burst length distribution
        burst_len_dist: coverpoint actual_burst_length {
            bins single = {{1}};
            bins short = {{[2:8]}};
            bins medium = {{[9:32]}};
            bins long = {{[33:128]}};
            bins max = {{[129:256]}};
        }}
        
        // Burst efficiency (useful data / total cycles)
        burst_eff: coverpoint burst_efficiency_percent {
            bins poor = {{[0:25]}};
            bins fair = {{[26:50]}};
            bins good = {{[51:75]}};
            bins excellent = {{[76:100]}};
        }}
        
        // Back-to-back bursts
        b2b_bursts: coverpoint back_to_back_burst_count {
            bins none = {{0}};
            bins few = {{[1:5]}};
            bins many = {{[6:20]}};
            bins continuous = {{[21:$]}};
        }}
    endgroup
    
    covergroup cg_power_efficiency;
        option.per_instance = 1;
        option.name = "power";
        
        // Clock gating opportunities
        idle_periods: coverpoint consecutive_idle_cycles {
            bins active = {{0}};
            bins short_idle = {{[1:10]}};
            bins medium_idle = {{[11:100]}};
            bins long_idle = {{[101:1000]}};
            bins very_long_idle = {{[1001:$]}};
        }}
        
        // Low power state entries
        lp_entries: coverpoint low_power_state_entries {
            bins none = {{0}};
            bins infrequent = {{[1:10]}};
            bins moderate = {{[11:50]}};
            bins frequent = {{[51:$]}};
        }}
    endgroup
    
    // Constructor
    function new(string name = "axi4_performance_coverage", uvm_component parent = null);
        super.new(name, parent);
        cg_throughput = new();
        cg_latency = new();
        cg_arbitration = new();
        cg_burst_efficiency = new();
        cg_power_efficiency = new();
    endfunction
    
    // Update performance metrics
    function void update_metrics();
        // Calculate utilization
        if (total_cycles > 0) begin
            bandwidth_utilization = real'(active_cycles) / real'(total_cycles) * 100.0;
        end
        
        // Sample coverage
        cg_throughput.sample();
        cg_latency.sample();
        cg_burst_efficiency.sample();
        
        if (idle_cycles > 0) begin
            cg_power_efficiency.sample();
        end
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), 
                  $sformatf("Performance Metrics:\\n" +
                           "  Total Cycles: %0d\\n" +
                           "  Active Cycles: %0d\\n" +
                           "  Bandwidth Utilization: %0.2f%%\\n" +
                           "  Avg Write Latency: %0.2f\\n" +
                           "  Avg Read Latency: %0.2f",
                           total_cycles, active_cycles, bandwidth_utilization,
                           get_avg_latency(write_latencies),
                           get_avg_latency(read_latencies)), UVM_LOW)
    endfunction
    
    // Helper function
    function real get_avg_latency(int unsigned latencies[$]);
        if (latencies.size() == 0) return 0.0;
        return real'(latencies.sum()) / real'(latencies.size());
    endfunction

endclass

`endif // AXI4_PERFORMANCE_COVERAGE_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_performance_coverage.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_error_coverage(self, output_dir: str):
        """Generate error injection and handling coverage"""
        content = f"""// AXI4 VIP Error Coverage Model  
// Generated: {datetime.datetime.now()}

`ifndef AXI4_ERROR_COVERAGE_SV
`define AXI4_ERROR_COVERAGE_SV

class axi4_error_coverage extends uvm_component;
    `uvm_component_utils(axi4_error_coverage)
    
    // Error counters
    int unsigned protocol_errors;
    int unsigned response_errors;
    int unsigned timeout_errors;
    
    covergroup cg_protocol_errors;
        option.per_instance = 1;
        option.name = "protocol_errors";
        
        // Protocol violation types
        error_type: coverpoint detected_error_type {
            bins stable_violation = {{STABLE_BEFORE_HANDSHAKE}};
            bins x_propagation = {{X_PROPAGATION}};
            bins illegal_burst_len = {{ILLEGAL_BURST_LENGTH}};
            bins illegal_burst_type = {{ILLEGAL_BURST_TYPE}};
            bins boundary_cross = {{BOUNDARY_4K_CROSS}};
            bins narrow_transfer = {{ILLEGAL_NARROW_TRANSFER}};
            bins exclusive_violation = {{EXCLUSIVE_VIOLATION}};
            bins cache_violation = {{CACHE_ATTR_VIOLATION}};
            bins id_violation = {{ID_WIDTH_VIOLATION}};
        }}
        
        // Error injection points
        injection_point: coverpoint error_injection_channel {
            bins aw_channel = {{AW_CHANNEL}};
            bins w_channel = {{W_CHANNEL}};
            bins b_channel = {{B_CHANNEL}};
            bins ar_channel = {{AR_CHANNEL}};
            bins r_channel = {{R_CHANNEL}};
        }}
        
        // Error detection
        detection_latency: coverpoint cycles_to_detect {
            bins immediate = {{0}};
            bins fast = {{[1:5]}};
            bins delayed = {{[6:$]}};
        }}
    endgroup
    
    covergroup cg_response_errors;
        option.per_instance = 1;
        option.name = "response_errors";
        
        // Error response generation
        resp_error_type: coverpoint response_error {
            bins slverr_decode = {{SLVERR_DECODE}};
            bins slverr_timeout = {{SLVERR_TIMEOUT}};
            bins slverr_protection = {{SLVERR_PROTECTION}};
            bins decerr_unmapped = {{DECERR_UNMAPPED}};
            bins decerr_disabled = {{DECERR_DISABLED}};
        }}
        
        // Error response handling
        error_recovery: coverpoint recovery_action {
            bins retry = {{RETRY_TRANSACTION}};
            bins abort = {{ABORT_TRANSACTION}};
            bins escalate = {{ESCALATE_ERROR}};
            bins ignore = {{IGNORE_ERROR}};
        }}
        
        // Multi-beat error responses
        error_beat: coverpoint error_on_beat_num {
            bins first_beat = {{0}};
            bins middle_beats = {{[1:14]}};
            bins last_beat = {{15}};
            bins any_beat = {{[16:$]}};
        }}
    endgroup
    
    covergroup cg_timeout_scenarios;
        option.per_instance = 1;
        option.name = "timeout";
        
        // Timeout locations
        timeout_point: coverpoint timeout_location {
            bins aw_timeout = {{AW_CHANNEL}};
            bins w_timeout = {{W_CHANNEL}};
            bins b_timeout = {{B_CHANNEL}};
            bins ar_timeout = {{AR_CHANNEL}};
            bins r_timeout = {{R_CHANNEL}};
        }}
        
        // Timeout duration
        timeout_cycles: coverpoint cycles_until_timeout {
            bins short_timeout = {{[1:100]}};
            bins medium_timeout = {{[101:1000]}};
            bins long_timeout = {{[1001:10000]}};
            bins very_long = {{[10001:$]}};
        }}
        
        // Recovery from timeout
        timeout_recovery: coverpoint recovery_method {
            bins reset = {{RESET_INTERFACE}};
            bins abort = {{ABORT_PENDING}};
            bins force_complete = {{FORCE_COMPLETION}};
        }}
    endgroup
    
    covergroup cg_data_corruption;
        option.per_instance = 1;
        option.name = "data_corruption";
        
        // Corruption type
        corruption_type: coverpoint data_error_type {
            bins bit_flip = {{SINGLE_BIT_FLIP}};
            bins multi_bit = {{MULTI_BIT_FLIP}};
            bins byte_swap = {{BYTE_SWAP}};
            bins all_zeros = {{ALL_ZEROS}};
            bins all_ones = {{ALL_ONES}};
            bins pattern = {{PATTERN_CORRUPTION}};
        }}
        
        // Detection method
        detection_method: coverpoint corruption_detected_by {
            bins parity = {{PARITY_CHECK}};
            bins ecc = {{ECC_CHECK}};
            bins data_compare = {{DATA_COMPARISON}};
            bins crc = {{CRC_CHECK}};
        }}
        
        // Corruption location
        corruption_loc: coverpoint corruption_beat {
            bins first_beat = {{0}};
            bins middle_beats = {{[1:14]}};
            bins last_beat = {{15}};
            bins multiple_beats = {{[16:$]}};
        }}
    endgroup
    
    covergroup cg_error_sequences;
        option.per_instance = 1;
        option.name = "error_sequences";
        
        // Back-to-back errors
        consecutive_errors: coverpoint num_consecutive_errors {
            bins single = {{1}};
            bins double = {{2}};
            bins multiple = {{[3:10]}};
            bins error_storm = {{[11:$]}};
        }}
        
        // Error combinations
        error_combo: coverpoint combined_error_types {
            bins protocol_only = {{PROTOCOL_ERROR}};
            bins response_only = {{RESPONSE_ERROR}};
            bins timeout_only = {{TIMEOUT_ERROR}};
            bins protocol_response = {{PROTOCOL_RESPONSE}};
            bins all_types = {{ALL_ERROR_TYPES}};
        }}
        
        // Error propagation
        error_spread: coverpoint affected_channels {
            bins single_channel = {{1}};
            bins two_channels = {{2}};
            bins three_channels = {{3}};
            bins all_channels = {{5}};
        }}
    endgroup
    
    // Constructor
    function new(string name = "axi4_error_coverage", uvm_component parent = null);
        super.new(name, parent);
        cg_protocol_errors = new();
        cg_response_errors = new();
        cg_timeout_scenarios = new();
        cg_data_corruption = new();
        cg_error_sequences = new();
    endfunction
    
    // Record error event
    function void record_error(error_event_type evt);
        case (evt.error_category)
            PROTOCOL: begin
                protocol_errors++;
                cg_protocol_errors.sample();
            end
            RESPONSE: begin
                response_errors++;
                cg_response_errors.sample();
            end
            TIMEOUT: begin
                timeout_errors++;
                cg_timeout_scenarios.sample();
            end
            DATA_CORRUPTION: begin
                cg_data_corruption.sample();
            end
        endcase
        
        // Check for error sequences
        if (evt.is_consecutive) begin
            cg_error_sequences.sample();
        end
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), 
                  $sformatf("Error Summary:\\n" +
                           "  Protocol Errors: %0d\\n" +
                           "  Response Errors: %0d\\n" +
                           "  Timeout Errors: %0d\\n" +
                           "  Total Errors: %0d",
                           protocol_errors, response_errors, 
                           timeout_errors,
                           protocol_errors + response_errors + timeout_errors), 
                  UVM_LOW)
    endfunction

endclass

`endif // AXI4_ERROR_COVERAGE_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_error_coverage.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_cross_coverage(self, output_dir: str):
        """Generate cross-coverage between different aspects"""
        content = f"""// AXI4 VIP Cross Coverage Model
// Generated: {datetime.datetime.now()}

`ifndef AXI4_CROSS_COVERAGE_SV
`define AXI4_CROSS_COVERAGE_SV

class axi4_cross_coverage extends uvm_component;
    `uvm_component_utils(axi4_cross_coverage)
    
    // Transaction attributes for cross coverage
    axi4_transaction trans;
    
    covergroup cg_master_slave_cross;
        option.per_instance = 1;
        option.name = "master_slave_cross";
        
        // Master ID
        master_id: coverpoint trans.master_id {
            bins master[{self.num_masters}] = {{[0:{self.num_masters-1}]}};
        }}
        
        // Slave ID  
        slave_id: coverpoint trans.slave_id {
            bins slave[{self.num_slaves}] = {{[0:{self.num_slaves-1}]}};
        }}
        
        // Master to slave combinations
        master_slave_combo: cross master_id, slave_id;
        
        // Master burst type per slave
        master_burst_slave: cross master_id, trans.burst, slave_id;
        
        // QoS per master-slave pair
        qos_routing: cross master_id, slave_id, trans.qos;
    endgroup
    
    covergroup cg_size_len_cross;
        option.per_instance = 1;
        option.name = "size_len_cross";
        
        // Transfer size
        size: coverpoint trans.size {
            bins narrow = {{[3'b000:3'b010]}};  // 1-4 bytes
            bins medium = {{[3'b011:3'b101]}};  // 8-32 bytes
            bins wide = {{[3'b110:3'b111]}};    // 64-128 bytes
        }}
        
        // Burst length categories
        len_cat: coverpoint trans.len {
            bins single = {{8'h00}};
            bins short = {{[8'h01:8'h0F]}};
            bins medium = {{[8'h10:8'h3F]}};
            bins long = {{[8'h40:8'hFF]}};
        }}
        
        // Size vs length combinations
        size_len: cross size, len_cat;
        
        // Optimal burst detection
        optimal_burst: coverpoint is_optimal_burst(trans.size, trans.len) {
            bins optimal = {{1'b1}};
            bins suboptimal = {{1'b0}};
        }}
    endgroup
    
    covergroup cg_address_attribute_cross;
        option.per_instance = 1;
        option.name = "addr_attr_cross";
        
        // Address region
        addr_region: coverpoint trans.addr[31:28] {
            bins secure_region = {{4'h0}};
            bins normal_region = {{[4'h1:4'h7]}};
            bins device_region = {{[4'h8:4'hF]}};
        }}
        
        // Protection attributes
        prot_type: coverpoint trans.prot {
            bins secure = {{3'b001, 3'b011, 3'b101, 3'b111}};
            bins non_secure = {{3'b000, 3'b010, 3'b100, 3'b110}};
        }}
        
        // Cache attributes
        cache_type: coverpoint trans.cache[3:2] {
            bins non_cacheable = {{2'b00}};
            bins write_through = {{2'b10}};
            bins write_back = {{2'b11}};
        }}
        
        // Cross coverage
        region_prot: cross addr_region, prot_type;
        region_cache: cross addr_region, cache_type;
        prot_cache: cross prot_type, cache_type;
    endgroup
    
    covergroup cg_exclusive_cross;
        option.per_instance = 1;
        option.name = "exclusive_cross";
        
        // Exclusive access
        excl: coverpoint trans.lock {
            bins normal = {{1'b0}};
            bins exclusive = {{1'b1}};
        }}
        
        // Response type
        resp: coverpoint trans.resp {
            bins okay = {{2'b00}};
            bins exokay = {{2'b01}};
            bins slverr = {{2'b10}};
            bins decerr = {{2'b11}};
        }}
        
        // Exclusive vs response
        excl_resp: cross excl, resp {
            illegal_bins invalid_exokay = binsof(excl.normal) && binsof(resp.exokay);
        }}
        
        // Exclusive vs size
        excl_size: cross excl, trans.size;
        
        // Exclusive vs master
        excl_master: cross excl, trans.master_id;
    endgroup
    
    covergroup cg_performance_cross;
        option.per_instance = 1;
        option.name = "performance_cross";
        
        // QoS level
        qos_level: coverpoint trans.qos {
            bins low = {{[4'h0:4'h3]}};
            bins medium = {{[4'h4:4'h7]}};
            bins high = {{[4'h8:4'hB]}};
            bins critical = {{[4'hC:4'hF]}};
        }}
        
        // Transaction latency
        latency: coverpoint trans.total_latency {
            bins fast = {{[0:20]}};
            bins normal = {{[21:100]}};
            bins slow = {{[101:500]}};
            bins very_slow = {{[501:$]}};
        }}
        
        // Burst efficiency
        efficiency: coverpoint trans.burst_efficiency {
            bins poor = {{[0:25]}};
            bins fair = {{[26:50]}};
            bins good = {{[51:75]}};
            bins excellent = {{[76:100]}};
        }}
        
        // QoS vs latency
        qos_latency: cross qos_level, latency {
            illegal_bins high_qos_slow = binsof(qos_level.critical) && 
                                        binsof(latency.slow);
        }}
        
        // QoS vs efficiency
        qos_efficiency: cross qos_level, efficiency;
    endgroup
    
    covergroup cg_error_cross;
        option.per_instance = 1;
        option.name = "error_cross";
        
        // Error response
        error_resp: coverpoint trans.resp {
            bins okay = {{2'b00}};
            bins error = {{2'b10, 2'b11}};
        }}
        
        // Transaction type
        trans_type: coverpoint trans.is_write {
            bins read = {{1'b0}};
            bins write = {{1'b1}};
        }}
        
        // Master causing error
        error_master: coverpoint trans.master_id iff (trans.resp != 2'b00);
        
        // Slave responding with error
        error_slave: coverpoint trans.slave_id iff (trans.resp != 2'b00);
        
        // Error type combinations
        error_trans_type: cross error_resp, trans_type;
        error_master_slave: cross error_master, error_slave;
    endgroup
    
    // Constructor
    function new(string name = "axi4_cross_coverage", uvm_component parent = null);
        super.new(name, parent);
        cg_master_slave_cross = new();
        cg_size_len_cross = new();
        cg_address_attribute_cross = new();
        cg_exclusive_cross = new();
        cg_performance_cross = new();
        cg_error_cross = new();
    endfunction
    
    // Sample all cross coverage
    function void sample_transaction(axi4_transaction t);
        trans = t;
        cg_master_slave_cross.sample();
        cg_size_len_cross.sample();
        cg_address_attribute_cross.sample();
        cg_exclusive_cross.sample();
        cg_performance_cross.sample();
        if (trans.resp != 2'b00) begin
            cg_error_cross.sample();
        end
    endfunction
    
    // Helper function
    function bit is_optimal_burst(bit [2:0] size, bit [7:0] len);
        // Check if burst maximizes bus utilization
        int bytes_per_beat = 1 << size;
        int total_bytes = (len + 1) * bytes_per_beat;
        
        // Optimal if it uses full bus width or is aligned to cache line
        return (bytes_per_beat == {self.data_width/8}) || 
               (total_bytes % 64 == 0);
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), 
                  $sformatf("Cross Coverage Summary:\\n" +
                           "  Master-Slave: %0.2f%%\\n" +
                           "  Size-Length: %0.2f%%\\n" +
                           "  Address-Attribute: %0.2f%%\\n" +
                           "  Exclusive: %0.2f%%\\n" +
                           "  Performance: %0.2f%%\\n" +
                           "  Error: %0.2f%%",
                           cg_master_slave_cross.get_coverage(),
                           cg_size_len_cross.get_coverage(),
                           cg_address_attribute_cross.get_coverage(),
                           cg_exclusive_cross.get_coverage(),
                           cg_performance_cross.get_coverage(),
                           cg_error_cross.get_coverage()), 
                  UVM_LOW)
    endfunction

endclass

`endif // AXI4_CROSS_COVERAGE_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_cross_coverage.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_transaction_scoreboard(self, output_dir: str):
        """Generate transaction-level scoreboard"""
        content = f"""// AXI4 VIP Transaction Scoreboard
// Generated: {datetime.datetime.now()}

`ifndef AXI4_TRANSACTION_SCOREBOARD_SV
`define AXI4_TRANSACTION_SCOREBOARD_SV

class axi4_transaction_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(axi4_transaction_scoreboard)
    
    // Analysis exports
    uvm_analysis_imp_master #(axi4_transaction, axi4_transaction_scoreboard) master_export;
    uvm_analysis_imp_slave #(axi4_transaction, axi4_transaction_scoreboard) slave_export;
    
    // Transaction storage
    axi4_transaction master_queue[bit[{self.id_width-1}:0]][$];
    axi4_transaction slave_queue[bit[{self.id_width-1}:0]][$];
    
    // Outstanding transaction tracking
    int unsigned outstanding_writes[bit[{self.id_width-1}:0]];
    int unsigned outstanding_reads[bit[{self.id_width-1}:0]];
    
    // Statistics
    int unsigned total_matches;
    int unsigned total_mismatches;
    int unsigned total_timeouts;
    int unsigned total_transactions;
    
    // Comparison controls
    bit disable_data_check = 0;
    bit disable_resp_check = 0;
    bit disable_timing_check = 0;
    
    // Constructor
    function new(string name = "axi4_transaction_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        master_export = new("master_export", this);
        slave_export = new("slave_export", this);
    endfunction
    
    // Master write method
    function void write_master(axi4_transaction trans);
        bit[{self.id_width-1}:0] id = trans.id;
        
        `uvm_info(get_type_name(), 
                  $sformatf("Master Transaction: %s", trans.convert2string()), 
                  UVM_HIGH)
        
        // Store transaction
        master_queue[id].push_back(trans);
        
        // Update outstanding counters
        if (trans.is_write) begin
            outstanding_writes[id]++;
        end else begin
            outstanding_reads[id]++;
        end
        
        total_transactions++;
        
        // Try to match with slave transaction
        check_for_match(id);
    endfunction
    
    // Slave write method
    function void write_slave(axi4_transaction trans);
        bit[{self.id_width-1}:0] id = trans.id;
        
        `uvm_info(get_type_name(), 
                  $sformatf("Slave Transaction: %s", trans.convert2string()), 
                  UVM_HIGH)
        
        // Store transaction
        slave_queue[id].push_back(trans);
        
        // Try to match with master transaction
        check_for_match(id);
    endfunction
    
    // Check for matching transactions
    function void check_for_match(bit[{self.id_width-1}:0] id);
        axi4_transaction master_trans, slave_trans;
        
        // Check if we have matching transactions
        while (master_queue[id].size() > 0 && slave_queue[id].size() > 0) begin
            master_trans = master_queue[id].pop_front();
            slave_trans = slave_queue[id].pop_front();
            
            // Compare transactions
            if (compare_transactions(master_trans, slave_trans)) begin
                total_matches++;
                `uvm_info(get_type_name(), 
                         $sformatf("MATCH: ID=%0h, Addr=%0h", id, master_trans.addr), 
                         UVM_MEDIUM)
            end else begin
                total_mismatches++;
                `uvm_error(get_type_name(), 
                          $sformatf("MISMATCH: ID=%0h\\nMaster: %s\\nSlave: %s", 
                                   id, 
                                   master_trans.convert2string(),
                                   slave_trans.convert2string()))
            end
            
            // Update outstanding counters
            if (master_trans.is_write) begin
                if (outstanding_writes[id] > 0)
                    outstanding_writes[id]--;
            end else begin
                if (outstanding_reads[id] > 0)
                    outstanding_reads[id]--;
            end
        end
    endfunction
    
    // Compare two transactions
    function bit compare_transactions(axi4_transaction master, axi4_transaction slave);
        bit match = 1;
        
        // Basic fields comparison
        if (master.addr !== slave.addr) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Address mismatch: Master=%0h, Slave=%0h", 
                               master.addr, slave.addr))
            match = 0;
        end
        
        if (master.len !== slave.len) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Length mismatch: Master=%0h, Slave=%0h", 
                               master.len, slave.len))
            match = 0;
        end
        
        if (master.size !== slave.size) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Size mismatch: Master=%0h, Slave=%0h", 
                               master.size, slave.size))
            match = 0;
        end
        
        if (master.burst !== slave.burst) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Burst mismatch: Master=%0h, Slave=%0h", 
                               master.burst, slave.burst))
            match = 0;
        end
        
        // Data comparison (if not disabled)
        if (!disable_data_check && master.is_write) begin
            foreach (master.data[i]) begin
                if (master.data[i] !== slave.data[i]) begin
                    `uvm_error(get_type_name(), 
                              $sformatf("Data mismatch at beat %0d: Master=%0h, Slave=%0h", 
                                       i, master.data[i], slave.data[i]))
                    match = 0;
                end
            end
        end
        
        // Response comparison (if not disabled)
        if (!disable_resp_check) begin
            if (master.resp !== slave.resp) begin
                `uvm_error(get_type_name(), 
                          $sformatf("Response mismatch: Master=%0h, Slave=%0h", 
                                   master.resp, slave.resp))
                match = 0;
            end
        end
        
        // Timing comparison (if not disabled)
        if (!disable_timing_check) begin
            int latency_diff = master.end_time - slave.end_time;
            if (latency_diff < 0) latency_diff = -latency_diff;
            
            if (latency_diff > 100) begin  // Configurable threshold
                `uvm_warning(get_type_name(), 
                            $sformatf("Large timing difference: %0d cycles", 
                                     latency_diff))
            end
        end
        
        return match;
    endfunction
    
    // Check phase - look for timeouts
    function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        
        // Check for unmatched transactions
        foreach (master_queue[id]) begin
            if (master_queue[id].size() > 0) begin
                `uvm_error(get_type_name(), 
                          $sformatf("Unmatched master transactions for ID %0h: %0d", 
                                   id, master_queue[id].size()))
                total_timeouts += master_queue[id].size();
            end
        end
        
        foreach (slave_queue[id]) begin
            if (slave_queue[id].size() > 0) begin
                `uvm_error(get_type_name(), 
                          $sformatf("Unmatched slave transactions for ID %0h: %0d", 
                                   id, slave_queue[id].size()))
                total_timeouts += slave_queue[id].size();
            end
        end
        
        // Check outstanding transactions
        foreach (outstanding_writes[id]) begin
            if (outstanding_writes[id] > 0) begin
                `uvm_error(get_type_name(), 
                          $sformatf("Outstanding writes for ID %0h: %0d", 
                                   id, outstanding_writes[id]))
            end
        end
        
        foreach (outstanding_reads[id]) begin
            if (outstanding_reads[id] > 0) begin
                `uvm_error(get_type_name(), 
                          $sformatf("Outstanding reads for ID %0h: %0d", 
                                   id, outstanding_reads[id]))
            end
        end
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        real match_rate;
        
        if (total_transactions > 0) begin
            match_rate = real'(total_matches) / real'(total_transactions) * 100.0;
        end else begin
            match_rate = 0.0;
        end
        
        `uvm_info(get_type_name(), 
                  $sformatf("Scoreboard Summary:\\n" +
                           "  Total Transactions: %0d\\n" +
                           "  Total Matches: %0d\\n" +
                           "  Total Mismatches: %0d\\n" +
                           "  Total Timeouts: %0d\\n" +
                           "  Match Rate: %0.2f%%",
                           total_transactions, total_matches, 
                           total_mismatches, total_timeouts,
                           match_rate), 
                  UVM_LOW)
                  
        if (total_mismatches > 0 || total_timeouts > 0) begin
            `uvm_error(get_type_name(), "Scoreboard detected errors!")
        end
    endfunction

endclass

`endif // AXI4_TRANSACTION_SCOREBOARD_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_transaction_scoreboard.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_memory_scoreboard(self, output_dir: str):
        """Generate memory model scoreboard"""
        content = f"""// AXI4 VIP Memory Scoreboard
// Generated: {datetime.datetime.now()}

`ifndef AXI4_MEMORY_SCOREBOARD_SV
`define AXI4_MEMORY_SCOREBOARD_SV

class axi4_memory_scoreboard extends uvm_component;
    `uvm_component_utils(axi4_memory_scoreboard)
    
    // Memory model
    bit [7:0] memory[bit[{self.addr_width-1}:0]];
    bit [7:0] memory_mask[bit[{self.addr_width-1}:0]];  // Track written bytes
    
    // Memory regions
    typedef struct {{
        bit[{self.addr_width-1}:0] start_addr;
        bit[{self.addr_width-1}:0] end_addr;
        bit read_only;
        bit secure;
        string name;
    }} memory_region_t;
    
    memory_region_t regions[$];
    
    // Access tracking
    int unsigned read_accesses[bit[{self.addr_width-1}:0]];
    int unsigned write_accesses[bit[{self.addr_width-1}:0]];
    
    // Error injection
    bit inject_ecc_errors = 0;
    int ecc_error_rate = 1000;  // 1 in 1000
    
    // Statistics
    int unsigned total_reads;
    int unsigned total_writes;
    int unsigned total_errors;
    
    // Constructor
    function new(string name = "axi4_memory_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Add memory region
    function void add_memory_region(bit[{self.addr_width-1}:0] start_addr,
                                   bit[{self.addr_width-1}:0] end_addr,
                                   bit read_only = 0,
                                   bit secure = 0,
                                   string name = "");
        memory_region_t region;
        region.start_addr = start_addr;
        region.end_addr = end_addr;
        region.read_only = read_only;
        region.secure = secure;
        region.name = name;
        regions.push_back(region);
        
        `uvm_info(get_type_name(), 
                  $sformatf("Added memory region %s: [%0h:%0h] RO=%0b SEC=%0b", 
                           name, start_addr, end_addr, read_only, secure), 
                  UVM_MEDIUM)
    endfunction
    
    // Write transaction to memory
    function void write_memory(axi4_transaction trans);
        bit[{self.addr_width-1}:0] addr;
        int byte_lanes;
        
        if (!trans.is_write) return;
        
        byte_lanes = 1 << trans.size;
        addr = trans.addr;
        
        foreach (trans.data[beat]) begin
            // Check region permissions
            if (!check_write_permission(addr, trans.prot)) begin
                total_errors++;
                `uvm_error(get_type_name(), 
                          $sformatf("Write permission denied: Addr=%0h", addr))
                return;
            end
            
            // Write data with strobe
            for (int lane = 0; lane < byte_lanes; lane++) begin
                if (trans.wstrb[beat][lane]) begin
                    memory[addr + lane] = trans.data[beat][lane*8 +: 8];
                    memory_mask[addr + lane] = 8'hFF;
                    write_accesses[addr + lane]++;
                end
            end
            
            // Update address for next beat
            case (trans.burst)
                2'b00: ;  // FIXED - address stays same
                2'b01: addr = addr + byte_lanes;  // INCR
                2'b10: begin  // WRAP
                    bit[{self.addr_width-1}:0] wrap_boundary;
                    wrap_boundary = (addr / (byte_lanes * (trans.len + 1))) * 
                                   (byte_lanes * (trans.len + 1));
                    addr = addr + byte_lanes;
                    if (addr >= wrap_boundary + (byte_lanes * (trans.len + 1)))
                        addr = wrap_boundary;
                end
            endcase
        end
        
        total_writes++;
        
        `uvm_info(get_type_name(), 
                  $sformatf("Memory Write: Addr=%0h, Len=%0d, Size=%0d", 
                           trans.addr, trans.len, trans.size), 
                  UVM_HIGH)
    endfunction
    
    // Read transaction from memory
    function void read_memory(axi4_transaction trans);
        bit[{self.addr_width-1}:0] addr;
        int byte_lanes;
        bit [7:0] read_data[];
        
        if (trans.is_write) return;
        
        byte_lanes = 1 << trans.size;
        addr = trans.addr;
        read_data = new[trans.len + 1];
        
        foreach (read_data[beat]) begin
            // Check region permissions
            if (!check_read_permission(addr, trans.prot)) begin
                total_errors++;
                trans.resp = 2'b10;  // SLVERR
                `uvm_error(get_type_name(), 
                          $sformatf("Read permission denied: Addr=%0h", addr))
                return;
            end
            
            // Read data
            read_data[beat] = 0;
            for (int lane = 0; lane < byte_lanes; lane++) begin
                if (memory_mask.exists(addr + lane)) begin
                    read_data[beat][lane*8 +: 8] = memory[addr + lane];
                    
                    // Inject ECC error if enabled
                    if (inject_ecc_errors && ($urandom_range(0, ecc_error_rate) == 0)) begin
                        read_data[beat][lane*8 +: 8] ^= 8'h01;  // Single bit flip
                        `uvm_warning(get_type_name(), 
                                    $sformatf("Injected ECC error at addr %0h", 
                                             addr + lane))
                    end
                end else begin
                    read_data[beat][lane*8 +: 8] = 8'hXX;  // Uninitialized
                end
                read_accesses[addr + lane]++;
            end
            
            // Update address for next beat
            case (trans.burst)
                2'b00: ;  // FIXED
                2'b01: addr = addr + byte_lanes;  // INCR
                2'b10: begin  // WRAP
                    bit[{self.addr_width-1}:0] wrap_boundary;
                    wrap_boundary = (addr / (byte_lanes * (trans.len + 1))) * 
                                   (byte_lanes * (trans.len + 1));
                    addr = addr + byte_lanes;
                    if (addr >= wrap_boundary + (byte_lanes * (trans.len + 1)))
                        addr = wrap_boundary;
                end
            endcase
        end
        
        // Store read data in transaction
        trans.data = read_data;
        trans.resp = 2'b00;  // OKAY
        
        total_reads++;
        
        `uvm_info(get_type_name(), 
                  $sformatf("Memory Read: Addr=%0h, Len=%0d, Size=%0d", 
                           trans.addr, trans.len, trans.size), 
                  UVM_HIGH)
    endfunction
    
    // Check write permission
    function bit check_write_permission(bit[{self.addr_width-1}:0] addr, 
                                       bit [2:0] prot);
        foreach (regions[i]) begin
            if (addr >= regions[i].start_addr && addr <= regions[i].end_addr) begin
                // Check read-only
                if (regions[i].read_only) return 0;
                
                // Check secure access
                if (regions[i].secure && !prot[1]) return 0;
                
                return 1;
            end
        end
        
        // Default region - always writable
        return 1;
    endfunction
    
    // Check read permission
    function bit check_read_permission(bit[{self.addr_width-1}:0] addr, 
                                      bit [2:0] prot);
        foreach (regions[i]) begin
            if (addr >= regions[i].start_addr && addr <= regions[i].end_addr) begin
                // Check secure access
                if (regions[i].secure && !prot[1]) return 0;
                
                return 1;
            end
        end
        
        // Default region - always readable
        return 1;
    endfunction
    
    // Dump memory contents
    function void dump_memory(bit[{self.addr_width-1}:0] start_addr,
                             bit[{self.addr_width-1}:0] end_addr);
        string dump_str;
        
        dump_str = $sformatf("Memory Dump [%0h:%0h]:\\n", start_addr, end_addr);
        
        for (bit[{self.addr_width-1}:0] addr = start_addr; 
             addr <= end_addr && addr < start_addr + 256; 
             addr += 16) begin
            dump_str = {{dump_str, $sformatf("%08h: ", addr)}};
            for (int i = 0; i < 16; i++) begin
                if (memory_mask.exists(addr + i)) begin
                    dump_str = {{dump_str, $sformatf("%02h ", memory[addr + i])}};
                end else begin
                    dump_str = {{dump_str, "XX "}};
                end
            end
            dump_str = {{dump_str, "\\n"}};
        end
        
        `uvm_info(get_type_name(), dump_str, UVM_LOW)
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        int unsigned total_accessed = 0;
        int unsigned total_written = 0;
        
        // Count accessed locations
        foreach (memory_mask[addr]) begin
            if (memory_mask[addr] !== 0) total_written++;
        end
        
        foreach (read_accesses[addr]) begin
            if (read_accesses[addr] > 0) total_accessed++;
        end
        
        `uvm_info(get_type_name(), 
                  $sformatf("Memory Scoreboard Summary:\\n" +
                           "  Total Reads: %0d\\n" +
                           "  Total Writes: %0d\\n" +
                           "  Unique Locations Written: %0d\\n" +
                           "  Unique Locations Read: %0d\\n" +
                           "  Total Errors: %0d",
                           total_reads, total_writes,
                           total_written, total_accessed,
                           total_errors), 
                  UVM_LOW)
    endfunction

endclass

`endif // AXI4_MEMORY_SCOREBOARD_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_memory_scoreboard.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_ordering_scoreboard(self, output_dir: str):
        """Generate ordering rules scoreboard"""
        content = f"""// AXI4 VIP Ordering Scoreboard
// Generated: {datetime.datetime.now()}

`ifndef AXI4_ORDERING_SCOREBOARD_SV
`define AXI4_ORDERING_SCOREBOARD_SV

class axi4_ordering_scoreboard extends uvm_component;
    `uvm_component_utils(axi4_ordering_scoreboard)
    
    // Transaction tracking per ID
    typedef struct {{
        axi4_transaction trans;
        realtime issue_time;
        realtime complete_time;
        int sequence_num;
    }} tracked_trans_t;
    
    // Per-ID transaction queues
    tracked_trans_t write_queue[bit[{self.id_width-1}:0]][$];
    tracked_trans_t read_queue[bit[{self.id_width-1}:0]][$];
    
    // Global sequence counter
    int global_sequence = 0;
    
    // Ordering violation counters
    int unsigned same_id_violations;
    int unsigned hazard_violations;
    int unsigned response_violations;
    
    // Configuration
    bit enable_strict_ordering = 1;
    bit enable_hazard_checking = 1;
    
    // Constructor
    function new(string name = "axi4_ordering_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Track new transaction
    function void track_transaction(axi4_transaction trans);
        tracked_trans_t tracked;
        bit[{self.id_width-1}:0] id = trans.id;
        
        tracked.trans = trans;
        tracked.issue_time = $realtime;
        tracked.sequence_num = global_sequence++;
        
        if (trans.is_write) begin
            write_queue[id].push_back(tracked);
            `uvm_info(get_type_name(), 
                      $sformatf("Tracking write: ID=%0h, Seq=%0d, Addr=%0h", 
                               id, tracked.sequence_num, trans.addr), 
                      UVM_HIGH)
        end else begin
            read_queue[id].push_back(tracked);
            `uvm_info(get_type_name(), 
                      $sformatf("Tracking read: ID=%0h, Seq=%0d, Addr=%0h", 
                               id, tracked.sequence_num, trans.addr), 
                      UVM_HIGH)
        end
        
        // Check for ordering violations
        check_ordering_rules(trans);
    endfunction
    
    // Complete transaction
    function void complete_transaction(axi4_transaction trans);
        bit[{self.id_width-1}:0] id = trans.id;
        bit found = 0;
        
        if (trans.is_write) begin
            foreach (write_queue[id][i]) begin
                if (compare_trans_addr(write_queue[id][i].trans, trans)) begin
                    write_queue[id][i].complete_time = $realtime;
                    check_completion_order(id, trans.is_write);
                    found = 1;
                    break;
                end
            end
        end else begin
            foreach (read_queue[id][i]) begin
                if (compare_trans_addr(read_queue[id][i].trans, trans)) begin
                    read_queue[id][i].complete_time = $realtime;
                    check_completion_order(id, trans.is_write);
                    found = 1;
                    break;
                end
            end
        end
        
        if (!found) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Completed transaction not found: ID=%0h, Addr=%0h", 
                               id, trans.addr))
        end
    endfunction
    
    // Check ordering rules
    function void check_ordering_rules(axi4_transaction trans);
        bit[{self.id_width-1}:0] id = trans.id;
        
        // Check same ID ordering
        if (enable_strict_ordering) begin
            check_same_id_order(id, trans.is_write);
        end
        
        // Check hazards
        if (enable_hazard_checking) begin
            check_address_hazards(trans);
        end
    endfunction
    
    // Check same ID ordering
    function void check_same_id_order(bit[{self.id_width-1}:0] id, bit is_write);
        if (is_write) begin
            // Check write queue for same ID
            if (write_queue[id].size() > 1) begin
                // Verify all previous writes are complete
                foreach (write_queue[id][i]) begin
                    if (i < write_queue[id].size() - 1) begin
                        if (write_queue[id][i].complete_time == 0) begin
                            `uvm_error(get_type_name(), 
                                      $sformatf("Same ID write ordering violation: " +
                                               "ID=%0h, pending seq=%0d", 
                                               id, write_queue[id][i].sequence_num))
                            same_id_violations++;
                        end
                    end
                end
            end
        end else begin
            // Check read queue for same ID
            if (read_queue[id].size() > 1) begin
                foreach (read_queue[id][i]) begin
                    if (i < read_queue[id].size() - 1) begin
                        if (read_queue[id][i].complete_time == 0) begin
                            `uvm_error(get_type_name(), 
                                      $sformatf("Same ID read ordering violation: " +
                                               "ID=%0h, pending seq=%0d", 
                                               id, read_queue[id][i].sequence_num))
                            same_id_violations++;
                        end
                    end
                end
            end
        end
    endfunction
    
    // Check address hazards
    function void check_address_hazards(axi4_transaction trans);
        bit[{self.addr_width-1}:0] start_addr, end_addr;
        
        // Calculate address range
        start_addr = trans.addr;
        end_addr = calculate_end_address(trans);
        
        // Check against all outstanding transactions
        foreach (write_queue[id]) begin
            foreach (write_queue[id][i]) begin
                if (write_queue[id][i].complete_time == 0) begin
                    if (check_address_overlap(trans, write_queue[id][i].trans)) begin
                        if (trans.is_write) begin
                            `uvm_warning(get_type_name(), 
                                        $sformatf("WAW hazard detected: Addr=%0h", 
                                                 trans.addr))
                        end else begin
                            `uvm_warning(get_type_name(), 
                                        $sformatf("RAW hazard detected: Addr=%0h", 
                                                 trans.addr))
                        end
                        hazard_violations++;
                    end
                end
            end
        end
        
        if (trans.is_write) begin
            foreach (read_queue[id]) begin
                foreach (read_queue[id][i]) begin
                    if (read_queue[id][i].complete_time == 0) begin
                        if (check_address_overlap(trans, read_queue[id][i].trans)) begin
                            `uvm_warning(get_type_name(), 
                                        $sformatf("WAR hazard detected: Addr=%0h", 
                                                 trans.addr))
                            hazard_violations++;
                        end
                    end
                end
            end
        end
    endfunction
    
    // Check completion order
    function void check_completion_order(bit[{self.id_width-1}:0] id, bit is_write);
        tracked_trans_t queue[$];
        int out_of_order_count = 0;
        
        // Get the appropriate queue
        if (is_write) begin
            queue = write_queue[id];
        end else begin
            queue = read_queue[id];
        end
        
        // Check if completions are in order
        for (int i = 0; i < queue.size() - 1; i++) begin
            if (queue[i].complete_time > 0 && queue[i+1].complete_time > 0) begin
                if (queue[i].complete_time > queue[i+1].complete_time) begin
                    out_of_order_count++;
                end
            end
        end
        
        if (out_of_order_count > 0) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Out of order completion: ID=%0h, Count=%0d", 
                               id, out_of_order_count))
            response_violations += out_of_order_count;
        end
    endfunction
    
    // Helper functions
    function bit compare_trans_addr(axi4_transaction t1, axi4_transaction t2);
        return (t1.addr == t2.addr) && (t1.len == t2.len) && 
               (t1.size == t2.size) && (t1.burst == t2.burst);
    endfunction
    
    function bit[{self.addr_width-1}:0] calculate_end_address(axi4_transaction trans);
        int bytes_per_beat = 1 << trans.size;
        int total_bytes = (trans.len + 1) * bytes_per_beat;
        
        case (trans.burst)
            2'b00: return trans.addr + bytes_per_beat - 1;  // FIXED
            2'b01: return trans.addr + total_bytes - 1;     // INCR
            2'b10: begin  // WRAP
                bit[{self.addr_width-1}:0] wrap_boundary;
                wrap_boundary = (trans.addr / total_bytes) * total_bytes;
                return wrap_boundary + total_bytes - 1;
            end
            default: return trans.addr;
        endcase
    endfunction
    
    function bit check_address_overlap(axi4_transaction t1, axi4_transaction t2);
        bit[{self.addr_width-1}:0] start1, end1, start2, end2;
        
        start1 = t1.addr;
        end1 = calculate_end_address(t1);
        start2 = t2.addr;
        end2 = calculate_end_address(t2);
        
        return !((end1 < start2) || (end2 < start1));
    endfunction
    
    // Clean up completed transactions
    function void cleanup_completed();
        foreach (write_queue[id]) begin
            write_queue[id] = write_queue[id].find(item) with 
                              (item.complete_time == 0);
        end
        
        foreach (read_queue[id]) begin
            read_queue[id] = read_queue[id].find(item) with 
                            (item.complete_time == 0);
        end
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        int unsigned total_outstanding = 0;
        
        foreach (write_queue[id]) begin
            total_outstanding += write_queue[id].size();
        end
        
        foreach (read_queue[id]) begin
            total_outstanding += read_queue[id].size();
        end
        
        `uvm_info(get_type_name(), 
                  $sformatf("Ordering Scoreboard Summary:\\n" +
                           "  Same ID Violations: %0d\\n" +
                           "  Hazard Violations: %0d\\n" +
                           "  Response Order Violations: %0d\\n" +
                           "  Outstanding Transactions: %0d",
                           same_id_violations, hazard_violations,
                           response_violations, total_outstanding), 
                  UVM_LOW)
                  
        if (same_id_violations > 0 || response_violations > 0) begin
            `uvm_error(get_type_name(), "AXI ordering violations detected!")
        end
    endfunction

endclass

`endif // AXI4_ORDERING_SCOREBOARD_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_ordering_scoreboard.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_performance_scoreboard(self, output_dir: str):
        """Generate performance metrics scoreboard"""
        content = f"""// AXI4 VIP Performance Scoreboard
// Generated: {datetime.datetime.now()}

`ifndef AXI4_PERFORMANCE_SCOREBOARD_SV
`define AXI4_PERFORMANCE_SCOREBOARD_SV

class axi4_performance_scoreboard extends uvm_component;
    `uvm_component_utils(axi4_performance_scoreboard)
    
    // Performance tracking structures
    typedef struct {{
        realtime start_time;
        realtime end_time;
        int beats;
        int bytes;
        bit [3:0] qos;
        bit [{self.id_width-1}:0] id;
    }} perf_transaction_t;
    
    // Master performance metrics
    typedef struct {{
        longint total_transactions;
        longint total_bytes;
        real total_latency;
        real min_latency;
        real max_latency;
        real avg_bandwidth;
        int outstanding_peak;
    }} master_metrics_t;
    
    // Slave performance metrics
    typedef struct {{
        longint total_transactions;
        longint total_bytes;
        real total_response_time;
        real min_response_time;
        real max_response_time;
        real utilization;
    }} slave_metrics_t;
    
    // Metrics storage
    master_metrics_t master_metrics[int];
    slave_metrics_t slave_metrics[int];
    
    // Real-time tracking
    perf_transaction_t active_trans[bit[{self.id_width-1}:0]][$];
    int outstanding_count[int];  // Per master
    
    // Bandwidth tracking
    real bandwidth_samples[$];
    realtime sample_window = 1us;
    realtime last_sample_time = 0;
    longint bytes_in_window = 0;
    
    // Latency histogram
    int latency_histogram[int];  // Binned by cycles
    int latency_bin_size = 10;
    
    // QoS tracking
    int qos_transaction_count[16];  // Per QoS level
    real qos_avg_latency[16];
    
    // Constructor
    function new(string name = "axi4_performance_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        
        // Initialize metrics
        for (int i = 0; i < {self.num_masters}; i++) begin
            master_metrics[i].min_latency = 1e9;  // Large initial value
            master_metrics[i].min_response_time = 1e9;
        end
        
        for (int i = 0; i < {self.num_slaves}; i++) begin
            slave_metrics[i].min_response_time = 1e9;
        end
    endfunction
    
    // Start transaction tracking
    function void start_transaction(axi4_transaction trans);
        perf_transaction_t perf_trans;
        bit[{self.id_width-1}:0] id = trans.id;
        int master_id = trans.master_id;
        
        perf_trans.start_time = $realtime;
        perf_trans.beats = trans.len + 1;
        perf_trans.bytes = perf_trans.beats * (1 << trans.size);
        perf_trans.qos = trans.qos;
        perf_trans.id = id;
        
        active_trans[id].push_back(perf_trans);
        outstanding_count[master_id]++;
        
        // Track peak outstanding
        if (outstanding_count[master_id] > master_metrics[master_id].outstanding_peak) begin
            master_metrics[master_id].outstanding_peak = outstanding_count[master_id];
        end
        
        `uvm_info(get_type_name(), 
                  $sformatf("Start transaction: Master=%0d, ID=%0h, Bytes=%0d", 
                           master_id, id, perf_trans.bytes), 
                  UVM_HIGH)
    endfunction
    
    // Complete transaction tracking
    function void complete_transaction(axi4_transaction trans);
        bit[{self.id_width-1}:0] id = trans.id;
        int master_id = trans.master_id;
        int slave_id = trans.slave_id;
        perf_transaction_t perf_trans;
        real latency;
        
        // Find matching transaction
        foreach (active_trans[id][i]) begin
            if (/* matching criteria */) begin
                perf_trans = active_trans[id][i];
                perf_trans.end_time = $realtime;
                active_trans[id].delete(i);
                outstanding_count[master_id]--;
                break;
            end
        end
        
        // Calculate latency
        latency = perf_trans.end_time - perf_trans.start_time;
        
        // Update master metrics
        master_metrics[master_id].total_transactions++;
        master_metrics[master_id].total_bytes += perf_trans.bytes;
        master_metrics[master_id].total_latency += latency;
        
        if (latency < master_metrics[master_id].min_latency)
            master_metrics[master_id].min_latency = latency;
        if (latency > master_metrics[master_id].max_latency)
            master_metrics[master_id].max_latency = latency;
        
        // Update slave metrics
        slave_metrics[slave_id].total_transactions++;
        slave_metrics[slave_id].total_bytes += perf_trans.bytes;
        slave_metrics[slave_id].total_response_time += latency;
        
        if (latency < slave_metrics[slave_id].min_response_time)
            slave_metrics[slave_id].min_response_time = latency;
        if (latency > slave_metrics[slave_id].max_response_time)
            slave_metrics[slave_id].max_response_time = latency;
        
        // Update QoS metrics
        qos_transaction_count[perf_trans.qos]++;
        qos_avg_latency[perf_trans.qos] = 
            (qos_avg_latency[perf_trans.qos] * (qos_transaction_count[perf_trans.qos] - 1) + 
             latency) / qos_transaction_count[perf_trans.qos];
        
        // Update latency histogram
        int bin = int'(latency / latency_bin_size);
        latency_histogram[bin]++;
        
        // Update bandwidth tracking
        bytes_in_window += perf_trans.bytes;
        update_bandwidth_samples();
        
        `uvm_info(get_type_name(), 
                  $sformatf("Complete transaction: Master=%0d, Slave=%0d, Latency=%0.2fns", 
                           master_id, slave_id, latency), 
                  UVM_HIGH)
    endfunction
    
    // Update bandwidth samples
    function void update_bandwidth_samples();
        realtime current_time = $realtime;
        
        if (current_time - last_sample_time >= sample_window) begin
            real bandwidth = real'(bytes_in_window) / (current_time - last_sample_time);
            bandwidth_samples.push_back(bandwidth);
            
            // Keep only recent samples (e.g., last 1000)
            if (bandwidth_samples.size() > 1000) begin
                void'(bandwidth_samples.pop_front());
            end
            
            bytes_in_window = 0;
            last_sample_time = current_time;
        end
    endfunction
    
    // Calculate utilization
    function real calculate_utilization(realtime start_time, realtime end_time);
        real total_active_time = 0;
        real total_time = end_time - start_time;
        
        // Calculate based on active transactions
        // This is simplified - real implementation would track channel activity
        return (total_active_time / total_time) * 100.0;
    endfunction
    
    // Generate performance report
    function string get_performance_report();
        string report = "\\n=== AXI4 Performance Report ===\\n\\n";
        
        // Master performance
        report = {{report, "Master Performance:\\n"}};
        foreach (master_metrics[id]) begin
            real avg_latency = master_metrics[id].total_latency / 
                              master_metrics[id].total_transactions;
            real throughput = real'(master_metrics[id].total_bytes) / 
                             (master_metrics[id].total_latency);
            
            report = {{report, $sformatf(
                "  Master %0d:\\n" +
                "    Transactions: %0d\\n" +
                "    Total Bytes: %0d\\n" +
                "    Avg Latency: %0.2fns\\n" +
                "    Min Latency: %0.2fns\\n" +
                "    Max Latency: %0.2fns\\n" +
                "    Throughput: %0.2f GB/s\\n" +
                "    Peak Outstanding: %0d\\n\\n",
                id, master_metrics[id].total_transactions,
                master_metrics[id].total_bytes,
                avg_latency,
                master_metrics[id].min_latency,
                master_metrics[id].max_latency,
                throughput * 1e-9,
                master_metrics[id].outstanding_peak
            )}};
        end
        
        // Slave performance
        report = {{report, "\\nSlave Performance:\\n"}};
        foreach (slave_metrics[id]) begin
            real avg_response = slave_metrics[id].total_response_time / 
                               slave_metrics[id].total_transactions;
            
            report = {{report, $sformatf(
                "  Slave %0d:\\n" +
                "    Transactions: %0d\\n" +
                "    Total Bytes: %0d\\n" +
                "    Avg Response: %0.2fns\\n" +
                "    Min Response: %0.2fns\\n" +
                "    Max Response: %0.2fns\\n" +
                "    Utilization: %0.2f%%\\n\\n",
                id, slave_metrics[id].total_transactions,
                slave_metrics[id].total_bytes,
                avg_response,
                slave_metrics[id].min_response_time,
                slave_metrics[id].max_response_time,
                slave_metrics[id].utilization
            )}};
        end
        
        // QoS performance
        report = {{report, "\\nQoS Performance:\\n"}};
        for (int qos = 0; qos < 16; qos++) begin
            if (qos_transaction_count[qos] > 0) begin
                report = {{report, $sformatf(
                    "  QoS %0d: Count=%0d, Avg Latency=%0.2fns\\n",
                    qos, qos_transaction_count[qos], qos_avg_latency[qos]
                )}};
            end
        end
        
        // Latency distribution
        report = {{report, "\\nLatency Distribution:\\n"}};
        foreach (latency_histogram[bin]) begin
            report = {{report, $sformatf(
                "  %0d-%0d ns: %0d transactions\\n",
                bin * latency_bin_size,
                (bin + 1) * latency_bin_size - 1,
                latency_histogram[bin]
            )}};
        end
        
        // Bandwidth statistics
        if (bandwidth_samples.size() > 0) begin
            real avg_bw = bandwidth_samples.sum() / bandwidth_samples.size();
            real max_bw = bandwidth_samples.max();
            real min_bw = bandwidth_samples.min();
            
            report = {{report, $sformatf(
                "\\nBandwidth Statistics:\\n" +
                "  Average: %0.2f GB/s\\n" +
                "  Maximum: %0.2f GB/s\\n" +
                "  Minimum: %0.2f GB/s\\n",
                avg_bw * 1e-9, max_bw * 1e-9, min_bw * 1e-9
            )}};
        end
        
        return report;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        string report = get_performance_report();
        `uvm_info(get_type_name(), report, UVM_LOW)
        
        // Save to file
        int fd = $fopen("axi4_performance_report.txt", "w");
        if (fd) begin
            $fwrite(fd, "%s", report);
            $fclose(fd);
            `uvm_info(get_type_name(), 
                     "Performance report saved to axi4_performance_report.txt", 
                     UVM_LOW)
        end
    endfunction

endclass

`endif // AXI4_PERFORMANCE_SCOREBOARD_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_performance_scoreboard.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_coverage_collector(self, output_dir: str):
        """Generate centralized coverage collector"""
        content = f"""// AXI4 VIP Coverage Collector
// Generated: {datetime.datetime.now()}

`ifndef AXI4_COVERAGE_COLLECTOR_SV
`define AXI4_COVERAGE_COLLECTOR_SV

class axi4_coverage_collector extends uvm_component;
    `uvm_component_utils(axi4_coverage_collector)
    
    // Coverage components
    axi4_functional_coverage func_cov;
    axi4_protocol_coverage proto_cov;
    axi4_performance_coverage perf_cov;
    axi4_error_coverage error_cov;
    axi4_cross_coverage cross_cov;
    
    // Analysis ports
    uvm_analysis_port #(axi4_transaction) trans_port;
    uvm_analysis_port #(axi4_aw_beat) aw_port;
    uvm_analysis_port #(axi4_w_beat) w_port;
    uvm_analysis_port #(axi4_ar_beat) ar_port;
    
    // Coverage database
    string coverage_db_name = "axi4_coverage.ucdb";
    
    // Constructor
    function new(string name = "axi4_coverage_collector", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create coverage components
        func_cov = axi4_functional_coverage::type_id::create("func_cov", this);
        proto_cov = axi4_protocol_coverage::type_id::create("proto_cov", this);
        perf_cov = axi4_performance_coverage::type_id::create("perf_cov", this);
        error_cov = axi4_error_coverage::type_id::create("error_cov", this);
        cross_cov = axi4_cross_coverage::type_id::create("cross_cov", this);
        
        // Create analysis ports
        trans_port = new("trans_port", this);
        aw_port = new("aw_port", this);
        w_port = new("w_port", this);
        ar_port = new("ar_port", this);
    endfunction
    
    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect transaction port to functional coverage
        trans_port.connect(func_cov.analysis_export);
        
        // Connect channel ports to protocol coverage
        aw_port.connect(proto_cov.aw_export);
        w_port.connect(proto_cov.w_export);
        ar_port.connect(proto_cov.ar_export);
    endfunction
    
    // Run phase - periodic coverage updates
    task run_phase(uvm_phase phase);
        forever begin
            #100ns;  // Update interval
            
            // Update performance coverage
            perf_cov.update_metrics();
            
            // Clean up old transactions
            cleanup_old_transactions();
        end
    endtask
    
    // Sample transaction for all coverage
    function void sample_transaction(axi4_transaction trans);
        // Functional coverage
        func_cov.write(trans);
        
        // Cross coverage
        cross_cov.sample_transaction(trans);
        
        // Performance tracking
        if (trans.is_complete) begin
            perf_cov.update_metrics();
        end
    endfunction
    
    // Sample error event
    function void sample_error(error_event_type evt);
        error_cov.record_error(evt);
    endfunction
    
    // Get total coverage
    function real get_total_coverage();
        real total_cov = 0.0;
        int num_groups = 0;
        
        // Collect coverage from all components
        if (func_cov != null) begin
            total_cov += func_cov.$get_coverage();
            num_groups++;
        end
        
        if (proto_cov != null) begin
            total_cov += proto_cov.$get_coverage();
            num_groups++;
        end
        
        if (cross_cov != null) begin
            total_cov += cross_cov.$get_coverage();
            num_groups++;
        end
        
        // Calculate average
        if (num_groups > 0) begin
            return total_cov / num_groups;
        end else begin
            return 0.0;
        end
    endfunction
    
    // Generate coverage summary
    function string get_coverage_summary();
        string summary;
        
        summary = "\\n=== AXI4 Coverage Summary ===\\n\\n";
        
        summary = {{summary, $sformatf(
            "Functional Coverage: %0.2f%%\\n",
            func_cov.$get_coverage()
        )}};
        
        summary = {{summary, $sformatf(
            "Protocol Coverage: %0.2f%%\\n",
            proto_cov.$get_coverage()
        )}};
        
        summary = {{summary, $sformatf(
            "Cross Coverage: %0.2f%%\\n",
            cross_cov.$get_coverage()
        )}};
        
        summary = {{summary, $sformatf(
            "\\nTotal Coverage: %0.2f%%\\n",
            get_total_coverage()
        )}};
        
        return summary;
    endfunction
    
    // Clean up old transactions
    function void cleanup_old_transactions();
        // Implementation depends on specific needs
        // Could remove completed transactions older than certain time
    endfunction
    
    // Extract phase - save coverage database
    function void extract_phase(uvm_phase phase);
        super.extract_phase(phase);
        
        // Save coverage to database
        `ifdef COVERAGE_SAVE
        $coverage_save(coverage_db_name);
        `uvm_info(get_type_name(), 
                 $sformatf("Coverage saved to %s", coverage_db_name), 
                 UVM_LOW)
        `endif
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        string summary = get_coverage_summary();
        `uvm_info(get_type_name(), summary, UVM_LOW)
        
        // Check coverage goals
        real total_cov = get_total_coverage();
        if (total_cov < 90.0) begin
            `uvm_warning(get_type_name(), 
                        $sformatf("Coverage goal not met: %0.2f%% < 90%%", 
                                 total_cov))
        end else begin
            `uvm_info(get_type_name(), 
                     $sformatf("Coverage goal achieved: %0.2f%%", total_cov), 
                     UVM_LOW)
        end
    endfunction

endclass

`endif // AXI4_COVERAGE_COLLECTOR_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_coverage_collector.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_report_generator(self, output_dir: str):
        """Generate comprehensive report generator"""
        content = f"""// AXI4 VIP Report Generator
// Generated: {datetime.datetime.now()}

`ifndef AXI4_REPORT_GENERATOR_SV
`define AXI4_REPORT_GENERATOR_SV

class axi4_report_generator extends uvm_component;
    `uvm_component_utils(axi4_report_generator)
    
    // Report components
    axi4_coverage_collector cov_collector;
    axi4_transaction_scoreboard trans_sb;
    axi4_memory_scoreboard mem_sb;
    axi4_ordering_scoreboard order_sb;
    axi4_performance_scoreboard perf_sb;
    
    // Report configuration
    bit generate_html_report = 1;
    bit generate_text_report = 1;
    bit generate_csv_report = 1;
    string report_dir = "reports";
    
    // Constructor
    function new(string name = "axi4_report_generator", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get handles to scoreboards and coverage
        if (!uvm_config_db#(axi4_coverage_collector)::get(this, "", "cov_collector", cov_collector))
            `uvm_warning(get_type_name(), "Coverage collector not found")
            
        if (!uvm_config_db#(axi4_transaction_scoreboard)::get(this, "", "trans_sb", trans_sb))
            `uvm_warning(get_type_name(), "Transaction scoreboard not found")
            
        if (!uvm_config_db#(axi4_memory_scoreboard)::get(this, "", "mem_sb", mem_sb))
            `uvm_warning(get_type_name(), "Memory scoreboard not found")
            
        if (!uvm_config_db#(axi4_ordering_scoreboard)::get(this, "", "order_sb", order_sb))
            `uvm_warning(get_type_name(), "Ordering scoreboard not found")
            
        if (!uvm_config_db#(axi4_performance_scoreboard)::get(this, "", "perf_sb", perf_sb))
            `uvm_warning(get_type_name(), "Performance scoreboard not found")
    endfunction
    
    // Report phase - generate all reports
    function void report_phase(uvm_phase phase);
        string timestamp = $sformatf("%0t", $time);
        
        // Create report directory
        void'($system($sformatf("mkdir -p %s", report_dir)));
        
        // Generate reports based on configuration
        if (generate_text_report) begin
            generate_text_report_file();
        end
        
        if (generate_html_report) begin
            generate_html_report_file();
        end
        
        if (generate_csv_report) begin
            generate_csv_report_files();
        end
        
        // Generate summary
        generate_summary_report();
        
        `uvm_info(get_type_name(), 
                 $sformatf("Reports generated in directory: %s", report_dir), 
                 UVM_LOW)
    endfunction
    
    // Generate text report
    function void generate_text_report_file();
        int fd;
        string filename = {{report_dir, "/axi4_verification_report.txt"}};
        
        fd = $fopen(filename, "w");
        if (fd == 0) begin
            `uvm_error(get_type_name(), $sformatf("Cannot open file %s", filename))
            return;
        end
        
        $fwrite(fd, "====================================\\n");
        $fwrite(fd, "AXI4 VIP Verification Report\\n");
        $fwrite(fd, "Generated: %s\\n", $sformatf("%0t", $time));
        $fwrite(fd, "====================================\\n\\n");
        
        // Coverage section
        if (cov_collector != null) begin
            $fwrite(fd, "%s\\n", cov_collector.get_coverage_summary());
        end
        
        // Scoreboard sections
        if (trans_sb != null) begin
            $fwrite(fd, "\\n=== Transaction Scoreboard ===\\n");
            $fwrite(fd, "Total Transactions: %0d\\n", trans_sb.total_transactions);
            $fwrite(fd, "Matches: %0d\\n", trans_sb.total_matches);
            $fwrite(fd, "Mismatches: %0d\\n", trans_sb.total_mismatches);
            $fwrite(fd, "Timeouts: %0d\\n\\n", trans_sb.total_timeouts);
        end
        
        if (order_sb != null) begin
            $fwrite(fd, "\\n=== Ordering Scoreboard ===\\n");
            $fwrite(fd, "Same ID Violations: %0d\\n", order_sb.same_id_violations);
            $fwrite(fd, "Hazard Violations: %0d\\n", order_sb.hazard_violations);
            $fwrite(fd, "Response Violations: %0d\\n\\n", order_sb.response_violations);
        end
        
        // Performance section
        if (perf_sb != null) begin
            $fwrite(fd, "%s\\n", perf_sb.get_performance_report());
        end
        
        $fclose(fd);
    endfunction
    
    // Generate HTML report
    function void generate_html_report_file();
        int fd;
        string filename = {{report_dir, "/axi4_verification_report.html"}};
        
        fd = $fopen(filename, "w");
        if (fd == 0) begin
            `uvm_error(get_type_name(), $sformatf("Cannot open file %s", filename))
            return;
        end
        
        // HTML header
        $fwrite(fd, "<!DOCTYPE html>\\n");
        $fwrite(fd, "<html>\\n<head>\\n");
        $fwrite(fd, "<title>AXI4 VIP Verification Report</title>\\n");
        $fwrite(fd, "<style>\\n");
        $fwrite(fd, "body {{ font-family: Arial, sans-serif; }}\\n");
        $fwrite(fd, "table {{ border-collapse: collapse; width: 100%%; }}\\n");
        $fwrite(fd, "th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}\\n");
        $fwrite(fd, "th {{ background-color: #4CAF50; color: white; }}\\n");
        $fwrite(fd, ".pass {{ color: green; font-weight: bold; }}\\n");
        $fwrite(fd, ".fail {{ color: red; font-weight: bold; }}\\n");
        $fwrite(fd, ".warning {{ color: orange; font-weight: bold; }}\\n");
        $fwrite(fd, "</style>\\n</head>\\n<body>\\n");
        
        $fwrite(fd, "<h1>AXI4 VIP Verification Report</h1>\\n");
        $fwrite(fd, "<p>Generated: %s</p>\\n", $sformatf("%0t", $time));
        
        // Summary section
        generate_html_summary(fd);
        
        // Coverage section
        generate_html_coverage(fd);
        
        // Scoreboard section
        generate_html_scoreboard(fd);
        
        // Performance section
        generate_html_performance(fd);
        
        // HTML footer
        $fwrite(fd, "</body>\\n</html>\\n");
        $fclose(fd);
    endfunction
    
    // Generate HTML summary
    function void generate_html_summary(int fd);
        real total_cov = (cov_collector != null) ? cov_collector.get_total_coverage() : 0.0;
        bit pass = (trans_sb.total_mismatches == 0) && 
                   (trans_sb.total_timeouts == 0) && 
                   (order_sb.same_id_violations == 0) && 
                   (order_sb.response_violations == 0);
        
        $fwrite(fd, "<h2>Summary</h2>\\n");
        $fwrite(fd, "<table>\\n");
        $fwrite(fd, "<tr><th>Metric</th><th>Value</th><th>Status</th></tr>\\n");
        
        $fwrite(fd, "<tr><td>Overall Status</td><td>%s</td><td class='%s'>%s</td></tr>\\n",
                pass ? "PASS" : "FAIL",
                pass ? "pass" : "fail",
                pass ? "PASS" : "FAIL");
                
        $fwrite(fd, "<tr><td>Total Coverage</td><td>%0.2f%%</td><td class='%s'>%s</td></tr>\\n",
                total_cov,
                total_cov >= 90.0 ? "pass" : (total_cov >= 80.0 ? "warning" : "fail"),
                total_cov >= 90.0 ? "PASS" : (total_cov >= 80.0 ? "WARNING" : "FAIL"));
                
        $fwrite(fd, "</table>\\n");
    endfunction
    
    // Generate HTML coverage table
    function void generate_html_coverage(int fd);
        if (cov_collector == null) return;
        
        $fwrite(fd, "<h2>Coverage Details</h2>\\n");
        $fwrite(fd, "<table>\\n");
        $fwrite(fd, "<tr><th>Coverage Type</th><th>Percentage</th></tr>\\n");
        
        $fwrite(fd, "<tr><td>Functional</td><td>%0.2f%%</td></tr>\\n",
                cov_collector.func_cov.$get_coverage());
        $fwrite(fd, "<tr><td>Protocol</td><td>%0.2f%%</td></tr>\\n",
                cov_collector.proto_cov.$get_coverage());
        $fwrite(fd, "<tr><td>Cross</td><td>%0.2f%%</td></tr>\\n",
                cov_collector.cross_cov.$get_coverage());
                
        $fwrite(fd, "</table>\\n");
    endfunction
    
    // Generate HTML scoreboard table
    function void generate_html_scoreboard(int fd);
        $fwrite(fd, "<h2>Scoreboard Results</h2>\\n");
        $fwrite(fd, "<table>\\n");
        $fwrite(fd, "<tr><th>Check</th><th>Count</th><th>Status</th></tr>\\n");
        
        if (trans_sb != null) begin
            $fwrite(fd, "<tr><td>Transaction Matches</td><td>%0d</td><td class='pass'>PASS</td></tr>\\n",
                    trans_sb.total_matches);
            $fwrite(fd, "<tr><td>Transaction Mismatches</td><td>%0d</td><td class='%s'>%s</td></tr>\\n",
                    trans_sb.total_mismatches,
                    trans_sb.total_mismatches == 0 ? "pass" : "fail",
                    trans_sb.total_mismatches == 0 ? "PASS" : "FAIL");
        end
        
        if (order_sb != null) begin
            $fwrite(fd, "<tr><td>Ordering Violations</td><td>%0d</td><td class='%s'>%s</td></tr>\\n",
                    order_sb.same_id_violations + order_sb.response_violations,
                    (order_sb.same_id_violations + order_sb.response_violations) == 0 ? "pass" : "fail",
                    (order_sb.same_id_violations + order_sb.response_violations) == 0 ? "PASS" : "FAIL");
        end
        
        $fwrite(fd, "</table>\\n");
    endfunction
    
    // Generate HTML performance charts
    function void generate_html_performance(int fd);
        if (perf_sb == null) return;
        
        $fwrite(fd, "<h2>Performance Metrics</h2>\\n");
        
        // Add performance charts using JavaScript libraries
        // This is a simplified example - real implementation would use Chart.js or similar
        $fwrite(fd, "<div id='performance-charts'>\\n");
        $fwrite(fd, "<p>See performance_metrics.csv for detailed data</p>\\n");
        $fwrite(fd, "</div>\\n");
    endfunction
    
    // Generate CSV report files
    function void generate_csv_report_files();
        generate_coverage_csv();
        generate_performance_csv();
        generate_transaction_csv();
    endfunction
    
    // Generate coverage CSV
    function void generate_coverage_csv();
        int fd;
        string filename = {{report_dir, "/coverage_metrics.csv"}};
        
        fd = $fopen(filename, "w");
        if (fd == 0) return;
        
        $fwrite(fd, "Coverage Type,Percentage\\n");
        
        if (cov_collector != null) begin
            $fwrite(fd, "Functional,%0.2f\\n", cov_collector.func_cov.$get_coverage());
            $fwrite(fd, "Protocol,%0.2f\\n", cov_collector.proto_cov.$get_coverage());
            $fwrite(fd, "Cross,%0.2f\\n", cov_collector.cross_cov.$get_coverage());
            $fwrite(fd, "Total,%0.2f\\n", cov_collector.get_total_coverage());
        end
        
        $fclose(fd);
    endfunction
    
    // Generate performance CSV
    function void generate_performance_csv();
        int fd;
        string filename = {{report_dir, "/performance_metrics.csv"}};
        
        fd = $fopen(filename, "w");
        if (fd == 0) return;
        
        $fwrite(fd, "Master ID,Transactions,Bytes,Avg Latency (ns),Min Latency (ns),Max Latency (ns)\\n");
        
        if (perf_sb != null) begin
            foreach (perf_sb.master_metrics[id]) begin
                real avg_latency = perf_sb.master_metrics[id].total_latency / 
                                  perf_sb.master_metrics[id].total_transactions;
                $fwrite(fd, "%0d,%0d,%0d,%0.2f,%0.2f,%0.2f\\n",
                        id,
                        perf_sb.master_metrics[id].total_transactions,
                        perf_sb.master_metrics[id].total_bytes,
                        avg_latency,
                        perf_sb.master_metrics[id].min_latency,
                        perf_sb.master_metrics[id].max_latency);
            end
        end
        
        $fclose(fd);
    endfunction
    
    // Generate transaction CSV
    function void generate_transaction_csv();
        int fd;
        string filename = {{report_dir, "/transaction_summary.csv"}};
        
        fd = $fopen(filename, "w");
        if (fd == 0) return;
        
        $fwrite(fd, "Metric,Count\\n");
        
        if (trans_sb != null) begin
            $fwrite(fd, "Total Transactions,%0d\\n", trans_sb.total_transactions);
            $fwrite(fd, "Matches,%0d\\n", trans_sb.total_matches);
            $fwrite(fd, "Mismatches,%0d\\n", trans_sb.total_mismatches);
            $fwrite(fd, "Timeouts,%0d\\n", trans_sb.total_timeouts);
        end
        
        $fclose(fd);
    endfunction
    
    // Generate summary report
    function void generate_summary_report();
        int fd;
        string filename = {{report_dir, "/summary.txt"}};
        bit overall_pass = 1;
        
        fd = $fopen(filename, "w");
        if (fd == 0) return;
        
        // Check all pass criteria
        if (trans_sb != null && (trans_sb.total_mismatches > 0 || trans_sb.total_timeouts > 0))
            overall_pass = 0;
            
        if (order_sb != null && (order_sb.same_id_violations > 0 || order_sb.response_violations > 0))
            overall_pass = 0;
            
        if (cov_collector != null && cov_collector.get_total_coverage() < 90.0)
            overall_pass = 0;
        
        $fwrite(fd, "VERIFICATION %s\\n", overall_pass ? "PASSED" : "FAILED");
        $fwrite(fd, "Coverage: %0.2f%%\\n", 
                cov_collector != null ? cov_collector.get_total_coverage() : 0.0);
        $fwrite(fd, "Errors: %0d\\n", 
                trans_sb != null ? trans_sb.total_mismatches + trans_sb.total_timeouts : 0);
        
        $fclose(fd);
    endfunction

endclass

`endif // AXI4_REPORT_GENERATOR_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_report_generator.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def generate_package_file(self, output_dir: str):
        """Generate package file that includes all coverage and scoreboard components"""
        content = f"""// AXI4 VIP Coverage and Scoreboard Package
// Generated: {datetime.datetime.now()}

`ifndef AXI4_COVERAGE_SCOREBOARD_PKG_SV
`define AXI4_COVERAGE_SCOREBOARD_PKG_SV

package axi4_coverage_scoreboard_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Import VIP base package
    import axi4_vip_pkg::*;
    
    // Include coverage models
    `include "coverage/axi4_functional_coverage.sv"
    `include "coverage/axi4_protocol_coverage.sv"
    `include "coverage/axi4_performance_coverage.sv"
    `include "coverage/axi4_error_coverage.sv"
    `include "coverage/axi4_cross_coverage.sv"
    `include "coverage/axi4_coverage_collector.sv"
    
    // Include scoreboards
    `include "scoreboard/axi4_transaction_scoreboard.sv"
    `include "scoreboard/axi4_memory_scoreboard.sv"
    `include "scoreboard/axi4_ordering_scoreboard.sv"
    `include "scoreboard/axi4_performance_scoreboard.sv"
    
    // Include report generator
    `include "axi4_report_generator.sv"
    
endpackage

`endif // AXI4_COVERAGE_SCOREBOARD_PKG_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_coverage_scoreboard_pkg.sv")
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
        'user_width': 8,
        'protocol': 'AXI4'
    }
    
    generator = VIPCoverageScoreboardGenerator(config)
    generator.generate_all_components("./vip_output")
    generator.generate_package_file("./vip_output")
    print("Coverage and scoreboard components generated successfully!")