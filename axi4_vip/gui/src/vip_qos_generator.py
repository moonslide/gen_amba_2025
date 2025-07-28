#!/usr/bin/env python3
"""
VIP QoS (Quality of Service) Implementation Generator
Generates comprehensive QoS components for AXI4 verification
"""

import os
import datetime
from typing import Dict, List, Optional, Tuple

class VIPQoSGenerator:
    """Generator for AXI4 VIP QoS implementation"""
    
    def __init__(self, config: Dict):
        """Initialize generator with configuration"""
        self.config = config
        self.num_masters = config.get('num_masters', 2)
        self.num_slaves = config.get('num_slaves', 2)
        self.data_width = config.get('data_width', 64)
        self.addr_width = config.get('addr_width', 32)
        self.id_width = config.get('id_width', 4)
        self.qos_width = 4  # AXI4 standard QoS width
        self.protocol_version = config.get('protocol', 'AXI4')
        
        # QoS configuration
        self.qos_levels = {
            'CRITICAL': (12, 15),    # QoS 12-15: Critical priority
            'HIGH': (8, 11),         # QoS 8-11: High priority  
            'MEDIUM': (4, 7),        # QoS 4-7: Medium priority
            'LOW': (0, 3)            # QoS 0-3: Low priority
        }
        
    def generate_all_qos_components(self, output_dir: str):
        """Generate all QoS-related components"""
        # Create directory structure
        qos_dir = os.path.join(output_dir, 'qos')
        os.makedirs(qos_dir, exist_ok=True)
        
        # Generate QoS components
        self._generate_qos_arbiter(qos_dir)
        self._generate_qos_monitor(qos_dir)
        self._generate_qos_manager(qos_dir)
        self._generate_qos_scheduler(qos_dir)
        self._generate_qos_enforcer(qos_dir)
        self._generate_qos_analyzer(qos_dir)
        self._generate_qos_configurator(qos_dir)
        self._generate_qos_package(qos_dir)
        
    def _generate_qos_arbiter(self, output_dir: str):
        """Generate QoS-aware arbiter"""
        content = f"""// AXI4 VIP QoS Arbiter
// Generated: {datetime.datetime.now()}
// QoS-aware arbitration with multiple algorithms

`ifndef AXI4_QOS_ARBITER_SV
`define AXI4_QOS_ARBITER_SV

class axi4_qos_arbiter extends uvm_component;
    `uvm_component_utils(axi4_qos_arbiter)
    
    // Configuration
    typedef enum {{
        STRICT_PRIORITY,      // Strict QoS priority
        WEIGHTED_ROUND_ROBIN, // Weighted by QoS
        DYNAMIC_PRIORITY,     // Dynamic adjustment
        FAIR_SHARE,          // Fair bandwidth sharing
        LATENCY_BASED        // Latency-sensitive
    }} qos_arbitration_mode_e;
    
    qos_arbitration_mode_e arb_mode = WEIGHTED_ROUND_ROBIN;
    
    // QoS request structure
    typedef struct {{
        bit[{self.id_width-1}:0] id;
        bit[3:0] qos;
        int master_id;
        realtime request_time;
        int wait_cycles;
        bit urgent;
    }} qos_request_t;
    
    // Request queues per QoS level
    qos_request_t critical_queue[$];
    qos_request_t high_queue[$];
    qos_request_t medium_queue[$];
    qos_request_t low_queue[$];
    
    // QoS weights for weighted arbitration
    int qos_weights[16] = '{{16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1}};
    
    // Bandwidth allocation per QoS level (percentage)
    int qos_bandwidth_allocation[4] = '{{40, 30, 20, 10}};  // Critical, High, Medium, Low
    
    // Starvation prevention
    int max_wait_cycles = 1000;
    int starvation_threshold = 500;
    
    // Performance tracking
    int qos_grant_count[16];
    real qos_avg_wait_time[16];
    int qos_max_wait_time[16];
    
    // Constructor
    function new(string name = "axi4_qos_arbiter", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Add request to appropriate queue
    function void add_request(qos_request_t request);
        case (request.qos)
            12, 13, 14, 15: critical_queue.push_back(request);
            8, 9, 10, 11:   high_queue.push_back(request);
            4, 5, 6, 7:     medium_queue.push_back(request);
            0, 1, 2, 3:     low_queue.push_back(request);
        endcase
        
        `uvm_info(get_type_name(), 
                  $sformatf("Added request: Master=%0d, QoS=%0d, ID=%0h", 
                           request.master_id, request.qos, request.id), 
                  UVM_HIGH)
    endfunction
    
    // Main arbitration function
    function qos_request_t arbitrate();
        qos_request_t winner;
        bit found = 0;
        
        // Update wait times and check for starvation
        update_wait_times();
        check_starvation();
        
        // Arbitrate based on mode
        case (arb_mode)
            STRICT_PRIORITY:      winner = arbitrate_strict_priority();
            WEIGHTED_ROUND_ROBIN: winner = arbitrate_weighted_rr();
            DYNAMIC_PRIORITY:     winner = arbitrate_dynamic_priority();
            FAIR_SHARE:          winner = arbitrate_fair_share();
            LATENCY_BASED:       winner = arbitrate_latency_based();
        endcase
        
        // Update statistics
        if (winner.qos >= 0 && winner.qos <= 15) begin
            qos_grant_count[winner.qos]++;
            update_qos_stats(winner);
        end
        
        return winner;
    endfunction
    
    // Strict priority arbitration
    function qos_request_t arbitrate_strict_priority();
        if (critical_queue.size() > 0) return critical_queue.pop_front();
        if (high_queue.size() > 0)     return high_queue.pop_front();
        if (medium_queue.size() > 0)   return medium_queue.pop_front();
        if (low_queue.size() > 0)      return low_queue.pop_front();
        
        // Return empty request
        qos_request_t empty;
        empty.qos = -1;
        return empty;
    endfunction
    
    // Weighted round-robin arbitration
    function qos_request_t arbitrate_weighted_rr();
        static int critical_credits = 0;
        static int high_credits = 0;
        static int medium_credits = 0;
        static int low_credits = 0;
        
        // Replenish credits if all are zero
        if (critical_credits == 0 && high_credits == 0 && 
            medium_credits == 0 && low_credits == 0) begin
            critical_credits = qos_bandwidth_allocation[0];
            high_credits = qos_bandwidth_allocation[1];
            medium_credits = qos_bandwidth_allocation[2];
            low_credits = qos_bandwidth_allocation[3];
        end
        
        // Grant based on credits
        if (critical_credits > 0 && critical_queue.size() > 0) begin
            critical_credits--;
            return critical_queue.pop_front();
        end
        
        if (high_credits > 0 && high_queue.size() > 0) begin
            high_credits--;
            return high_queue.pop_front();
        end
        
        if (medium_credits > 0 && medium_queue.size() > 0) begin
            medium_credits--;
            return medium_queue.pop_front();
        end
        
        if (low_credits > 0 && low_queue.size() > 0) begin
            low_credits--;
            return low_queue.pop_front();
        end
        
        // If no credits, use strict priority
        return arbitrate_strict_priority();
    endfunction
    
    // Dynamic priority arbitration
    function qos_request_t arbitrate_dynamic_priority();
        qos_request_t candidates[$];
        qos_request_t winner;
        real max_priority = -1;
        
        // Collect all candidates
        if (critical_queue.size() > 0) candidates = {{candidates, critical_queue}};
        if (high_queue.size() > 0)     candidates = {{candidates, high_queue}};
        if (medium_queue.size() > 0)   candidates = {{candidates, medium_queue}};
        if (low_queue.size() > 0)      candidates = {{candidates, low_queue}};
        
        // Calculate dynamic priority for each
        foreach (candidates[i]) begin
            real priority = calculate_dynamic_priority(candidates[i]);
            if (priority > max_priority) begin
                max_priority = priority;
                winner = candidates[i];
            end
        end
        
        // Remove winner from appropriate queue
        remove_from_queue(winner);
        
        return winner;
    endfunction
    
    // Fair share arbitration
    function qos_request_t arbitrate_fair_share();
        static int qos_deficit[16] = '{{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}};
        qos_request_t winner;
        int max_deficit = -1000;
        
        // Find request with highest deficit
        foreach ({{critical_queue, high_queue, medium_queue, low_queue}}[q]) begin
            if (q.size() > 0) begin
                foreach (q[i]) begin
                    int deficit = qos_weights[q[i].qos] - qos_grant_count[q[i].qos];
                    qos_deficit[q[i].qos] = deficit;
                    
                    if (deficit > max_deficit) begin
                        max_deficit = deficit;
                        winner = q[i];
                    end
                end
            end
        end
        
        // Remove winner from queue
        remove_from_queue(winner);
        
        return winner;
    endfunction
    
    // Latency-based arbitration
    function qos_request_t arbitrate_latency_based();
        qos_request_t all_requests[$];
        qos_request_t winner;
        real max_urgency = -1;
        
        // Collect all requests
        all_requests = {{all_requests, critical_queue, high_queue, medium_queue, low_queue}};
        
        // Find most urgent based on wait time and QoS
        foreach (all_requests[i]) begin
            real urgency = calculate_urgency(all_requests[i]);
            if (urgency > max_urgency) begin
                max_urgency = urgency;
                winner = all_requests[i];
            end
        end
        
        // Remove winner
        remove_from_queue(winner);
        
        return winner;
    endfunction
    
    // Calculate dynamic priority
    function real calculate_dynamic_priority(qos_request_t request);
        real qos_factor = real'(request.qos) / 15.0;
        real wait_factor = real'(request.wait_cycles) / real'(max_wait_cycles);
        real urgency_factor = request.urgent ? 2.0 : 1.0;
        
        return (qos_factor * 0.5 + wait_factor * 0.4) * urgency_factor;
    endfunction
    
    // Calculate urgency for latency-based arbitration
    function real calculate_urgency(qos_request_t request);
        real base_urgency = real'(request.qos) / 15.0;
        real wait_penalty = real'(request.wait_cycles) / 100.0;
        
        // Exponential increase for long waits
        if (request.wait_cycles > starvation_threshold) begin
            wait_penalty = wait_penalty * wait_penalty;
        end
        
        return base_urgency + wait_penalty;
    endfunction
    
    // Update wait times for all queued requests
    function void update_wait_times();
        foreach (critical_queue[i]) critical_queue[i].wait_cycles++;
        foreach (high_queue[i])     high_queue[i].wait_cycles++;
        foreach (medium_queue[i])   medium_queue[i].wait_cycles++;
        foreach (low_queue[i])      low_queue[i].wait_cycles++;
    endfunction
    
    // Check for starvation and promote if needed
    function void check_starvation();
        // Check low priority queue for starvation
        foreach (low_queue[i]) begin
            if (low_queue[i].wait_cycles > starvation_threshold) begin
                low_queue[i].urgent = 1;
                `uvm_warning(get_type_name(), 
                            $sformatf("Request starving: Master=%0d, Wait=%0d cycles", 
                                     low_queue[i].master_id, low_queue[i].wait_cycles))
                
                // Optionally promote to higher queue
                if (low_queue[i].wait_cycles > max_wait_cycles) begin
                    qos_request_t promoted = low_queue[i];
                    low_queue.delete(i);
                    medium_queue.push_back(promoted);
                    `uvm_info(get_type_name(), "Promoted starving request", UVM_MEDIUM)
                end
            end
        end
        
        // Similar checks for medium queue
        foreach (medium_queue[i]) begin
            if (medium_queue[i].wait_cycles > starvation_threshold) begin
                medium_queue[i].urgent = 1;
            end
        end
    endfunction
    
    // Remove request from appropriate queue
    function void remove_from_queue(qos_request_t request);
        // Search and remove from appropriate queue
        foreach (critical_queue[i]) begin
            if (match_request(critical_queue[i], request)) begin
                critical_queue.delete(i);
                return;
            end
        end
        
        foreach (high_queue[i]) begin
            if (match_request(high_queue[i], request)) begin
                high_queue.delete(i);
                return;
            end
        end
        
        foreach (medium_queue[i]) begin
            if (match_request(medium_queue[i], request)) begin
                medium_queue.delete(i);
                return;
            end
        end
        
        foreach (low_queue[i]) begin
            if (match_request(low_queue[i], request)) begin
                low_queue.delete(i);
                return;
            end
        end
    endfunction
    
    // Match requests
    function bit match_request(qos_request_t a, qos_request_t b);
        return (a.id == b.id) && (a.master_id == b.master_id) && 
               (a.qos == b.qos) && (a.request_time == b.request_time);
    endfunction
    
    // Update QoS statistics
    function void update_qos_stats(qos_request_t request);
        int wait_time = request.wait_cycles;
        int qos = request.qos;
        
        // Update average wait time
        qos_avg_wait_time[qos] = (qos_avg_wait_time[qos] * (qos_grant_count[qos] - 1) + 
                                  wait_time) / qos_grant_count[qos];
        
        // Update max wait time
        if (wait_time > qos_max_wait_time[qos]) begin
            qos_max_wait_time[qos] = wait_time;
        end
    endfunction
    
    // Get QoS statistics
    function string get_qos_stats();
        string stats = "\\nQoS Arbitration Statistics:\\n";
        
        for (int qos = 0; qos < 16; qos++) begin
            if (qos_grant_count[qos] > 0) begin
                stats = {{stats, $sformatf("  QoS %2d: Grants=%6d, Avg Wait=%6.2f, Max Wait=%6d\\n",
                                          qos, qos_grant_count[qos], 
                                          qos_avg_wait_time[qos], 
                                          qos_max_wait_time[qos])}};
            end
        end
        
        return stats;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_qos_stats(), UVM_LOW)
    endfunction

endclass

`endif // AXI4_QOS_ARBITER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_qos_arbiter.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_qos_monitor(self, output_dir: str):
        """Generate QoS monitoring component"""
        content = f"""// AXI4 VIP QoS Monitor
// Generated: {datetime.datetime.now()}
// Monitors QoS compliance and performance

`ifndef AXI4_QOS_MONITOR_SV
`define AXI4_QOS_MONITOR_SV

class axi4_qos_monitor extends uvm_monitor;
    `uvm_component_utils(axi4_qos_monitor)
    
    // Analysis ports
    uvm_analysis_port #(axi4_qos_transaction) qos_ap;
    
    // Virtual interface
    virtual axi4_if vif;
    
    // QoS tracking per master
    typedef struct {{
        int total_transactions;
        int qos_distribution[16];
        real avg_latency_per_qos[16];
        int outstanding_per_qos[16];
        realtime last_request_time[16];
    }} master_qos_stats_t;
    
    master_qos_stats_t master_stats[int];
    
    // QoS violations
    int qos_violations;
    int qos_downgrades;
    int qos_upgrades;
    
    // Latency requirements per QoS level (configurable)
    int max_latency_per_qos[16] = '{{
        1000, 1000, 1000, 1000,  // Low priority
        500, 500, 500, 500,       // Medium priority
        200, 200, 200, 200,       // High priority
        100, 100, 100, 100        // Critical priority
    }};
    
    // Constructor
    function new(string name = "axi4_qos_monitor", uvm_component parent = null);
        super.new(name, parent);
        qos_ap = new("qos_ap", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
    endfunction
    
    // Main monitoring task
    task run_phase(uvm_phase phase);
        fork
            monitor_aw_channel();
            monitor_ar_channel();
            monitor_write_response();
            monitor_read_response();
            periodic_qos_check();
        join
    endtask
    
    // Monitor write address channel with QoS
    task monitor_aw_channel();
        forever begin
            @(posedge vif.clk);
            
            if (vif.awvalid && vif.awready) begin
                axi4_qos_transaction trans = new();
                trans.addr = vif.awaddr;
                trans.id = vif.awid;
                trans.qos = vif.awqos;
                trans.master_id = get_master_id(vif.awid);
                trans.is_write = 1;
                trans.start_time = $realtime;
                
                // Track transaction
                track_qos_request(trans);
                
                // Send to analysis port
                qos_ap.write(trans);
                
                `uvm_info(get_type_name(), 
                         $sformatf("AW QoS: Master=%0d, ID=%0h, QoS=%0d, Addr=%0h", 
                                  trans.master_id, trans.id, trans.qos, trans.addr), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Monitor read address channel with QoS
    task monitor_ar_channel();
        forever begin
            @(posedge vif.clk);
            
            if (vif.arvalid && vif.arready) begin
                axi4_qos_transaction trans = new();
                trans.addr = vif.araddr;
                trans.id = vif.arid;
                trans.qos = vif.arqos;
                trans.master_id = get_master_id(vif.arid);
                trans.is_write = 0;
                trans.start_time = $realtime;
                
                // Track transaction
                track_qos_request(trans);
                
                // Send to analysis port
                qos_ap.write(trans);
                
                `uvm_info(get_type_name(), 
                         $sformatf("AR QoS: Master=%0d, ID=%0h, QoS=%0d, Addr=%0h", 
                                  trans.master_id, trans.id, trans.qos, trans.addr), 
                         UVM_HIGH)
            end
        end
    endtask
    
    // Monitor write response for QoS compliance
    task monitor_write_response();
        forever begin
            @(posedge vif.clk);
            
            if (vif.bvalid && vif.bready) begin
                bit[{self.id_width-1}:0] id = vif.bid;
                int master_id = get_master_id(id);
                realtime end_time = $realtime;
                
                // Find matching request and calculate latency
                check_qos_compliance_write(id, master_id, end_time);
            end
        end
    endtask
    
    // Monitor read response for QoS compliance
    task monitor_read_response();
        forever begin
            @(posedge vif.clk);
            
            if (vif.rvalid && vif.rready && vif.rlast) begin
                bit[{self.id_width-1}:0] id = vif.rid;
                int master_id = get_master_id(id);
                realtime end_time = $realtime;
                
                // Find matching request and calculate latency
                check_qos_compliance_read(id, master_id, end_time);
            end
        end
    endtask
    
    // Track QoS request
    function void track_qos_request(axi4_qos_transaction trans);
        int master_id = trans.master_id;
        int qos = trans.qos;
        
        // Initialize stats if needed
        if (!master_stats.exists(master_id)) begin
            master_qos_stats_t new_stats;
            master_stats[master_id] = new_stats;
        end
        
        // Update statistics
        master_stats[master_id].total_transactions++;
        master_stats[master_id].qos_distribution[qos]++;
        master_stats[master_id].outstanding_per_qos[qos]++;
        master_stats[master_id].last_request_time[qos] = trans.start_time;
    endfunction
    
    // Check QoS compliance for write
    function void check_qos_compliance_write(bit[{self.id_width-1}:0] id, 
                                           int master_id, 
                                           realtime end_time);
        // Implementation would match with tracked requests
        // and verify latency meets QoS requirements
    endfunction
    
    // Check QoS compliance for read
    function void check_qos_compliance_read(bit[{self.id_width-1}:0] id,
                                          int master_id,
                                          realtime end_time);
        // Implementation would match with tracked requests
        // and verify latency meets QoS requirements
    endfunction
    
    // Periodic QoS analysis
    task periodic_qos_check();
        forever begin
            #1us;  // Check every microsecond
            
            // Analyze QoS patterns
            analyze_qos_patterns();
            
            // Check for QoS anomalies
            detect_qos_anomalies();
        end
    endtask
    
    // Analyze QoS usage patterns
    function void analyze_qos_patterns();
        foreach (master_stats[master_id]) begin
            int total = master_stats[master_id].total_transactions;
            if (total > 0) begin
                // Check QoS distribution
                for (int qos = 0; qos < 16; qos++) begin
                    real percentage = real'(master_stats[master_id].qos_distribution[qos]) / 
                                     real'(total) * 100.0;
                    
                    if (percentage > 50.0 && qos >= 12) begin
                        `uvm_warning(get_type_name(), 
                                    $sformatf("Master %0d using critical QoS excessively: %0.1f%%", 
                                             master_id, percentage))
                    end
                end
            end
        end
    endfunction
    
    // Detect QoS anomalies
    function void detect_qos_anomalies();
        // Check for QoS inversions, unusual patterns, etc.
        foreach (master_stats[master_id]) begin
            // Check if low QoS getting better service than high QoS
            for (int qos = 0; qos < 15; qos++) begin
                if (master_stats[master_id].avg_latency_per_qos[qos] < 
                    master_stats[master_id].avg_latency_per_qos[qos+1]) begin
                    `uvm_warning(get_type_name(), 
                                $sformatf("QoS inversion detected: QoS %0d faster than QoS %0d", 
                                         qos, qos+1))
                    qos_violations++;
                end
            end
        end
    endfunction
    
    // Get master ID from transaction ID
    function int get_master_id(bit[{self.id_width-1}:0] id);
        // Extract master ID from upper bits of ID
        return id[{self.id_width-1}:{self.id_width-2}];
    endfunction
    
    // Generate QoS report
    function string get_qos_report();
        string report = "\\n=== QoS Monitor Report ===\\n";
        
        foreach (master_stats[master_id]) begin
            report = {{report, $sformatf("\\nMaster %0d:\\n", master_id)}};
            report = {{report, $sformatf("  Total Transactions: %0d\\n", 
                                        master_stats[master_id].total_transactions)}};
            
            report = {{report, "  QoS Distribution:\\n"}};
            for (int qos = 0; qos < 16; qos++) begin
                if (master_stats[master_id].qos_distribution[qos] > 0) begin
                    real percentage = real'(master_stats[master_id].qos_distribution[qos]) / 
                                     real'(master_stats[master_id].total_transactions) * 100.0;
                    report = {{report, $sformatf("    QoS %2d: %6d (%5.1f%%)\\n",
                                                qos, 
                                                master_stats[master_id].qos_distribution[qos],
                                                percentage)}};
                end
            end
        end
        
        report = {{report, $sformatf("\\nQoS Violations: %0d\\n", qos_violations)}};
        report = {{report, $sformatf("QoS Downgrades: %0d\\n", qos_downgrades)}};
        report = {{report, $sformatf("QoS Upgrades: %0d\\n", qos_upgrades)}};
        
        return report;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_qos_report(), UVM_LOW)
    endfunction

endclass

// QoS transaction class
class axi4_qos_transaction extends uvm_sequence_item;
    `uvm_object_utils(axi4_qos_transaction)
    
    // Transaction fields
    bit[{self.addr_width-1}:0] addr;
    bit[{self.id_width-1}:0] id;
    bit[3:0] qos;
    int master_id;
    bit is_write;
    realtime start_time;
    realtime end_time;
    int latency_cycles;
    
    // Constructor
    function new(string name = "axi4_qos_transaction");
        super.new(name);
    endfunction
    
    // Convert to string
    function string convert2string();
        return $sformatf("QoS Trans: Master=%0d, ID=%0h, QoS=%0d, Addr=%0h, %s",
                        master_id, id, qos, addr, is_write ? "Write" : "Read");
    endfunction

endclass

`endif // AXI4_QOS_MONITOR_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_qos_monitor.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_qos_manager(self, output_dir: str):
        """Generate QoS management component"""
        content = f"""// AXI4 VIP QoS Manager
// Generated: {datetime.datetime.now()}
// Manages QoS policies and bandwidth allocation

`ifndef AXI4_QOS_MANAGER_SV
`define AXI4_QOS_MANAGER_SV

class axi4_qos_manager extends uvm_component;
    `uvm_component_utils(axi4_qos_manager)
    
    // QoS policy structure
    typedef struct {{
        string name;
        bit[3:0] min_qos;
        bit[3:0] max_qos;
        bit[3:0] default_qos;
        int bandwidth_percentage;
        int max_outstanding;
        bit allow_promotion;
        bit allow_demotion;
    }} qos_policy_t;
    
    // Master QoS policies
    qos_policy_t master_policies[int];
    
    // Slave QoS requirements
    typedef struct {{
        bit[3:0] min_required_qos;
        int max_latency_ns;
        bit strict_ordering;
        bit exclusive_high_qos;
    }} slave_qos_req_t;
    
    slave_qos_req_t slave_requirements[int];
    
    // Global QoS settings
    bit enable_qos_enforcement = 1;
    bit enable_dynamic_qos = 1;
    bit enable_qos_monitoring = 1;
    
    // Bandwidth tracking
    real master_bandwidth_usage[int];
    real qos_bandwidth_usage[16];
    realtime measurement_window = 1us;
    
    // QoS mapping table (configurable)
    bit[3:0] qos_remap_table[16] = '{{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}};
    
    // Constructor
    function new(string name = "axi4_qos_manager", uvm_component parent = null);
        super.new(name, parent);
        initialize_default_policies();
    endfunction
    
    // Initialize default policies
    function void initialize_default_policies();
        // Default master policies
        for (int i = 0; i < {self.num_masters}; i++) begin
            qos_policy_t policy;
            policy.name = $sformatf("Master_%0d_Policy", i);
            policy.min_qos = 0;
            policy.max_qos = 15;
            policy.default_qos = 4;
            policy.bandwidth_percentage = 100 / {self.num_masters};
            policy.max_outstanding = 16;
            policy.allow_promotion = 1;
            policy.allow_demotion = 0;
            master_policies[i] = policy;
        end
        
        // Default slave requirements
        for (int i = 0; i < {self.num_slaves}; i++) begin
            slave_qos_req_t req;
            req.min_required_qos = 0;
            req.max_latency_ns = 1000;
            req.strict_ordering = 0;
            req.exclusive_high_qos = 0;
            slave_requirements[i] = req;
        end
    endfunction
    
    // Set master QoS policy
    function void set_master_policy(int master_id, qos_policy_t policy);
        master_policies[master_id] = policy;
        `uvm_info(get_type_name(), 
                 $sformatf("Set policy for Master %0d: QoS range [%0d:%0d], BW=%0d%%", 
                          master_id, policy.min_qos, policy.max_qos, 
                          policy.bandwidth_percentage), 
                 UVM_MEDIUM)
    endfunction
    
    // Set slave QoS requirements
    function void set_slave_requirements(int slave_id, slave_qos_req_t req);
        slave_requirements[slave_id] = req;
        `uvm_info(get_type_name(), 
                 $sformatf("Set requirements for Slave %0d: Min QoS=%0d, Max latency=%0dns", 
                          slave_id, req.min_required_qos, req.max_latency_ns), 
                 UVM_MEDIUM)
    endfunction
    
    // Validate QoS value for master
    function bit[3:0] validate_qos(int master_id, bit[3:0] requested_qos);
        qos_policy_t policy = master_policies[master_id];
        bit[3:0] validated_qos = requested_qos;
        
        // Enforce min/max limits
        if (requested_qos < policy.min_qos) begin
            validated_qos = policy.min_qos;
            `uvm_warning(get_type_name(), 
                        $sformatf("Master %0d QoS %0d below minimum, adjusted to %0d", 
                                 master_id, requested_qos, validated_qos))
        end else if (requested_qos > policy.max_qos) begin
            validated_qos = policy.max_qos;
            `uvm_warning(get_type_name(), 
                        $sformatf("Master %0d QoS %0d above maximum, adjusted to %0d", 
                                 master_id, requested_qos, validated_qos))
        end
        
        // Apply remapping if enabled
        validated_qos = qos_remap_table[validated_qos];
        
        return validated_qos;
    endfunction
    
    // Check if QoS promotion is allowed
    function bit can_promote_qos(int master_id, bit[3:0] current_qos, bit[3:0] new_qos);
        qos_policy_t policy = master_policies[master_id];
        
        if (!policy.allow_promotion) return 0;
        if (new_qos > policy.max_qos) return 0;
        if (new_qos <= current_qos) return 0;
        
        // Check bandwidth constraints
        if (!check_bandwidth_available(master_id, new_qos)) return 0;
        
        return 1;
    endfunction
    
    // Dynamic QoS adjustment
    function bit[3:0] adjust_qos_dynamic(int master_id, bit[3:0] base_qos, 
                                        real urgency_factor);
        bit[3:0] adjusted_qos = base_qos;
        
        if (!enable_dynamic_qos) return base_qos;
        
        // Calculate adjustment based on urgency
        int adjustment = int'(urgency_factor * 4);  // Max 4 levels adjustment
        
        // Apply adjustment within policy limits
        adjusted_qos = base_qos + adjustment;
        adjusted_qos = validate_qos(master_id, adjusted_qos);
        
        return adjusted_qos;
    endfunction
    
    // Check bandwidth availability
    function bit check_bandwidth_available(int master_id, bit[3:0] qos);
        real required_bw = calculate_required_bandwidth(qos);
        real available_bw = 100.0 - get_total_bandwidth_usage();
        
        return (required_bw <= available_bw);
    endfunction
    
    // Calculate required bandwidth for QoS level
    function real calculate_required_bandwidth(bit[3:0] qos);
        // Higher QoS requires more bandwidth reservation
        case (qos)
            15, 14, 13, 12: return 25.0;  // Critical
            11, 10, 9, 8:   return 15.0;  // High
            7, 6, 5, 4:     return 10.0;  // Medium
            default:        return 5.0;   // Low
        endcase
    endfunction
    
    // Get total bandwidth usage
    function real get_total_bandwidth_usage();
        real total = 0.0;
        foreach (master_bandwidth_usage[i]) begin
            total += master_bandwidth_usage[i];
        end
        return total;
    endfunction
    
    // Update bandwidth usage
    function void update_bandwidth_usage(int master_id, real usage);
        master_bandwidth_usage[master_id] = usage;
        
        // Check for bandwidth violations
        if (usage > master_policies[master_id].bandwidth_percentage) begin
            `uvm_warning(get_type_name(), 
                        $sformatf("Master %0d exceeding bandwidth allocation: %0.1f%% > %0d%%", 
                                 master_id, usage, 
                                 master_policies[master_id].bandwidth_percentage))
        end
    endfunction
    
    // Get QoS recommendation for transaction
    function bit[3:0] get_qos_recommendation(int master_id, int slave_id, 
                                           bit is_urgent, bit is_exclusive);
        qos_policy_t master_policy = master_policies[master_id];
        slave_qos_req_t slave_req = slave_requirements[slave_id];
        bit[3:0] recommended_qos = master_policy.default_qos;
        
        // Adjust for slave requirements
        if (slave_req.min_required_qos > recommended_qos) begin
            recommended_qos = slave_req.min_required_qos;
        end
        
        // Adjust for urgency
        if (is_urgent) begin
            recommended_qos = recommended_qos + 4;
            if (recommended_qos > 15) recommended_qos = 15;
        end
        
        // Adjust for exclusive access
        if (is_exclusive && slave_req.exclusive_high_qos) begin
            recommended_qos = (recommended_qos < 12) ? 12 : recommended_qos;
        end
        
        // Validate against master policy
        recommended_qos = validate_qos(master_id, recommended_qos);
        
        return recommended_qos;
    endfunction
    
    // Generate QoS configuration
    function void generate_qos_config(string filename);
        int fd = $fopen(filename, "w");
        
        if (fd) begin
            $fwrite(fd, "// AXI4 QoS Configuration\\n");
            $fwrite(fd, "// Generated: %s\\n\\n", $sformatf("%0t", $time));
            
            // Master policies
            $fwrite(fd, "// Master QoS Policies\\n");
            foreach (master_policies[id]) begin
                qos_policy_t p = master_policies[id];
                $fwrite(fd, "Master %0d: %s\\n", id, p.name);
                $fwrite(fd, "  QoS Range: [%0d:%0d], Default: %0d\\n", 
                       p.min_qos, p.max_qos, p.default_qos);
                $fwrite(fd, "  Bandwidth: %0d%%, Max Outstanding: %0d\\n", 
                       p.bandwidth_percentage, p.max_outstanding);
                $fwrite(fd, "  Promotion: %s, Demotion: %s\\n\\n",
                       p.allow_promotion ? "Allowed" : "Disabled",
                       p.allow_demotion ? "Allowed" : "Disabled");
            end
            
            // Slave requirements
            $fwrite(fd, "// Slave QoS Requirements\\n");
            foreach (slave_requirements[id]) begin
                slave_qos_req_t r = slave_requirements[id];
                $fwrite(fd, "Slave %0d:\\n", id);
                $fwrite(fd, "  Min QoS: %0d, Max Latency: %0dns\\n",
                       r.min_required_qos, r.max_latency_ns);
                $fwrite(fd, "  Strict Ordering: %s, Exclusive High QoS: %s\\n\\n",
                       r.strict_ordering ? "Yes" : "No",
                       r.exclusive_high_qos ? "Yes" : "No");
            end
            
            // QoS remapping table
            $fwrite(fd, "// QoS Remapping Table\\n");
            for (int i = 0; i < 16; i++) begin
                if (qos_remap_table[i] != i) begin
                    $fwrite(fd, "QoS %2d -> %2d\\n", i, qos_remap_table[i]);
                end
            end
            
            $fclose(fd);
            `uvm_info(get_type_name(), 
                     $sformatf("QoS configuration saved to %s", filename), 
                     UVM_LOW)
        end
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "QoS Manager Summary:", UVM_LOW)
        
        // Report bandwidth usage
        foreach (master_bandwidth_usage[id]) begin
            `uvm_info(get_type_name(), 
                     $sformatf("  Master %0d bandwidth usage: %0.1f%%", 
                              id, master_bandwidth_usage[id]), 
                     UVM_LOW)
        end
        
        // Save configuration
        generate_qos_config("qos_config.txt");
    endfunction

endclass

`endif // AXI4_QOS_MANAGER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_qos_manager.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_qos_scheduler(self, output_dir: str):
        """Generate QoS-aware transaction scheduler"""
        content = f"""// AXI4 VIP QoS Scheduler
// Generated: {datetime.datetime.now()}
// Schedules transactions based on QoS priorities

`ifndef AXI4_QOS_SCHEDULER_SV
`define AXI4_QOS_SCHEDULER_SV

class axi4_qos_scheduler extends uvm_component;
    `uvm_component_utils(axi4_qos_scheduler)
    
    // Transaction queue entry
    typedef struct {{
        axi4_transaction trans;
        bit[3:0] qos;
        realtime enqueue_time;
        realtime deadline;
        int priority_score;
        bit scheduled;
        bit completed;
    }} sched_entry_t;
    
    // Scheduling queues per master
    sched_entry_t write_queue[int][$];
    sched_entry_t read_queue[int][$];
    
    // QoS scheduling parameters
    int qos_time_slices[16] = '{{1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4}};
    int qos_burst_sizes[16] = '{{1, 1, 2, 2, 4, 4, 8, 8, 16, 16, 32, 32, 64, 64, 128, 128}};
    
    // Scheduling algorithm
    typedef enum {{
        STRICT_QOS_PRIORITY,
        WEIGHTED_FAIR_QUEUING,
        EARLIEST_DEADLINE_FIRST,
        RATE_MONOTONIC,
        DYNAMIC_PRIORITY
    }} scheduling_algorithm_e;
    
    scheduling_algorithm_e algorithm = WEIGHTED_FAIR_QUEUING;
    
    // Performance counters
    int transactions_scheduled[16];
    real avg_wait_time[16];
    int deadline_misses[16];
    
    // Constructor
    function new(string name = "axi4_qos_scheduler", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Add transaction to schedule
    function void add_transaction(axi4_transaction trans, bit[3:0] qos, int master_id);
        sched_entry_t entry;
        entry.trans = trans;
        entry.qos = qos;
        entry.enqueue_time = $realtime;
        entry.deadline = calculate_deadline(trans, qos);
        entry.priority_score = calculate_priority(trans, qos);
        entry.scheduled = 0;
        entry.completed = 0;
        
        if (trans.is_write) begin
            write_queue[master_id].push_back(entry);
        end else begin
            read_queue[master_id].push_back(entry);
        end
        
        `uvm_info(get_type_name(), 
                 $sformatf("Added transaction: Master=%0d, QoS=%0d, Priority=%0d", 
                          master_id, qos, entry.priority_score), 
                 UVM_HIGH)
    endfunction
    
    // Schedule next transaction
    function sched_entry_t schedule_next_transaction(bit is_write);
        sched_entry_t selected;
        selected.qos = -1;  // Invalid marker
        
        case (algorithm)
            STRICT_QOS_PRIORITY:      selected = schedule_strict_priority(is_write);
            WEIGHTED_FAIR_QUEUING:    selected = schedule_wfq(is_write);
            EARLIEST_DEADLINE_FIRST:  selected = schedule_edf(is_write);
            RATE_MONOTONIC:          selected = schedule_rate_monotonic(is_write);
            DYNAMIC_PRIORITY:        selected = schedule_dynamic_priority(is_write);
        endcase
        
        if (selected.qos != -1) begin
            transactions_scheduled[selected.qos]++;
            update_wait_time(selected);
            check_deadline(selected);
        end
        
        return selected;
    endfunction
    
    // Strict QoS priority scheduling
    function sched_entry_t schedule_strict_priority(bit is_write);
        sched_entry_t best;
        best.qos = -1;
        int best_qos = -1;
        
        foreach (is_write ? write_queue : read_queue[master_id]) begin
            sched_entry_t queue[$] = is_write ? write_queue[master_id] : read_queue[master_id];
            foreach (queue[i]) begin
                if (!queue[i].scheduled && queue[i].qos > best_qos) begin
                    best = queue[i];
                    best_qos = queue[i].qos;
                end
            end
        end
        
        if (best.qos != -1) begin
            mark_scheduled(best);
        end
        
        return best;
    endfunction
    
    // Weighted Fair Queuing
    function sched_entry_t schedule_wfq(bit is_write);
        sched_entry_t best;
        best.qos = -1;
        real best_finish_time = 1e9;
        
        foreach (is_write ? write_queue : read_queue[master_id]) begin
            sched_entry_t queue[$] = is_write ? write_queue[master_id] : read_queue[master_id];
            foreach (queue[i]) begin
                if (!queue[i].scheduled) begin
                    real virtual_finish_time = calculate_virtual_finish_time(queue[i]);
                    if (virtual_finish_time < best_finish_time) begin
                        best = queue[i];
                        best_finish_time = virtual_finish_time;
                    end
                end
            end
        end
        
        if (best.qos != -1) begin
            mark_scheduled(best);
        end
        
        return best;
    endfunction
    
    // Earliest Deadline First
    function sched_entry_t schedule_edf(bit is_write);
        sched_entry_t best;
        best.qos = -1;
        realtime earliest_deadline = 1s;  // Far future
        
        foreach (is_write ? write_queue : read_queue[master_id]) begin
            sched_entry_t queue[$] = is_write ? write_queue[master_id] : read_queue[master_id];
            foreach (queue[i]) begin
                if (!queue[i].scheduled && queue[i].deadline < earliest_deadline) begin
                    best = queue[i];
                    earliest_deadline = queue[i].deadline;
                end
            end
        end
        
        if (best.qos != -1) begin
            mark_scheduled(best);
        end
        
        return best;
    endfunction
    
    // Rate Monotonic Scheduling
    function sched_entry_t schedule_rate_monotonic(bit is_write);
        sched_entry_t best;
        best.qos = -1;
        int shortest_period = 1000000;
        
        foreach (is_write ? write_queue : read_queue[master_id]) begin
            sched_entry_t queue[$] = is_write ? write_queue[master_id] : read_queue[master_id];
            foreach (queue[i]) begin
                if (!queue[i].scheduled) begin
                    int period = calculate_period(queue[i].qos);
                    if (period < shortest_period) begin
                        best = queue[i];
                        shortest_period = period;
                    end
                end
            end
        end
        
        if (best.qos != -1) begin
            mark_scheduled(best);
        end
        
        return best;
    endfunction
    
    // Dynamic Priority Scheduling
    function sched_entry_t schedule_dynamic_priority(bit is_write);
        sched_entry_t best;
        best.qos = -1;
        int highest_priority = -1;
        
        foreach (is_write ? write_queue : read_queue[master_id]) begin
            sched_entry_t queue[$] = is_write ? write_queue[master_id] : read_queue[master_id];
            foreach (queue[i]) begin
                if (!queue[i].scheduled) begin
                    // Update dynamic priority based on wait time
                    queue[i].priority_score = calculate_dynamic_priority(queue[i]);
                    
                    if (queue[i].priority_score > highest_priority) begin
                        best = queue[i];
                        highest_priority = queue[i].priority_score;
                    end
                end
            end
        end
        
        if (best.qos != -1) begin
            mark_scheduled(best);
        end
        
        return best;
    endfunction
    
    // Calculate deadline based on QoS
    function realtime calculate_deadline(axi4_transaction trans, bit[3:0] qos);
        realtime deadline;
        
        // Base deadline from QoS level (in nanoseconds)
        case (qos)
            15, 14, 13, 12: deadline = 100ns;   // Critical
            11, 10, 9, 8:   deadline = 500ns;   // High
            7, 6, 5, 4:     deadline = 1us;     // Medium
            default:        deadline = 10us;    // Low
        endcase
        
        // Adjust for transaction size
        int bytes = (trans.len + 1) * (1 << trans.size);
        deadline = deadline + (bytes * 1ns);  // 1ns per byte
        
        return $realtime + deadline;
    endfunction
    
    // Calculate priority score
    function int calculate_priority(axi4_transaction trans, bit[3:0] qos);
        int priority = qos * 100;  // Base priority from QoS
        
        // Adjust for transaction characteristics
        if (trans.lock) priority += 50;  // Exclusive access
        if (trans.len == 0) priority += 20;  // Single beat
        
        return priority;
    endfunction
    
    // Calculate virtual finish time for WFQ
    function real calculate_virtual_finish_time(sched_entry_t entry);
        real service_time = real'(entry.trans.len + 1) / real'(qos_time_slices[entry.qos]);
        real wait_time = $realtime - entry.enqueue_time;
        return wait_time + service_time;
    endfunction
    
    // Calculate period for rate monotonic
    function int calculate_period(bit[3:0] qos);
        // Higher QoS = shorter period
        return 1000 / (qos + 1);  // In cycles
    endfunction
    
    // Calculate dynamic priority
    function int calculate_dynamic_priority(sched_entry_t entry);
        realtime wait_time = $realtime - entry.enqueue_time;
        int base_priority = entry.qos * 100;
        int wait_bonus = int'(wait_time / 10ns);  // Bonus for waiting
        int deadline_factor = 0;
        
        // Increase priority as deadline approaches
        if (entry.deadline > $realtime) begin
            realtime time_to_deadline = entry.deadline - $realtime;
            deadline_factor = 1000 / int'(time_to_deadline / 1ns);
        end else begin
            deadline_factor = 1000;  // Past deadline - highest urgency
        end
        
        return base_priority + wait_bonus + deadline_factor;
    endfunction
    
    // Mark entry as scheduled
    function void mark_scheduled(sched_entry_t entry);
        // Find and mark in appropriate queue
        foreach (write_queue[master_id]) begin
            foreach (write_queue[master_id][i]) begin
                if (match_entry(write_queue[master_id][i], entry)) begin
                    write_queue[master_id][i].scheduled = 1;
                    return;
                end
            end
        end
        
        foreach (read_queue[master_id]) begin
            foreach (read_queue[master_id][i]) begin
                if (match_entry(read_queue[master_id][i], entry)) begin
                    read_queue[master_id][i].scheduled = 1;
                    return;
                end
            end
        end
    endfunction
    
    // Match entries
    function bit match_entry(sched_entry_t a, sched_entry_t b);
        return (a.trans == b.trans) && (a.qos == b.qos) && 
               (a.enqueue_time == b.enqueue_time);
    endfunction
    
    // Update wait time statistics
    function void update_wait_time(sched_entry_t entry);
        realtime wait = $realtime - entry.enqueue_time;
        int qos = entry.qos;
        
        // Update average
        avg_wait_time[qos] = (avg_wait_time[qos] * (transactions_scheduled[qos] - 1) + 
                             wait) / transactions_scheduled[qos];
    endfunction
    
    // Check deadline
    function void check_deadline(sched_entry_t entry);
        if ($realtime > entry.deadline) begin
            deadline_misses[entry.qos]++;
            `uvm_warning(get_type_name(), 
                        $sformatf("Deadline miss: QoS=%0d, Late by %0.2fns", 
                                 entry.qos, $realtime - entry.deadline))
        end
    endfunction
    
    // Clean completed entries
    function void cleanup_completed();
        foreach (write_queue[master_id]) begin
            write_queue[master_id] = write_queue[master_id].find(item) with 
                                    (!item.completed);
        end
        
        foreach (read_queue[master_id]) begin
            read_queue[master_id] = read_queue[master_id].find(item) with 
                                  (!item.completed);
        end
    endfunction
    
    // Get scheduling statistics
    function string get_scheduling_stats();
        string stats = "\\nQoS Scheduling Statistics:\\n";
        
        for (int qos = 0; qos < 16; qos++) begin
            if (transactions_scheduled[qos] > 0) begin
                stats = {{stats, $sformatf(
                    "  QoS %2d: Scheduled=%6d, Avg Wait=%6.2fns, Deadline Misses=%3d\\n",
                    qos, transactions_scheduled[qos], avg_wait_time[qos], 
                    deadline_misses[qos]
                )}};
            end
        end
        
        return stats;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_scheduling_stats(), UVM_LOW)
    endfunction

endclass

`endif // AXI4_QOS_SCHEDULER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_qos_scheduler.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_qos_enforcer(self, output_dir: str):
        """Generate QoS enforcement component"""
        content = f"""// AXI4 VIP QoS Enforcer
// Generated: {datetime.datetime.now()}
// Enforces QoS policies and service level agreements

`ifndef AXI4_QOS_ENFORCER_SV
`define AXI4_QOS_ENFORCER_SV

class axi4_qos_enforcer extends uvm_component;
    `uvm_component_utils(axi4_qos_enforcer)
    
    // Service Level Agreement (SLA) definition
    typedef struct {{
        string name;
        bit[3:0] qos_level;
        int min_bandwidth_mbps;
        int max_latency_ns;
        real target_throughput;
        int max_jitter_ns;
        bit guaranteed_service;
    }} qos_sla_t;
    
    // QoS SLAs per level
    qos_sla_t sla_definitions[16];
    
    // Enforcement actions
    typedef enum {{
        NO_ACTION,
        THROTTLE_LOWER_QOS,
        BOOST_PRIORITY,
        REJECT_REQUEST,
        PREEMPT_LOWER,
        REPORT_VIOLATION
    }} enforcement_action_e;
    
    // Violation tracking
    typedef struct {{
        int bandwidth_violations;
        int latency_violations;
        int jitter_violations;
        realtime last_violation_time;
        string last_violation_reason;
    }} violation_record_t;
    
    violation_record_t violations[16];
    
    // Real-time metrics per QoS
    real current_bandwidth[16];
    real current_latency[16];
    real current_jitter[16];
    int active_transactions[16];
    
    // Enforcement configuration
    bit strict_enforcement = 1;
    bit allow_temporary_violations = 1;
    int violation_threshold = 3;
    realtime violation_window = 1ms;
    
    // Preemption support
    bit enable_preemption = 1;
    int preemption_count = 0;
    
    // Constructor
    function new(string name = "axi4_qos_enforcer", uvm_component parent = null);
        super.new(name, parent);
        initialize_slas();
    endfunction
    
    // Initialize default SLAs
    function void initialize_slas();
        // Critical priority (QoS 12-15)
        for (int i = 12; i <= 15; i++) begin
            sla_definitions[i].name = $sformatf("Critical_QoS_%0d", i);
            sla_definitions[i].qos_level = i;
            sla_definitions[i].min_bandwidth_mbps = 1000;
            sla_definitions[i].max_latency_ns = 100;
            sla_definitions[i].target_throughput = 0.95;
            sla_definitions[i].max_jitter_ns = 20;
            sla_definitions[i].guaranteed_service = 1;
        end
        
        // High priority (QoS 8-11)
        for (int i = 8; i <= 11; i++) begin
            sla_definitions[i].name = $sformatf("High_QoS_%0d", i);
            sla_definitions[i].qos_level = i;
            sla_definitions[i].min_bandwidth_mbps = 500;
            sla_definitions[i].max_latency_ns = 500;
            sla_definitions[i].target_throughput = 0.90;
            sla_definitions[i].max_jitter_ns = 100;
            sla_definitions[i].guaranteed_service = 1;
        end
        
        // Medium priority (QoS 4-7)
        for (int i = 4; i <= 7; i++) begin
            sla_definitions[i].name = $sformatf("Medium_QoS_%0d", i);
            sla_definitions[i].qos_level = i;
            sla_definitions[i].min_bandwidth_mbps = 200;
            sla_definitions[i].max_latency_ns = 1000;
            sla_definitions[i].target_throughput = 0.80;
            sla_definitions[i].max_jitter_ns = 500;
            sla_definitions[i].guaranteed_service = 0;
        end
        
        // Low priority (QoS 0-3)
        for (int i = 0; i <= 3; i++) begin
            sla_definitions[i].name = $sformatf("Low_QoS_%0d", i);
            sla_definitions[i].qos_level = i;
            sla_definitions[i].min_bandwidth_mbps = 50;
            sla_definitions[i].max_latency_ns = 10000;
            sla_definitions[i].target_throughput = 0.50;
            sla_definitions[i].max_jitter_ns = 5000;
            sla_definitions[i].guaranteed_service = 0;
        end
    endfunction
    
    // Check transaction against QoS policy
    function enforcement_action_e check_transaction(axi4_transaction trans, 
                                                   bit[3:0] qos);
        enforcement_action_e action = NO_ACTION;
        qos_sla_t sla = sla_definitions[qos];
        
        // Check current metrics against SLA
        if (!check_bandwidth_compliance(qos, sla)) begin
            action = handle_bandwidth_violation(qos, sla);
        end
        
        if (!check_latency_compliance(qos, sla)) begin
            if (action == NO_ACTION) begin
                action = handle_latency_violation(qos, sla);
            end
        end
        
        if (!check_jitter_compliance(qos, sla)) begin
            if (action == NO_ACTION) begin
                action = handle_jitter_violation(qos, sla);
            end
        end
        
        // Log enforcement action
        if (action != NO_ACTION) begin
            `uvm_info(get_type_name(), 
                     $sformatf("Enforcement action for QoS %0d: %s", 
                              qos, action.name()), 
                     UVM_MEDIUM)
        end
        
        return action;
    endfunction
    
    // Check bandwidth compliance
    function bit check_bandwidth_compliance(bit[3:0] qos, qos_sla_t sla);
        if (current_bandwidth[qos] < sla.min_bandwidth_mbps) begin
            violations[qos].bandwidth_violations++;
            violations[qos].last_violation_time = $realtime;
            violations[qos].last_violation_reason = "Bandwidth below minimum";
            return 0;
        end
        return 1;
    endfunction
    
    // Check latency compliance
    function bit check_latency_compliance(bit[3:0] qos, qos_sla_t sla);
        if (current_latency[qos] > sla.max_latency_ns) begin
            violations[qos].latency_violations++;
            violations[qos].last_violation_time = $realtime;
            violations[qos].last_violation_reason = "Latency exceeds maximum";
            return 0;
        end
        return 1;
    endfunction
    
    // Check jitter compliance
    function bit check_jitter_compliance(bit[3:0] qos, qos_sla_t sla);
        if (current_jitter[qos] > sla.max_jitter_ns) begin
            violations[qos].jitter_violations++;
            violations[qos].last_violation_time = $realtime;
            violations[qos].last_violation_reason = "Jitter exceeds maximum";
            return 0;
        end
        return 1;
    endfunction
    
    // Handle bandwidth violation
    function enforcement_action_e handle_bandwidth_violation(bit[3:0] qos, 
                                                           qos_sla_t sla);
        if (sla.guaranteed_service) begin
            // For guaranteed service, boost priority or throttle others
            if (can_throttle_lower_qos(qos)) begin
                return THROTTLE_LOWER_QOS;
            end else begin
                return BOOST_PRIORITY;
            end
        end else begin
            // For best effort, just report
            return REPORT_VIOLATION;
        end
    endfunction
    
    // Handle latency violation
    function enforcement_action_e handle_latency_violation(bit[3:0] qos, 
                                                         qos_sla_t sla);
        if (sla.guaranteed_service && enable_preemption) begin
            // Preempt lower priority transactions
            if (can_preempt_lower_qos(qos)) begin
                return PREEMPT_LOWER;
            end
        end
        
        // Otherwise boost priority
        return BOOST_PRIORITY;
    endfunction
    
    // Handle jitter violation
    function enforcement_action_e handle_jitter_violation(bit[3:0] qos, 
                                                        qos_sla_t sla);
        // Jitter violations typically need traffic shaping
        return THROTTLE_LOWER_QOS;
    endfunction
    
    // Check if lower QoS can be throttled
    function bit can_throttle_lower_qos(bit[3:0] min_qos);
        for (int qos = 0; qos < min_qos; qos++) begin
            if (active_transactions[qos] > 0 && 
                !sla_definitions[qos].guaranteed_service) begin
                return 1;
            end
        end
        return 0;
    endfunction
    
    // Check if lower QoS can be preempted
    function bit can_preempt_lower_qos(bit[3:0] min_qos);
        for (int qos = 0; qos < min_qos; qos++) begin
            if (active_transactions[qos] > 0) begin
                return 1;
            end
        end
        return 0;
    endfunction
    
    // Execute enforcement action
    function void execute_enforcement(enforcement_action_e action, bit[3:0] qos);
        case (action)
            THROTTLE_LOWER_QOS: begin
                throttle_lower_priority(qos);
            end
            
            BOOST_PRIORITY: begin
                boost_qos_priority(qos);
            end
            
            REJECT_REQUEST: begin
                `uvm_warning(get_type_name(), 
                            $sformatf("Rejecting request for QoS %0d due to SLA violation", 
                                     qos))
            end
            
            PREEMPT_LOWER: begin
                preempt_lower_priority(qos);
                preemption_count++;
            end
            
            REPORT_VIOLATION: begin
                report_sla_violation(qos);
            end
        endcase
    endfunction
    
    // Throttle lower priority traffic
    function void throttle_lower_priority(bit[3:0] min_qos);
        `uvm_info(get_type_name(), 
                 $sformatf("Throttling QoS levels below %0d", min_qos), 
                 UVM_MEDIUM)
        
        // Implementation would reduce bandwidth for lower QoS
        for (int qos = 0; qos < min_qos; qos++) begin
            if (!sla_definitions[qos].guaranteed_service) begin
                // Reduce allowed bandwidth
            end
        end
    endfunction
    
    // Boost QoS priority
    function void boost_qos_priority(bit[3:0] qos);
        `uvm_info(get_type_name(), 
                 $sformatf("Boosting priority for QoS %0d", qos), 
                 UVM_MEDIUM)
        
        // Implementation would temporarily increase priority
    endfunction
    
    // Preempt lower priority transactions
    function void preempt_lower_priority(bit[3:0] min_qos);
        `uvm_info(get_type_name(), 
                 $sformatf("Preempting transactions below QoS %0d", min_qos), 
                 UVM_MEDIUM)
        
        // Implementation would cancel/defer lower priority transactions
    endfunction
    
    // Report SLA violation
    function void report_sla_violation(bit[3:0] qos);
        violation_record_t vr = violations[qos];
        
        `uvm_warning(get_type_name(), 
                    $sformatf("SLA Violation for QoS %0d: %s\\n" +
                             "  Bandwidth violations: %0d\\n" +
                             "  Latency violations: %0d\\n" +
                             "  Jitter violations: %0d\\n" +
                             "  Last violation: %0t",
                             qos, vr.last_violation_reason,
                             vr.bandwidth_violations,
                             vr.latency_violations,
                             vr.jitter_violations,
                             vr.last_violation_time))
    endfunction
    
    // Update real-time metrics
    function void update_metrics(bit[3:0] qos, real bandwidth, 
                                real latency, real jitter);
        current_bandwidth[qos] = bandwidth;
        current_latency[qos] = latency;
        current_jitter[qos] = jitter;
    endfunction
    
    // Check if SLA is being met
    function bit is_sla_met(bit[3:0] qos);
        qos_sla_t sla = sla_definitions[qos];
        
        return (current_bandwidth[qos] >= sla.min_bandwidth_mbps) &&
               (current_latency[qos] <= sla.max_latency_ns) &&
               (current_jitter[qos] <= sla.max_jitter_ns);
    endfunction
    
    // Generate SLA report
    function string get_sla_report();
        string report = "\\n=== QoS SLA Compliance Report ===\\n";
        
        for (int qos = 0; qos < 16; qos++) begin
            if (active_transactions[qos] > 0 || violations[qos].bandwidth_violations > 0 ||
                violations[qos].latency_violations > 0 || violations[qos].jitter_violations > 0) begin
                
                qos_sla_t sla = sla_definitions[qos];
                bit met = is_sla_met(qos);
                
                report = {{report, $sformatf("\\nQoS Level %0d (%s):\\n", qos, sla.name)}};
                report = {{report, $sformatf("  SLA Status: %s\\n", met ? "MET" : "VIOLATED")}};
                report = {{report, $sformatf("  Current Bandwidth: %0.1f Mbps (min: %0d)\\n",
                                            current_bandwidth[qos], sla.min_bandwidth_mbps)}};
                report = {{report, $sformatf("  Current Latency: %0.1f ns (max: %0d)\\n",
                                            current_latency[qos], sla.max_latency_ns)}};
                report = {{report, $sformatf("  Current Jitter: %0.1f ns (max: %0d)\\n",
                                            current_jitter[qos], sla.max_jitter_ns)}};
                report = {{report, $sformatf("  Violations - BW: %0d, Latency: %0d, Jitter: %0d\\n",
                                            violations[qos].bandwidth_violations,
                                            violations[qos].latency_violations,
                                            violations[qos].jitter_violations)}};
            end
        end
        
        report = {{report, $sformatf("\\nTotal Preemptions: %0d\\n", preemption_count)}};
        
        return report;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_sla_report(), UVM_LOW)
    endfunction

endclass

`endif // AXI4_QOS_ENFORCER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_qos_enforcer.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_qos_analyzer(self, output_dir: str):
        """Generate QoS analysis component"""
        content = f"""// AXI4 VIP QoS Analyzer
// Generated: {datetime.datetime.now()}
// Analyzes QoS patterns and provides optimization recommendations

`ifndef AXI4_QOS_ANALYZER_SV
`define AXI4_QOS_ANALYZER_SV

class axi4_qos_analyzer extends uvm_component;
    `uvm_component_utils(axi4_qos_analyzer)
    
    // Analysis window configuration
    realtime analysis_window = 10us;
    int sample_count = 0;
    
    // QoS pattern analysis
    typedef struct {{
        int usage_count;
        real avg_bandwidth;
        real peak_bandwidth;
        real avg_latency;
        real min_latency;
        real max_latency;
        int burst_count;
        real efficiency;
    }} qos_pattern_t;
    
    qos_pattern_t qos_patterns[16];
    
    // Master behavior analysis
    typedef struct {{
        int qos_distribution[16];
        real qos_switching_rate;
        bit qos_stable;
        string access_pattern;
        real bandwidth_utilization;
    }} master_behavior_t;
    
    master_behavior_t master_behaviors[int];
    
    // System-wide QoS metrics
    real system_qos_efficiency;
    real qos_fairness_index;
    int qos_conflicts;
    int qos_starvation_events;
    
    // Optimization recommendations
    string recommendations[$];
    
    // Constructor
    function new(string name = "axi4_qos_analyzer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Analyze transaction with QoS
    function void analyze_transaction(axi4_transaction trans, bit[3:0] qos, 
                                    int master_id, real latency);
        // Update QoS pattern
        update_qos_pattern(qos, trans, latency);
        
        // Update master behavior
        update_master_behavior(master_id, qos, trans);
        
        // Perform periodic analysis
        sample_count++;
        if (sample_count % 1000 == 0) begin
            perform_comprehensive_analysis();
        end
    endfunction
    
    // Update QoS pattern analysis
    function void update_qos_pattern(bit[3:0] qos, axi4_transaction trans, 
                                   real latency);
        qos_patterns[qos].usage_count++;
        
        // Calculate bandwidth
        int bytes = (trans.len + 1) * (1 << trans.size);
        real bandwidth = real'(bytes) / latency;
        
        // Update averages
        real n = real'(qos_patterns[qos].usage_count);
        qos_patterns[qos].avg_bandwidth = 
            (qos_patterns[qos].avg_bandwidth * (n-1) + bandwidth) / n;
        qos_patterns[qos].avg_latency = 
            (qos_patterns[qos].avg_latency * (n-1) + latency) / n;
        
        // Update min/max
        if (bandwidth > qos_patterns[qos].peak_bandwidth)
            qos_patterns[qos].peak_bandwidth = bandwidth;
        if (latency < qos_patterns[qos].min_latency || qos_patterns[qos].min_latency == 0)
            qos_patterns[qos].min_latency = latency;
        if (latency > qos_patterns[qos].max_latency)
            qos_patterns[qos].max_latency = latency;
        
        // Track bursts
        if (trans.len > 0) qos_patterns[qos].burst_count++;
        
        // Calculate efficiency
        qos_patterns[qos].efficiency = calculate_qos_efficiency(qos);
    endfunction
    
    // Update master behavior analysis
    function void update_master_behavior(int master_id, bit[3:0] qos, 
                                       axi4_transaction trans);
        if (!master_behaviors.exists(master_id)) begin
            master_behavior_t new_behavior;
            master_behaviors[master_id] = new_behavior;
        end
        
        master_behaviors[master_id].qos_distribution[qos]++;
        
        // Analyze access pattern
        analyze_access_pattern(master_id, trans);
        
        // Calculate QoS stability
        analyze_qos_stability(master_id);
    endfunction
    
    // Perform comprehensive analysis
    function void perform_comprehensive_analysis();
        // Analyze QoS distribution
        analyze_qos_distribution();
        
        // Analyze QoS efficiency
        analyze_qos_efficiency();
        
        // Analyze fairness
        analyze_qos_fairness();
        
        // Detect anomalies
        detect_qos_anomalies();
        
        // Generate recommendations
        generate_recommendations();
    endfunction
    
    // Analyze QoS distribution across system
    function void analyze_qos_distribution();
        int total_transactions = 0;
        int qos_histogram[16];
        
        // Build histogram
        for (int qos = 0; qos < 16; qos++) begin
            qos_histogram[qos] = qos_patterns[qos].usage_count;
            total_transactions += qos_patterns[qos].usage_count;
        end
        
        // Check for imbalance
        if (total_transactions > 0) begin
            // Check if critical QoS overused
            real critical_percentage = real'(qos_histogram[15] + qos_histogram[14] + 
                                           qos_histogram[13] + qos_histogram[12]) / 
                                     real'(total_transactions) * 100.0;
            
            if (critical_percentage > 25.0) begin
                recommendations.push_back(
                    $sformatf("High critical QoS usage (%0.1f%%). Consider redistributing priorities.",
                             critical_percentage)
                );
            end
            
            // Check for unused QoS levels
            for (int qos = 0; qos < 16; qos++) begin
                if (qos_histogram[qos] == 0 && qos >= 4 && qos <= 11) begin
                    recommendations.push_back(
                        $sformatf("QoS level %0d unused. Consider consolidating QoS levels.", qos)
                    );
                end
            end
        end
    endfunction
    
    // Analyze QoS efficiency
    function void analyze_qos_efficiency();
        real total_efficiency = 0.0;
        int active_qos_levels = 0;
        
        for (int qos = 0; qos < 16; qos++) begin
            if (qos_patterns[qos].usage_count > 0) begin
                qos_patterns[qos].efficiency = calculate_qos_efficiency(qos);
                total_efficiency += qos_patterns[qos].efficiency;
                active_qos_levels++;
                
                // Check for inefficient QoS usage
                if (qos_patterns[qos].efficiency < 0.7) begin
                    recommendations.push_back(
                        $sformatf("QoS %0d operating at low efficiency (%0.1f%%). Review allocation.",
                                 qos, qos_patterns[qos].efficiency * 100.0)
                    );
                end
            end
        end
        
        if (active_qos_levels > 0) begin
            system_qos_efficiency = total_efficiency / real'(active_qos_levels);
        end
    endfunction
    
    // Calculate QoS efficiency
    function real calculate_qos_efficiency(bit[3:0] qos);
        if (qos_patterns[qos].usage_count == 0) return 0.0;
        
        // Efficiency based on bandwidth utilization and latency achievement
        real bw_efficiency = qos_patterns[qos].avg_bandwidth / 
                           qos_patterns[qos].peak_bandwidth;
        
        // Expected latency based on QoS level
        real expected_latency = get_expected_latency(qos);
        real latency_efficiency = expected_latency / qos_patterns[qos].avg_latency;
        if (latency_efficiency > 1.0) latency_efficiency = 1.0;
        
        return (bw_efficiency * 0.5 + latency_efficiency * 0.5);
    endfunction
    
    // Get expected latency for QoS level
    function real get_expected_latency(bit[3:0] qos);
        case (qos)
            15, 14, 13, 12: return 100.0;   // 100ns for critical
            11, 10, 9, 8:   return 500.0;   // 500ns for high
            7, 6, 5, 4:     return 1000.0;  // 1us for medium
            default:        return 10000.0;  // 10us for low
        endcase
    endfunction
    
    // Analyze QoS fairness
    function void analyze_qos_fairness();
        real sum_squares = 0.0;
        real sum = 0.0;
        int n = 0;
        
        // Calculate Jain's fairness index
        for (int qos = 0; qos < 16; qos++) begin
            if (qos_patterns[qos].usage_count > 0) begin
                real throughput = qos_patterns[qos].avg_bandwidth;
                sum += throughput;
                sum_squares += throughput * throughput;
                n++;
            end
        end
        
        if (n > 0 && sum_squares > 0) begin
            qos_fairness_index = (sum * sum) / (n * sum_squares);
            
            if (qos_fairness_index < 0.8) begin
                recommendations.push_back(
                    $sformatf("Low QoS fairness index (%0.2f). Some QoS levels may be starved.",
                             qos_fairness_index)
                );
            end
        end
    endfunction
    
    // Detect QoS anomalies
    function void detect_qos_anomalies();
        // Check for QoS inversions
        for (int qos = 0; qos < 15; qos++) begin
            if (qos_patterns[qos].usage_count > 0 && 
                qos_patterns[qos+1].usage_count > 0) begin
                if (qos_patterns[qos].avg_latency < qos_patterns[qos+1].avg_latency) begin
                    qos_conflicts++;
                    recommendations.push_back(
                        $sformatf("QoS inversion: Level %0d has better latency than %0d",
                                 qos, qos+1)
                    );
                end
            end
        end
        
        // Check for starvation
        for (int qos = 0; qos < 16; qos++) begin
            if (qos_patterns[qos].usage_count > 0) begin
                if (qos_patterns[qos].max_latency > 10 * qos_patterns[qos].avg_latency) begin
                    qos_starvation_events++;
                    recommendations.push_back(
                        $sformatf("Possible starvation at QoS %0d: Max latency %0.0fx average",
                                 qos, qos_patterns[qos].max_latency / qos_patterns[qos].avg_latency)
                    );
                end
            end
        end
    endfunction
    
    // Analyze access pattern
    function void analyze_access_pattern(int master_id, axi4_transaction trans);
        // Simplified pattern detection
        if (trans.len == 0) begin
            master_behaviors[master_id].access_pattern = "Single beat";
        end else if (trans.burst == 2'b01) begin
            master_behaviors[master_id].access_pattern = "Sequential";
        end else if (trans.burst == 2'b10) begin
            master_behaviors[master_id].access_pattern = "Wrap";
        end
    endfunction
    
    // Analyze QoS stability
    function void analyze_qos_stability(int master_id);
        int total = 0;
        int max_count = 0;
        
        // Find dominant QoS
        for (int qos = 0; qos < 16; qos++) begin
            total += master_behaviors[master_id].qos_distribution[qos];
            if (master_behaviors[master_id].qos_distribution[qos] > max_count) begin
                max_count = master_behaviors[master_id].qos_distribution[qos];
            end
        end
        
        // Check if one QoS dominates
        if (total > 0) begin
            real dominance = real'(max_count) / real'(total);
            master_behaviors[master_id].qos_stable = (dominance > 0.8);
        end
    endfunction
    
    // Generate optimization recommendations
    function void generate_recommendations();
        // Clear previous recommendations
        recommendations.delete();
        
        // Already populated during analysis
        
        // Add system-wide recommendations
        if (system_qos_efficiency < 0.8) begin
            recommendations.push_back(
                "Overall QoS efficiency is low. Consider reviewing QoS allocation strategy."
            );
        end
        
        if (qos_conflicts > 10) begin
            recommendations.push_back(
                "Multiple QoS conflicts detected. Review arbitration algorithm."
            );
        end
        
        if (qos_starvation_events > 0) begin
            recommendations.push_back(
                "Starvation events detected. Enable starvation prevention mechanisms."
            );
        end
    endfunction
    
    // Get analysis report
    function string get_analysis_report();
        string report = "\\n=== QoS Analysis Report ===\\n";
        
        // System metrics
        report = {{report, $sformatf("\\nSystem Metrics:\\n")}};
        report = {{report, $sformatf("  QoS Efficiency: %0.1f%%\\n", 
                                    system_qos_efficiency * 100.0)}};
        report = {{report, $sformatf("  Fairness Index: %0.2f\\n", qos_fairness_index)}};
        report = {{report, $sformatf("  QoS Conflicts: %0d\\n", qos_conflicts)}};
        report = {{report, $sformatf("  Starvation Events: %0d\\n", qos_starvation_events)}};
        
        // QoS level analysis
        report = {{report, "\\nQoS Level Analysis:\\n"}};
        for (int qos = 0; qos < 16; qos++) begin
            if (qos_patterns[qos].usage_count > 0) begin
                report = {{report, $sformatf(
                    "  QoS %2d: Count=%6d, Avg BW=%0.1f MB/s, Avg Latency=%0.1f ns, Efficiency=%0.1f%%\\n",
                    qos, qos_patterns[qos].usage_count,
                    qos_patterns[qos].avg_bandwidth / 1e6,
                    qos_patterns[qos].avg_latency,
                    qos_patterns[qos].efficiency * 100.0
                )}};
            end
        end
        
        // Master behavior
        report = {{report, "\\nMaster Behavior Analysis:\\n"}};
        foreach (master_behaviors[id]) begin
            report = {{report, $sformatf("  Master %0d: Pattern=%s, QoS Stable=%s\\n",
                                        id, 
                                        master_behaviors[id].access_pattern,
                                        master_behaviors[id].qos_stable ? "Yes" : "No")}};
        end
        
        // Recommendations
        if (recommendations.size() > 0) begin
            report = {{report, "\\nOptimization Recommendations:\\n"}};
            foreach (recommendations[i]) begin
                report = {{report, $sformatf("  - %s\\n", recommendations[i])}};
            end
        end
        
        return report;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        perform_comprehensive_analysis();
        `uvm_info(get_type_name(), get_analysis_report(), UVM_LOW)
    endfunction

endclass

`endif // AXI4_QOS_ANALYZER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_qos_analyzer.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_qos_configurator(self, output_dir: str):
        """Generate QoS configuration interface"""
        content = f"""// AXI4 VIP QoS Configurator
// Generated: {datetime.datetime.now()}
// Provides runtime QoS configuration interface

`ifndef AXI4_QOS_CONFIGURATOR_SV
`define AXI4_QOS_CONFIGURATOR_SV

class axi4_qos_configurator extends uvm_object;
    `uvm_object_utils(axi4_qos_configurator)
    
    // QoS configuration database
    static axi4_qos_configurator m_inst;
    
    // Configuration parameters
    bit enable_qos = 1;
    bit[3:0] default_qos = 4'h4;
    
    // QoS mapping configuration
    bit[3:0] master_default_qos[int];
    bit[3:0] slave_min_qos[int];
    
    // QoS range constraints
    bit[3:0] master_min_qos[int];
    bit[3:0] master_max_qos[int];
    
    // Dynamic QoS settings
    bit enable_dynamic_qos = 1;
    bit enable_qos_promotion = 1;
    bit enable_qos_demotion = 0;
    
    // Arbitration settings
    string arbitration_mode = "WEIGHTED_ROUND_ROBIN";
    int qos_weights[16] = '{{16, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1}};
    
    // Constructor
    function new(string name = "axi4_qos_configurator");
        super.new(name);
    endfunction
    
    // Singleton pattern
    static function axi4_qos_configurator get();
        if (m_inst == null) begin
            m_inst = axi4_qos_configurator::type_id::create("axi4_qos_configurator");
        end
        return m_inst;
    endfunction
    
    // Configure master QoS settings
    function void configure_master_qos(int master_id, bit[3:0] default_qos,
                                      bit[3:0] min_qos = 0, 
                                      bit[3:0] max_qos = 15);
        master_default_qos[master_id] = default_qos;
        master_min_qos[master_id] = min_qos;
        master_max_qos[master_id] = max_qos;
        
        `uvm_info("QOS_CONFIG", 
                 $sformatf("Master %0d QoS configured: default=%0d, range=[%0d:%0d]",
                          master_id, default_qos, min_qos, max_qos), 
                 UVM_MEDIUM)
    endfunction
    
    // Configure slave QoS requirements
    function void configure_slave_qos(int slave_id, bit[3:0] min_required_qos);
        slave_min_qos[slave_id] = min_required_qos;
        
        `uvm_info("QOS_CONFIG", 
                 $sformatf("Slave %0d minimum QoS requirement: %0d",
                          slave_id, min_required_qos), 
                 UVM_MEDIUM)
    endfunction
    
    // Set QoS arbitration mode
    function void set_arbitration_mode(string mode);
        arbitration_mode = mode;
        `uvm_info("QOS_CONFIG", 
                 $sformatf("QoS arbitration mode set to: %s", mode), 
                 UVM_MEDIUM)
    endfunction
    
    // Configure QoS weights
    function void set_qos_weights(int weights[16]);
        qos_weights = weights;
        `uvm_info("QOS_CONFIG", "QoS weights updated", UVM_MEDIUM)
    endfunction
    
    // Get effective QoS for transaction
    function bit[3:0] get_effective_qos(int master_id, bit[3:0] requested_qos);
        bit[3:0] effective_qos = requested_qos;
        
        // Apply master constraints
        if (master_min_qos.exists(master_id)) begin
            if (effective_qos < master_min_qos[master_id])
                effective_qos = master_min_qos[master_id];
        end
        
        if (master_max_qos.exists(master_id)) begin
            if (effective_qos > master_max_qos[master_id])
                effective_qos = master_max_qos[master_id];
        end
        
        return effective_qos;
    endfunction
    
    // Load configuration from file
    function void load_config(string filename);
        // Implementation would parse configuration file
        `uvm_info("QOS_CONFIG", 
                 $sformatf("Loading QoS configuration from %s", filename), 
                 UVM_MEDIUM)
    endfunction
    
    // Save configuration to file
    function void save_config(string filename);
        int fd = $fopen(filename, "w");
        
        if (fd) begin
            $fwrite(fd, "# AXI4 QoS Configuration\\n");
            $fwrite(fd, "# Generated: %s\\n\\n", $sformatf("%0t", $time));
            
            $fwrite(fd, "[Global]\\n");
            $fwrite(fd, "enable_qos = %0d\\n", enable_qos);
            $fwrite(fd, "default_qos = %0d\\n", default_qos);
            $fwrite(fd, "enable_dynamic_qos = %0d\\n", enable_dynamic_qos);
            $fwrite(fd, "arbitration_mode = %s\\n\\n", arbitration_mode);
            
            $fwrite(fd, "[Masters]\\n");
            foreach (master_default_qos[id]) begin
                $fwrite(fd, "master%0d.default_qos = %0d\\n", id, master_default_qos[id]);
                $fwrite(fd, "master%0d.min_qos = %0d\\n", id, master_min_qos[id]);
                $fwrite(fd, "master%0d.max_qos = %0d\\n", id, master_max_qos[id]);
            end
            
            $fwrite(fd, "\\n[Slaves]\\n");
            foreach (slave_min_qos[id]) begin
                $fwrite(fd, "slave%0d.min_qos = %0d\\n", id, slave_min_qos[id]);
            end
            
            $fwrite(fd, "\\n[Weights]\\n");
            for (int i = 0; i < 16; i++) begin
                $fwrite(fd, "qos%0d.weight = %0d\\n", i, qos_weights[i]);
            end
            
            $fclose(fd);
            `uvm_info("QOS_CONFIG", 
                     $sformatf("QoS configuration saved to %s", filename), 
                     UVM_LOW)
        end
    endfunction

endclass

`endif // AXI4_QOS_CONFIGURATOR_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_qos_configurator.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_qos_package(self, output_dir: str):
        """Generate QoS package file"""
        content = f"""// AXI4 VIP QoS Package
// Generated: {datetime.datetime.now()}
// Contains all QoS-related components

`ifndef AXI4_QOS_PKG_SV
`define AXI4_QOS_PKG_SV

package axi4_qos_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Import base VIP package
    import axi4_vip_pkg::*;
    
    // QoS type definitions
    typedef enum {{
        QOS_LEVEL_LOW      = 0,
        QOS_LEVEL_MEDIUM   = 4,
        QOS_LEVEL_HIGH     = 8,
        QOS_LEVEL_CRITICAL = 12
    }} qos_level_e;
    
    // Include QoS components
    `include "axi4_qos_arbiter.sv"
    `include "axi4_qos_monitor.sv"
    `include "axi4_qos_manager.sv"
    `include "axi4_qos_scheduler.sv"
    `include "axi4_qos_enforcer.sv"
    `include "axi4_qos_analyzer.sv"
    `include "axi4_qos_configurator.sv"
    
endpackage

`endif // AXI4_QOS_PKG_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_qos_pkg.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def generate_qos_integration_example(self, output_dir: str):
        """Generate example of QoS integration"""
        content = f"""// AXI4 VIP QoS Integration Example
// Generated: {datetime.datetime.now()}
// Shows how to integrate QoS components

class axi4_qos_env extends uvm_env;
    `uvm_component_utils(axi4_qos_env)
    
    // QoS components
    axi4_qos_arbiter qos_arbiter;
    axi4_qos_monitor qos_monitor;
    axi4_qos_manager qos_manager;
    axi4_qos_scheduler qos_scheduler;
    axi4_qos_enforcer qos_enforcer;
    axi4_qos_analyzer qos_analyzer;
    
    // Constructor
    function new(string name = "axi4_qos_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create QoS components
        qos_arbiter = axi4_qos_arbiter::type_id::create("qos_arbiter", this);
        qos_monitor = axi4_qos_monitor::type_id::create("qos_monitor", this);
        qos_manager = axi4_qos_manager::type_id::create("qos_manager", this);
        qos_scheduler = axi4_qos_scheduler::type_id::create("qos_scheduler", this);
        qos_enforcer = axi4_qos_enforcer::type_id::create("qos_enforcer", this);
        qos_analyzer = axi4_qos_analyzer::type_id::create("qos_analyzer", this);
        
        // Configure QoS
        configure_qos();
    endfunction
    
    // Configure QoS settings
    function void configure_qos();
        axi4_qos_configurator qos_config = axi4_qos_configurator::get();
        
        // Configure masters
        qos_config.configure_master_qos(0, 4'h4, 4'h0, 4'hF);  // Master 0: Full range
        qos_config.configure_master_qos(1, 4'h8, 4'h4, 4'hC);  // Master 1: Medium-High
        qos_config.configure_master_qos(2, 4'hC, 4'h8, 4'hF);  // Master 2: High-Critical
        qos_config.configure_master_qos(3, 4'h2, 4'h0, 4'h7);  // Master 3: Low-Medium
        
        // Configure slaves
        qos_config.configure_slave_qos(0, 4'h0);  // Slave 0: No minimum
        qos_config.configure_slave_qos(1, 4'h4);  // Slave 1: Medium minimum
        qos_config.configure_slave_qos(2, 4'h8);  // Slave 2: High minimum
        qos_config.configure_slave_qos(3, 4'h0);  // Slave 3: No minimum
        
        // Set arbitration mode
        qos_config.set_arbitration_mode("WEIGHTED_ROUND_ROBIN");
        
        // Configure arbiter
        qos_arbiter.arb_mode = axi4_qos_arbiter::WEIGHTED_ROUND_ROBIN;
        qos_arbiter.max_wait_cycles = 1000;
        qos_arbiter.starvation_threshold = 500;
        
        // Configure scheduler
        qos_scheduler.algorithm = axi4_qos_scheduler::WEIGHTED_FAIR_QUEUING;
        
        // Configure enforcer
        qos_enforcer.strict_enforcement = 1;
        qos_enforcer.enable_preemption = 1;
        
        // Save configuration
        qos_config.save_config("qos_config.ini");
    endfunction
    
    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect QoS monitor to other components
        // qos_monitor.qos_ap.connect(qos_analyzer.analysis_export);
        // Additional connections...
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        // QoS components run automatically
    endtask
    
    // Report phase
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        // Generate comprehensive QoS report
        `uvm_info(get_type_name(), "=== QoS System Report ===", UVM_LOW)
        `uvm_info(get_type_name(), qos_arbiter.get_qos_stats(), UVM_LOW)
        `uvm_info(get_type_name(), qos_monitor.get_qos_report(), UVM_LOW)
        `uvm_info(get_type_name(), qos_scheduler.get_scheduling_stats(), UVM_LOW)
        `uvm_info(get_type_name(), qos_enforcer.get_sla_report(), UVM_LOW)
        `uvm_info(get_type_name(), qos_analyzer.get_analysis_report(), UVM_LOW)
    endfunction

endclass
"""
        
        filepath = os.path.join(output_dir, "axi4_qos_integration_example.sv")
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
        'protocol': 'AXI4'
    }
    
    generator = VIPQoSGenerator(config)
    generator.generate_all_qos_components("./vip_output")
    generator.generate_qos_integration_example("./vip_output")
    print("QoS components generated successfully!")
"""
        
        filepath = os.path.join(output_dir, "axi4_qos_integration_example.sv")
        with open(filepath, 'w') as f:
            f.write(content)