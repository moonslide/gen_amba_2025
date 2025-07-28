#!/usr/bin/env python3
"""
VIP Bus Matrix Reference Model Generator
Generates transaction-level reference model 100% consistent with GUI settings
Based on tim_axi4_vip reference model architecture
"""

import os
import json
from datetime import datetime
from typing import Dict, List, Optional, Tuple, Any
import math

class VIPBusMatrixReferenceModel:
    """Generate bus matrix reference model with exact configuration matching"""
    
    def __init__(self, config):
        self.config = config
        self.timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        # Extract configuration
        self.num_masters = config.get('num_masters', 4)
        self.num_slaves = config.get('num_slaves', 4)
        self.data_width = config.get('data_width', 128)
        self.addr_width = config.get('addr_width', 64)
        self.id_width = config.get('id_width', 8)
        self.user_width = config.get('user_width', 32)
        
        # Memory map from configuration
        self.memory_map = config.get('memory_map', self._generate_default_memory_map())
        
        # Features
        self.support_qos = config.get('support_qos', True)
        self.support_region = config.get('support_region', True)
        self.support_exclusive = config.get('support_exclusive', True)
        self.support_user = config.get('support_user', True)
        
        # Arbitration settings
        self.arbitration_scheme = config.get('arbitration_scheme', 'round_robin')
        self.qos_enable = config.get('qos_enable', True)
        
        # ID mapping configuration
        self.id_map_bits = math.ceil(math.log2(self.num_masters))
        
    def _generate_default_memory_map(self) -> List[Dict]:
        """Generate default memory map if not provided"""
        memory_map = []
        base_addr = 0
        size_per_slave = (1 << self.addr_width) // self.num_slaves
        
        for i in range(self.num_slaves):
            memory_map.append({
                'slave_id': i,
                'base_addr': base_addr,
                'size': size_per_slave,
                'end_addr': base_addr + size_per_slave - 1,
                'name': f'slave_{i}'
            })
            base_addr += size_per_slave
            
        return memory_map
        
    def generate_reference_model(self, output_dir: str) -> bool:
        """Generate complete bus matrix reference model"""
        
        # Create reference model directory
        ref_model_dir = os.path.join(output_dir, "reference_model")
        os.makedirs(ref_model_dir, exist_ok=True)
        
        # Save configuration for verification
        self._save_configuration(ref_model_dir)
        
        # Generate components
        self._generate_bus_matrix_model(ref_model_dir)
        self._generate_routing_model(ref_model_dir)
        self._generate_arbitration_model(ref_model_dir)
        self._generate_id_mapping_model(ref_model_dir)
        self._generate_address_decoder_model(ref_model_dir)
        self._generate_exclusive_monitor_model(ref_model_dir)
        self._generate_transaction_predictor(ref_model_dir)
        self._generate_scoreboard_predictor(ref_model_dir)
        
        return True
        
    def _save_configuration(self, output_dir: str):
        """Save configuration for verification consistency"""
        
        config_file = os.path.join(output_dir, "reference_model_config.json")
        
        config_data = {
            'timestamp': self.timestamp,
            'num_masters': self.num_masters,
            'num_slaves': self.num_slaves,
            'data_width': self.data_width,
            'addr_width': self.addr_width,
            'id_width': self.id_width,
            'user_width': self.user_width,
            'memory_map': self.memory_map,
            'support_qos': self.support_qos,
            'support_region': self.support_region,
            'support_exclusive': self.support_exclusive,
            'support_user': self.support_user,
            'arbitration_scheme': self.arbitration_scheme,
            'qos_enable': self.qos_enable,
            'id_map_bits': self.id_map_bits
        }
        
        with open(config_file, 'w') as f:
            json.dump(config_data, f, indent=2)
            
    def _generate_bus_matrix_model(self, output_dir: str):
        """Generate main bus matrix reference model"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Bus Matrix Reference Model
// Generated: {self.timestamp}
// Description: Transaction-level reference model for bus matrix
// Configuration: {self.num_masters}x{self.num_slaves} matrix
//------------------------------------------------------------------------------

class axi4_bus_matrix_model extends uvm_component;
    
    `uvm_component_utils(axi4_bus_matrix_model)
    
    // Configuration - MUST match RTL exactly
    localparam NUM_MASTERS = {self.num_masters};
    localparam NUM_SLAVES = {self.num_slaves};
    localparam DATA_WIDTH = {self.data_width};
    localparam ADDR_WIDTH = {self.addr_width};
    localparam ID_WIDTH = {self.id_width};
    localparam USER_WIDTH = {self.user_width};
    localparam ID_MAP_BITS = {self.id_map_bits};
    
    // Analysis ports for each master
    uvm_analysis_imp_decl(_master)
    uvm_analysis_imp_master #(axi4_transaction, axi4_bus_matrix_model) master_ports[NUM_MASTERS];
    
    // Analysis ports for predicted slave transactions
    uvm_analysis_port #(axi4_transaction) slave_ports[NUM_SLAVES];
    
    // Sub-models
    axi4_routing_model routing_model;
    axi4_arbitration_model arbitration_model;
    axi4_id_mapping_model id_mapping_model;
    axi4_address_decoder_model address_decoder;
    axi4_exclusive_monitor_model exclusive_monitor;
    
    // Transaction queues for each channel
    axi4_transaction write_addr_queue[NUM_MASTERS][$];
    axi4_transaction write_data_queue[NUM_MASTERS][$];
    axi4_transaction write_resp_queue[NUM_SLAVES][$];
    axi4_transaction read_addr_queue[NUM_MASTERS][$];
    axi4_transaction read_data_queue[NUM_SLAVES][$];
    
    // Outstanding transaction tracking
    int outstanding_writes[NUM_MASTERS][bit[ID_WIDTH-1:0]];
    int outstanding_reads[NUM_MASTERS][bit[ID_WIDTH-1:0]];
    
    // Constructor
    function new(string name = "axi4_bus_matrix_model", uvm_component parent = null);
        super.new(name, parent);
        
        // Create analysis ports
        foreach (master_ports[i]) begin
            master_ports[i] = new($sformatf("master_port_%0d", i), this);
        end
        
        foreach (slave_ports[i]) begin
            slave_ports[i] = new($sformatf("slave_port_%0d", i), this);
        end
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create sub-models with same configuration
        routing_model = axi4_routing_model::type_id::create("routing_model", this);
        routing_model.configure(NUM_MASTERS, NUM_SLAVES);
        
        arbitration_model = axi4_arbitration_model::type_id::create("arbitration_model", this);
        arbitration_model.configure(NUM_MASTERS, NUM_SLAVES, "{self.arbitration_scheme}");
        
        id_mapping_model = axi4_id_mapping_model::type_id::create("id_mapping_model", this);
        id_mapping_model.configure(NUM_MASTERS, ID_WIDTH, ID_MAP_BITS);
        
        address_decoder = axi4_address_decoder_model::type_id::create("address_decoder", this);
        address_decoder.configure(NUM_SLAVES, ADDR_WIDTH);
        
        exclusive_monitor = axi4_exclusive_monitor_model::type_id::create("exclusive_monitor", this);
        exclusive_monitor.configure(NUM_MASTERS, NUM_SLAVES);
        
        // Configure memory map
        configure_memory_map();
    endfunction
    
    // Configure memory map - MUST match RTL configuration
    function void configure_memory_map();
'''
        
        # Add memory map configuration
        for slave in self.memory_map:
            content += f'''        address_decoder.add_slave_region({slave['slave_id']}, 
                                         {slave['base_addr']:#x}, 
                                         {slave['end_addr']:#x}, 
                                         "{slave['name']}");
'''
            
        content += '''    endfunction
    
    // Write function for master transactions
    function void write_master(int master_id, axi4_transaction trans);
        process_master_transaction(master_id, trans);
    endfunction
    
    // Process master transaction
    function void process_master_transaction(int master_id, axi4_transaction trans);
        axi4_transaction predicted_trans;
        int slave_id;
        
        // Clone transaction for prediction
        predicted_trans = axi4_transaction::type_id::create("predicted_trans");
        predicted_trans.copy(trans);
        
        // Decode target slave
        slave_id = address_decoder.decode_address(trans.addr);
        
        if (slave_id == -1) begin
            // No slave - predict DECERR
            predict_decode_error(master_id, predicted_trans);
            return;
        end
        
        // Apply ID mapping
        predicted_trans = id_mapping_model.map_transaction(master_id, predicted_trans);
        
        // Track outstanding
        if (trans.trans_type == AXI4_WRITE) begin
            outstanding_writes[master_id][trans.id]++;
            write_addr_queue[master_id].push_back(predicted_trans);
        end else begin
            outstanding_reads[master_id][trans.id]++;
            read_addr_queue[master_id].push_back(predicted_trans);
        end
        
        // Check exclusive access
        if (trans.lock == 1'b1) begin
            exclusive_monitor.process_exclusive_transaction(master_id, slave_id, predicted_trans);
        end
        
        // Apply arbitration delay
        predicted_trans.start_time = $time;
        predicted_trans.arbitration_delay = arbitration_model.get_arbitration_delay(
            master_id, slave_id, trans.trans_type
        );
        
        // Route to slave
        route_to_slave(master_id, slave_id, predicted_trans);
    endfunction
    
    // Route transaction to slave
    function void route_to_slave(int master_id, int slave_id, axi4_transaction trans);
        // Add routing information
        trans.routed_to_slave = slave_id;
        trans.routed_from_master = master_id;
        
        // Send to slave analysis port
        slave_ports[slave_id].write(trans);
        
        // Log routing
        `uvm_info(get_name(), $sformatf("Routed %s from Master[%0d] to Slave[%0d], Addr=%0h",
                                       trans.trans_type.name(), master_id, slave_id, trans.addr), UVM_HIGH)
    endfunction
    
    // Predict decode error response
    function void predict_decode_error(int master_id, axi4_transaction trans);
        axi4_transaction error_resp;
        
        error_resp = axi4_transaction::type_id::create("error_resp");
        error_resp.copy(trans);
        error_resp.resp = AXI4_DECERR;
        
        // Send to default slave (if configured)
        `uvm_info(get_name(), $sformatf("Predicted DECERR for Master[%0d], Addr=%0h",
                                       master_id, trans.addr), UVM_MEDIUM)
    endfunction
    
    // Get predicted response path
    function int get_response_master(int slave_id, bit [ID_WIDTH-1:0] id);
        return id_mapping_model.get_master_from_id(id);
    endfunction
    
    // Check configuration consistency
    function bit verify_configuration(axi4_bus_config rtl_config);
        bit config_match = 1;
        
        if (rtl_config.num_masters != NUM_MASTERS) begin
            `uvm_error(get_name(), $sformatf("Master count mismatch: Model=%0d, RTL=%0d",
                                           NUM_MASTERS, rtl_config.num_masters))
            config_match = 0;
        end
        
        if (rtl_config.num_slaves != NUM_SLAVES) begin
            `uvm_error(get_name(), $sformatf("Slave count mismatch: Model=%0d, RTL=%0d",
                                           NUM_SLAVES, rtl_config.num_slaves))
            config_match = 0;
        end
        
        // Check all parameters
        if (rtl_config.data_width != DATA_WIDTH) config_match = 0;
        if (rtl_config.addr_width != ADDR_WIDTH) config_match = 0;
        if (rtl_config.id_width != ID_WIDTH) config_match = 0;
        
        return config_match;
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_bus_matrix_model.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_routing_model(self, output_dir: str):
        """Generate routing prediction model"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Routing Model
// Generated: {self.timestamp}
// Description: Models routing decisions for bus matrix
//------------------------------------------------------------------------------

class axi4_routing_model extends uvm_object;
    
    `uvm_object_utils(axi4_routing_model)
    
    // Configuration
    int num_masters;
    int num_slaves;
    
    // Routing tables
    bit [15:0] master_to_slave_connectivity[int][int]; // [master][slave]
    bit [15:0] slave_to_master_connectivity[int][int]; // [slave][master]
    
    // Active routes
    int active_write_routes[int][int]; // [master][slave]
    int active_read_routes[int][int];  // [master][slave]
    
    // Constructor
    function new(string name = "axi4_routing_model");
        super.new(name);
    endfunction
    
    // Configure
    function void configure(int num_m, int num_s);
        num_masters = num_m;
        num_slaves = num_s;
        
        // Initialize full connectivity by default
        for (int m = 0; m < num_masters; m++) begin
            for (int s = 0; s < num_slaves; s++) begin
                master_to_slave_connectivity[m][s] = 1;
                slave_to_master_connectivity[s][m] = 1;
            end
        end
    endfunction
    
    // Check if route is available
    function bit is_route_available(int master_id, int slave_id, axi4_trans_type_e trans_type);
        // Check connectivity
        if (!master_to_slave_connectivity[master_id][slave_id]) begin
            return 0;
        end
        
        // Check if route is busy (optional blocking)
        if (trans_type == AXI4_WRITE) begin
            return (active_write_routes[master_id][slave_id] < {self.config.get('max_outstanding_per_route', 16)});
        end else begin
            return (active_read_routes[master_id][slave_id] < {self.config.get('max_outstanding_per_route', 16)});
        end
    endfunction
    
    // Reserve route
    function void reserve_route(int master_id, int slave_id, axi4_trans_type_e trans_type);
        if (trans_type == AXI4_WRITE) begin
            active_write_routes[master_id][slave_id]++;
        end else begin
            active_read_routes[master_id][slave_id]++;
        end
    endfunction
    
    // Release route
    function void release_route(int master_id, int slave_id, axi4_trans_type_e trans_type);
        if (trans_type == AXI4_WRITE) begin
            if (active_write_routes[master_id][slave_id] > 0)
                active_write_routes[master_id][slave_id]--;
        end else begin
            if (active_read_routes[master_id][slave_id] > 0)
                active_read_routes[master_id][slave_id]--;
        end
    endfunction
    
    // Get available slaves for master
    function void get_available_slaves(int master_id, output int slave_list[$]);
        slave_list.delete();
        
        for (int s = 0; s < num_slaves; s++) begin
            if (master_to_slave_connectivity[master_id][s]) begin
                slave_list.push_back(s);
            end
        end
    endfunction
    
    // Get available masters for slave
    function void get_available_masters(int slave_id, output int master_list[$]);
        master_list.delete();
        
        for (int m = 0; m < num_masters; m++) begin
            if (slave_to_master_connectivity[slave_id][m]) begin
                master_list.push_back(m);
            end
        end
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_routing_model.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_arbitration_model(self, output_dir: str):
        """Generate arbitration model"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Arbitration Model
// Generated: {self.timestamp}
// Description: Models arbitration decisions and delays
//------------------------------------------------------------------------------

class axi4_arbitration_model extends uvm_object;
    
    `uvm_object_utils(axi4_arbitration_model)
    
    // Configuration
    int num_masters;
    int num_slaves;
    string arbitration_scheme;
    bit qos_enable = {str(self.qos_enable).lower()};
    
    // Arbitration state
    int current_grant[int]; // [slave_id] -> granted master
    int last_granted[int];  // [slave_id] -> last granted master for round-robin
    real last_grant_time[int][int]; // [slave][master]
    
    // QoS tracking
    int master_qos[int]; // [master_id] -> QoS value
    int pending_requests[int][int]; // [slave][master]
    
    // Statistics
    int grant_count[int][int]; // [slave][master]
    real total_wait_time[int][int]; // [slave][master]
    
    // Constructor
    function new(string name = "axi4_arbitration_model");
        super.new(name);
    endfunction
    
    // Configure
    function void configure(int num_m, int num_s, string arb_scheme);
        num_masters = num_m;
        num_slaves = num_s;
        arbitration_scheme = arb_scheme;
        
        // Initialize
        for (int s = 0; s < num_slaves; s++) begin
            current_grant[s] = -1;
            last_granted[s] = 0;
        end
    endfunction
    
    // Get arbitration delay
    function int get_arbitration_delay(int master_id, int slave_id, axi4_trans_type_e trans_type);
        int delay = 0;
        int granted_master;
        
        // Check current grant
        if (current_grant[slave_id] == master_id) begin
            // Already granted
            return 0;
        end
        
        // Model arbitration based on scheme
        case (arbitration_scheme)
            "round_robin": begin
                delay = calculate_round_robin_delay(master_id, slave_id);
            end
            
            "fixed_priority": begin
                delay = calculate_fixed_priority_delay(master_id, slave_id);
            end
            
            "qos_based": begin
                delay = calculate_qos_based_delay(master_id, slave_id);
            end
            
            "weighted_round_robin": begin
                delay = calculate_weighted_delay(master_id, slave_id);
            end
            
            default: begin
                delay = 1; // Default single cycle
            end
        endcase
        
        // Update grant
        current_grant[slave_id] = master_id;
        last_grant_time[slave_id][master_id] = $time;
        grant_count[slave_id][master_id]++;
        
        return delay;
    endfunction
    
    // Round-robin arbitration
    function int calculate_round_robin_delay(int master_id, int slave_id);
        int next_master = last_granted[slave_id];
        int cycles = 0;
        
        // Find next master in round-robin order
        do begin
            next_master = (next_master + 1) % num_masters;
            cycles++;
            
            if (pending_requests[slave_id][next_master] > 0) begin
                if (next_master == master_id) begin
                    last_granted[slave_id] = master_id;
                    return cycles;
                end
            end
        end while (cycles < num_masters);
        
        // Default if no pending requests
        return 1;
    endfunction
    
    // Fixed priority arbitration
    function int calculate_fixed_priority_delay(int master_id, int slave_id);
        int higher_priority_masters = 0;
        
        // Count higher priority masters with pending requests
        for (int m = 0; m < master_id; m++) begin
            if (pending_requests[slave_id][m] > 0) begin
                higher_priority_masters++;
            end
        end
        
        // Delay based on higher priority masters
        return higher_priority_masters + 1;
    endfunction
    
    // QoS-based arbitration
    function int calculate_qos_based_delay(int master_id, int slave_id);
        int my_qos = master_qos[master_id];
        int higher_qos_masters = 0;
        
        // Count masters with higher QoS
        for (int m = 0; m < num_masters; m++) begin
            if (m != master_id && pending_requests[slave_id][m] > 0) begin
                if (master_qos[m] > my_qos) begin
                    higher_qos_masters++;
                end
            end
        end
        
        // QoS-based delay
        return higher_qos_masters * 2 + 1; // Higher QoS gets priority
    endfunction
    
    // Weighted round-robin
    function int calculate_weighted_delay(int master_id, int slave_id);
        // Implementation based on weights
        int weight = get_master_weight(master_id);
        int total_weight = 0;
        
        for (int m = 0; m < num_masters; m++) begin
            if (pending_requests[slave_id][m] > 0) begin
                total_weight += get_master_weight(m);
            end
        end
        
        return (total_weight / weight) + 1;
    endfunction
    
    // Get master weight for weighted arbitration
    function int get_master_weight(int master_id);
        // Default weights - can be configured
        case (master_id)
            0: return 4; // Highest weight
            1: return 3;
            2: return 2;
            default: return 1;
        endcase
    endfunction
    
    // Update QoS value
    function void set_master_qos(int master_id, int qos_value);
        master_qos[master_id] = qos_value;
    endfunction
    
    // Add pending request
    function void add_pending_request(int master_id, int slave_id);
        pending_requests[slave_id][master_id]++;
    endfunction
    
    // Remove pending request
    function void remove_pending_request(int master_id, int slave_id);
        if (pending_requests[slave_id][master_id] > 0) begin
            pending_requests[slave_id][master_id]--;
        end
    endfunction
    
    // Get arbitration statistics
    function void get_arbitration_stats(int slave_id);
        `uvm_info("ARB_STATS", $sformatf("Slave[%0d] Arbitration Statistics:", slave_id), UVM_LOW)
        
        for (int m = 0; m < num_masters; m++) begin
            if (grant_count[slave_id][m] > 0) begin
                real avg_wait = total_wait_time[slave_id][m] / grant_count[slave_id][m];
                `uvm_info("ARB_STATS", $sformatf("  Master[%0d]: Grants=%0d, Avg Wait=%.2f",
                                                m, grant_count[slave_id][m], avg_wait), UVM_LOW)
            end
        end
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_arbitration_model.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_id_mapping_model(self, output_dir: str):
        """Generate ID mapping model"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// ID Mapping Model
// Generated: {self.timestamp}
// Description: Models ID mapping/remapping in interconnect
//------------------------------------------------------------------------------

class axi4_id_mapping_model extends uvm_object;
    
    `uvm_object_utils(axi4_id_mapping_model)
    
    // Configuration - MUST match RTL
    int num_masters;
    int id_width;
    int id_map_bits;
    
    // ID mapping table
    bit [15:0] id_base[int]; // [master] -> base ID
    bit [15:0] id_mask[int]; // [master] -> ID mask
    
    // Reverse mapping for responses
    int id_to_master_map[bit[15:0]]; // [mapped_id] -> master
    
    // Constructor
    function new(string name = "axi4_id_mapping_model");
        super.new(name);
    endfunction
    
    // Configure - MUST match RTL configuration exactly
    function void configure(int num_m, int id_w, int map_bits);
        num_masters = num_m;
        id_width = id_w;
        id_map_bits = map_bits;
        
        // Initialize ID mapping - MUST match RTL
        for (int m = 0; m < num_masters; m++) begin
            id_base[m] = m << (id_width - id_map_bits);
            id_mask[m] = (1 << (id_width - id_map_bits)) - 1;
            
            // Build reverse map
            for (int i = 0; i < (1 << (id_width - id_map_bits)); i++) begin
                bit [15:0] mapped_id = id_base[m] | i;
                id_to_master_map[mapped_id] = m;
            end
        end
    endfunction
    
    // Map transaction ID from master to interconnect
    function axi4_transaction map_transaction(int master_id, axi4_transaction trans);
        axi4_transaction mapped_trans;
        
        // Clone transaction
        mapped_trans = axi4_transaction::type_id::create("mapped_trans");
        mapped_trans.copy(trans);
        
        // Apply ID mapping - MUST match RTL logic
        mapped_trans.original_id = trans.id;
        mapped_trans.id = (trans.id & id_mask[master_id]) | id_base[master_id];
        mapped_trans.source_master = master_id;
        
        `uvm_info(get_name(), $sformatf("ID Mapping: Master[%0d] ID %0h -> %0h",
                                       master_id, trans.id, mapped_trans.id), UVM_HIGH)
        
        return mapped_trans;
    endfunction
    
    // Get master from mapped ID
    function int get_master_from_id(bit [15:0] mapped_id);
        if (id_to_master_map.exists(mapped_id)) begin
            return id_to_master_map[mapped_id];
        end
        
        // Extract master from upper bits
        return mapped_id >> (id_width - id_map_bits);
    endfunction
    
    // Unmap response transaction
    function axi4_transaction unmap_response(axi4_transaction resp_trans);
        axi4_transaction unmapped_trans;
        int master_id;
        
        // Clone transaction
        unmapped_trans = axi4_transaction::type_id::create("unmapped_trans");
        unmapped_trans.copy(resp_trans);
        
        // Get original master
        master_id = get_master_from_id(resp_trans.id);
        
        // Restore original ID
        unmapped_trans.id = resp_trans.id & id_mask[master_id];
        unmapped_trans.target_master = master_id;
        
        return unmapped_trans;
    endfunction
    
    // Check for ID conflicts
    function bit check_id_conflict(int master_id, bit [15:0] id);
        bit [15:0] mapped_id = (id & id_mask[master_id]) | id_base[master_id];
        
        // Check if this mapped ID could conflict with another master
        for (int m = 0; m < num_masters; m++) begin
            if (m != master_id) begin
                if ((mapped_id & ~id_mask[m]) == id_base[m]) begin
                    `uvm_warning(get_name(), $sformatf("Potential ID conflict: Master[%0d] ID %0h maps to %0h",
                                                     master_id, id, mapped_id))
                    return 1;
                end
            end
        end
        
        return 0;
    endfunction
    
    // Get available ID range for master
    function void get_id_range(int master_id, output bit [15:0] min_id, output bit [15:0] max_id);
        min_id = 0;
        max_id = id_mask[master_id];
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_id_mapping_model.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_address_decoder_model(self, output_dir: str):
        """Generate address decoder model"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Address Decoder Model
// Generated: {self.timestamp}
// Description: Models address decoding logic - MUST match RTL
//------------------------------------------------------------------------------

class axi4_address_decoder_model extends uvm_object;
    
    `uvm_object_utils(axi4_address_decoder_model)
    
    // Configuration
    int num_slaves;
    int addr_width;
    
    // Memory map - MUST match RTL exactly
    typedef struct {
        bit [63:0] base_addr;
        bit [63:0] end_addr;
        bit [63:0] size;
        string name;
        bit enabled;
    } slave_region_t;
    
    slave_region_t slave_regions[int];
    
    // Constructor
    function new(string name = "axi4_address_decoder_model");
        super.new(name);
    endfunction
    
    // Configure
    function void configure(int num_s, int addr_w);
        num_slaves = num_s;
        addr_width = addr_w;
    endfunction
    
    // Add slave region - MUST match RTL memory map
    function void add_slave_region(int slave_id, bit [63:0] base, bit [63:0] end_addr, string name);
        slave_region_t region;
        
        region.base_addr = base;
        region.end_addr = end_addr;
        region.size = end_addr - base + 1;
        region.name = name;
        region.enabled = 1;
        
        slave_regions[slave_id] = region;
        
        `uvm_info(get_name(), $sformatf("Added Slave[%0d] '%s': Base=%0h, End=%0h, Size=%0h",
                                       slave_id, name, base, end_addr, region.size), UVM_MEDIUM)
    endfunction
    
    // Decode address to slave - MUST match RTL decoder logic
    function int decode_address(bit [63:0] addr);
        // Check each slave region
        foreach (slave_regions[slave_id]) begin
            if (slave_regions[slave_id].enabled) begin
                if (addr >= slave_regions[slave_id].base_addr && 
                    addr <= slave_regions[slave_id].end_addr) begin
                    `uvm_info(get_name(), $sformatf("Address %0h decoded to Slave[%0d] '%s'",
                                                   addr, slave_id, slave_regions[slave_id].name), UVM_HIGH)
                    return slave_id;
                end
            end
        end
        
        // No matching slave - decode error
        `uvm_info(get_name(), $sformatf("Address %0h decoded to DECERR (no slave)", addr), UVM_MEDIUM)
        return -1;
    endfunction
    
    // Check if address is valid
    function bit is_valid_address(bit [63:0] addr);
        return (decode_address(addr) != -1);
    endfunction
    
    // Get slave info
    function bit get_slave_info(int slave_id, output slave_region_t region);
        if (slave_regions.exists(slave_id)) begin
            region = slave_regions[slave_id];
            return 1;
        end
        return 0;
    endfunction
    
    // Check for overlapping regions
    function bit check_overlapping_regions();
        bit overlap_found = 0;
        
        foreach (slave_regions[id1]) begin
            foreach (slave_regions[id2]) begin
                if (id1 < id2) begin // Check each pair once
                    if (regions_overlap(slave_regions[id1], slave_regions[id2])) begin
                        `uvm_error(get_name(), $sformatf("Overlapping regions: Slave[%0d] and Slave[%0d]",
                                                       id1, id2))
                        overlap_found = 1;
                    end
                end
            end
        end
        
        return overlap_found;
    endfunction
    
    // Check if two regions overlap
    function bit regions_overlap(slave_region_t r1, slave_region_t r2);
        return !((r1.end_addr < r2.base_addr) || (r2.end_addr < r1.base_addr));
    endfunction
    
    // Get total address space coverage
    function bit [63:0] get_total_coverage();
        bit [63:0] total = 0;
        
        foreach (slave_regions[id]) begin
            if (slave_regions[id].enabled) begin
                total += slave_regions[id].size;
            end
        end
        
        return total;
    endfunction
    
    // Print memory map
    function void print_memory_map();
        `uvm_info(get_name(), "=== Memory Map Configuration ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Address Width: %0d bits", addr_width), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Number of Slaves: %0d", num_slaves), UVM_LOW)
        
        foreach (slave_regions[id]) begin
            `uvm_info(get_name(), $sformatf("Slave[%0d] '%s':", id, slave_regions[id].name), UVM_LOW)
            `uvm_info(get_name(), $sformatf("  Base: %0h", slave_regions[id].base_addr), UVM_LOW)
            `uvm_info(get_name(), $sformatf("  End:  %0h", slave_regions[id].end_addr), UVM_LOW)
            `uvm_info(get_name(), $sformatf("  Size: %0h (%0d KB)", slave_regions[id].size, 
                                           slave_regions[id].size / 1024), UVM_LOW)
        end
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_address_decoder_model.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_exclusive_monitor_model(self, output_dir: str):
        """Generate exclusive monitor reference model"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Exclusive Monitor Model
// Generated: {self.timestamp}
// Description: Models exclusive access monitoring - MUST match RTL
//------------------------------------------------------------------------------

class axi4_exclusive_monitor_model extends uvm_object;
    
    `uvm_object_utils(axi4_exclusive_monitor_model)
    
    // Configuration
    int num_masters;
    int num_slaves;
    
    // Exclusive reservation table - MUST match RTL implementation
    typedef struct {
        bit valid;
        bit [63:0] address;
        bit [2:0] size;
        bit [7:0] id;
        int master_id;
        int slave_id;
        time reservation_time;
    } exclusive_entry_t;
    
    // Reservation table per slave
    exclusive_entry_t exclusive_table[int][bit[63:0]]; // [slave][address]
    
    // Configuration
    real exclusive_timeout_ns = 1000.0; // Must match RTL
    bit enable_timeout = 1;
    
    // Constructor
    function new(string name = "axi4_exclusive_monitor_model");
        super.new(name);
    endfunction
    
    // Configure
    function void configure(int num_m, int num_s);
        num_masters = num_m;
        num_slaves = num_s;
    endfunction
    
    // Process exclusive transaction - predict response
    function axi4_resp_e process_exclusive_transaction(int master_id, int slave_id, axi4_transaction trans);
        bit [63:0] aligned_addr = trans.addr & ~((1 << trans.size) - 1);
        axi4_resp_e predicted_resp;
        
        if (trans.trans_type == AXI4_READ && trans.lock == 1'b1) begin
            // Exclusive read - create reservation
            create_exclusive_reservation(master_id, slave_id, trans);
            predicted_resp = AXI4_OKAY;
            
        end else if (trans.trans_type == AXI4_WRITE && trans.lock == 1'b1) begin
            // Exclusive write - check reservation
            predicted_resp = check_exclusive_write(master_id, slave_id, trans);
            
        end else if (trans.trans_type == AXI4_WRITE) begin
            // Normal write - may clear reservations
            clear_overlapping_reservations(slave_id, trans);
            predicted_resp = AXI4_OKAY;
        end else begin
            predicted_resp = AXI4_OKAY;
        end
        
        return predicted_resp;
    endfunction
    
    // Create exclusive reservation
    function void create_exclusive_reservation(int master_id, int slave_id, axi4_transaction trans);
        bit [63:0] aligned_addr = trans.addr & ~((1 << trans.size) - 1);
        exclusive_entry_t entry;
        
        // Check constraints
        if (!check_exclusive_constraints(trans)) begin
            `uvm_error(get_name(), "Exclusive access violates constraints")
            return;
        end
        
        // Create entry
        entry.valid = 1;
        entry.address = aligned_addr;
        entry.size = trans.size;
        entry.id = trans.id;
        entry.master_id = master_id;
        entry.slave_id = slave_id;
        entry.reservation_time = $time;
        
        // Store reservation
        exclusive_table[slave_id][aligned_addr] = entry;
        
        `uvm_info(get_name(), $sformatf("Created exclusive reservation: Master[%0d], Slave[%0d], Addr=%0h, ID=%0h",
                                       master_id, slave_id, aligned_addr, trans.id), UVM_MEDIUM)
    endfunction
    
    // Check exclusive write
    function axi4_resp_e check_exclusive_write(int master_id, int slave_id, axi4_transaction trans);
        bit [63:0] aligned_addr = trans.addr & ~((1 << trans.size) - 1);
        
        // Check if reservation exists
        if (!exclusive_table[slave_id].exists(aligned_addr)) begin
            `uvm_info(get_name(), "Exclusive write: No reservation found", UVM_MEDIUM)
            return AXI4_OKAY;
        end
        
        exclusive_entry_t entry = exclusive_table[slave_id][aligned_addr];
        
        // Check if valid
        if (!entry.valid) begin
            return AXI4_OKAY;
        end
        
        // Check timeout
        if (enable_timeout && (($time - entry.reservation_time) > exclusive_timeout_ns * 1ns)) begin
            `uvm_info(get_name(), "Exclusive write: Reservation timed out", UVM_MEDIUM)
            entry.valid = 0;
            exclusive_table[slave_id][aligned_addr] = entry;
            return AXI4_OKAY;
        end
        
        // Check match - MUST match RTL logic exactly
        if (entry.master_id == master_id &&
            entry.id == trans.id &&
            entry.size == trans.size) begin
            // Success - clear reservation
            entry.valid = 0;
            exclusive_table[slave_id][aligned_addr] = entry;
            `uvm_info(get_name(), "Exclusive write: SUCCESS", UVM_MEDIUM)
            return AXI4_EXOKAY;
        end else begin
            // Mismatch
            `uvm_info(get_name(), $sformatf("Exclusive write: FAIL - Mismatch (master:%0d/%0d, id:%0h/%0h, size:%0d/%0d)",
                                           master_id, entry.master_id, trans.id, entry.id, 
                                           trans.size, entry.size), UVM_MEDIUM)
            return AXI4_OKAY;
        end
    endfunction
    
    // Clear overlapping reservations
    function void clear_overlapping_reservations(int slave_id, axi4_transaction trans);
        bit [63:0] start_addr = trans.addr;
        bit [63:0] end_addr = start_addr + ((trans.len + 1) * (1 << trans.size)) - 1;
        
        foreach (exclusive_table[slave_id][addr]) begin
            if (exclusive_table[slave_id][addr].valid) begin
                bit [63:0] res_addr = addr;
                bit [63:0] res_end = res_addr + (1 << exclusive_table[slave_id][addr].size) - 1;
                
                // Check overlap
                if (!((end_addr < res_addr) || (start_addr > res_end))) begin
                    exclusive_table[slave_id][addr].valid = 0;
                    `uvm_info(get_name(), $sformatf("Cleared exclusive reservation at %0h due to write", addr), UVM_HIGH)
                end
            end
        end
    endfunction
    
    // Check exclusive constraints
    function bit check_exclusive_constraints(axi4_transaction trans);
        // Burst length must be 1
        if (trans.len != 0) return 0;
        
        // Size must be power of 2 and <= 128 bytes
        if (!(1 << trans.size inside {1, 2, 4, 8, 16, 32, 64, 128})) return 0;
        
        // Must be aligned
        if (trans.addr & ((1 << trans.size) - 1)) return 0;
        
        return 1;
    endfunction
    
    // Clean expired reservations
    function void clean_expired_reservations();
        if (!enable_timeout) return;
        
        foreach (exclusive_table[slave_id]) begin
            foreach (exclusive_table[slave_id][addr]) begin
                if (exclusive_table[slave_id][addr].valid) begin
                    if (($time - exclusive_table[slave_id][addr].reservation_time) > exclusive_timeout_ns * 1ns) begin
                        exclusive_table[slave_id][addr].valid = 0;
                        `uvm_info(get_name(), $sformatf("Expired reservation: Slave[%0d], Addr=%0h",
                                                       slave_id, addr), UVM_HIGH)
                    end
                end
            end
        end
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_exclusive_monitor_model.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_transaction_predictor(self, output_dir: str):
        """Generate transaction predictor"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Transaction Predictor
// Generated: {self.timestamp}
// Description: Predicts expected transactions based on input
//------------------------------------------------------------------------------

class axi4_transaction_predictor extends uvm_component;
    
    `uvm_component_utils(axi4_transaction_predictor)
    
    // Analysis ports
    uvm_analysis_imp #(axi4_transaction, axi4_transaction_predictor) master_export;
    uvm_analysis_port #(axi4_transaction) predicted_port;
    
    // Reference models
    axi4_bus_matrix_model matrix_model;
    
    // Configuration
    axi4_vip_config cfg;
    
    // Constructor
    function new(string name = "axi4_transaction_predictor", uvm_component parent = null);
        super.new(name, parent);
        master_export = new("master_export", this);
        predicted_port = new("predicted_port", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        if (!uvm_config_db#(axi4_vip_config)::get(this, "", "axi4_vip_config", cfg)) begin
            `uvm_fatal("CONFIG", "Failed to get axi4_vip_config")
        end
        
        // Get reference model
        if (!uvm_config_db#(axi4_bus_matrix_model)::get(this, "", "matrix_model", matrix_model)) begin
            `uvm_error(get_name(), "Failed to get matrix_model from config DB")
        end
    endfunction
    
    // Write method
    function void write(axi4_transaction trans);
        predict_transaction(trans);
    endfunction
    
    // Predict transaction outcome
    function void predict_transaction(axi4_transaction trans);
        axi4_transaction predicted;
        
        // Clone transaction
        predicted = axi4_transaction::type_id::create("predicted");
        predicted.copy(trans);
        
        // Add predictions based on bus matrix model
        predict_routing(predicted);
        predict_id_mapping(predicted);
        predict_response(predicted);
        predict_timing(predicted);
        
        // Send predicted transaction
        predicted_port.write(predicted);
    endfunction
    
    // Predict routing
    function void predict_routing(axi4_transaction trans);
        int target_slave;
        
        // Use address decoder from matrix model
        target_slave = matrix_model.address_decoder.decode_address(trans.addr);
        
        if (target_slave == -1) begin
            trans.predicted_slave = -1;
            trans.predicted_response = AXI4_DECERR;
        end else begin
            trans.predicted_slave = target_slave;
        end
    endfunction
    
    // Predict ID mapping
    function void predict_id_mapping(axi4_transaction trans);
        // Use ID mapping model
        if (trans.source_master >= 0) begin
            axi4_transaction mapped = matrix_model.id_mapping_model.map_transaction(
                trans.source_master, trans
            );
            trans.predicted_id = mapped.id;
        end
    endfunction
    
    // Predict response
    function void predict_response(axi4_transaction trans);
        // Default prediction
        if (trans.predicted_response == AXI4_DECERR) begin
            // Already set
        end else if (trans.lock == 1'b1) begin
            // Exclusive access
            trans.predicted_response = matrix_model.exclusive_monitor.process_exclusive_transaction(
                trans.source_master,
                trans.predicted_slave,
                trans
            );
        end else begin
            trans.predicted_response = AXI4_OKAY;
        end
    endfunction
    
    // Predict timing
    function void predict_timing(axi4_transaction trans);
        int arb_delay;
        
        // Get arbitration delay
        if (trans.source_master >= 0 && trans.predicted_slave >= 0) begin
            arb_delay = matrix_model.arbitration_model.get_arbitration_delay(
                trans.source_master,
                trans.predicted_slave,
                trans.trans_type
            );
            
            trans.predicted_latency = arb_delay + 1; // Basic prediction
        end
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_transaction_predictor.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_scoreboard_predictor(self, output_dir: str):
        """Generate scoreboard with predictor integration"""
        
        content = f'''`timescale 1ns/1ps
//------------------------------------------------------------------------------
// Scoreboard with Reference Model
// Generated: {self.timestamp}
// Description: Scoreboard that uses reference model for checking
//------------------------------------------------------------------------------

class axi4_reference_scoreboard extends uvm_scoreboard;
    
    `uvm_component_utils(axi4_reference_scoreboard)
    
    // Analysis exports
    uvm_analysis_imp_decl(_actual)
    uvm_analysis_imp_decl(_predicted)
    
    uvm_analysis_imp_actual #(axi4_transaction, axi4_reference_scoreboard) actual_export;
    uvm_analysis_imp_predicted #(axi4_transaction, axi4_reference_scoreboard) predicted_export;
    
    // Transaction queues
    axi4_transaction actual_queue[$];
    axi4_transaction predicted_queue[$];
    
    // Reference model handle
    axi4_bus_matrix_model matrix_model;
    
    // Statistics
    int match_count = 0;
    int mismatch_count = 0;
    int total_checked = 0;
    
    // Mismatch details
    int routing_mismatches = 0;
    int id_mismatches = 0;
    int response_mismatches = 0;
    int data_mismatches = 0;
    
    // Constructor
    function new(string name = "axi4_reference_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        actual_export = new("actual_export", this);
        predicted_export = new("predicted_export", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get reference model
        if (!uvm_config_db#(axi4_bus_matrix_model)::get(this, "", "matrix_model", matrix_model)) begin
            `uvm_error(get_name(), "Failed to get matrix_model from config DB")
        end
    endfunction
    
    // Write actual transaction
    function void write_actual(axi4_transaction trans);
        actual_queue.push_back(trans);
        check_transactions();
    endfunction
    
    // Write predicted transaction
    function void write_predicted(axi4_transaction trans);
        predicted_queue.push_back(trans);
        check_transactions();
    endfunction
    
    // Check transactions
    function void check_transactions();
        while (actual_queue.size() > 0 && predicted_queue.size() > 0) begin
            axi4_transaction actual = actual_queue.pop_front();
            axi4_transaction predicted = find_matching_predicted(actual);
            
            if (predicted != null) begin
                compare_transactions(actual, predicted);
            end else begin
                `uvm_error(get_name(), $sformatf("No matching prediction for actual transaction: %s",
                                                actual.convert2string()))
                mismatch_count++;
            end
            
            total_checked++;
        end
    endfunction
    
    // Find matching predicted transaction
    function axi4_transaction find_matching_predicted(axi4_transaction actual);
        foreach (predicted_queue[i]) begin
            if (transactions_match(actual, predicted_queue[i])) begin
                return predicted_queue.delete(i);
            end
        end
        return null;
    endfunction
    
    // Check if transactions match (for pairing)
    function bit transactions_match(axi4_transaction actual, axi4_transaction predicted);
        // Match based on key fields
        if (actual.trans_type != predicted.trans_type) return 0;
        if (actual.source_master != predicted.source_master) return 0;
        if (actual.addr != predicted.addr) return 0;
        if (actual.original_id != predicted.original_id) return 0;
        
        return 1;
    endfunction
    
    // Compare transactions in detail
    function void compare_transactions(axi4_transaction actual, axi4_transaction predicted);
        bit match = 1;
        string mismatch_details = "";
        
        // Check routing
        if (actual.routed_to_slave != predicted.predicted_slave) begin
            mismatch_details = {mismatch_details, 
                               $sformatf("\\n  Routing: actual=%0d, predicted=%0d",
                                        actual.routed_to_slave, predicted.predicted_slave)};
            routing_mismatches++;
            match = 0;
        end
        
        // Check ID mapping
        if (actual.id != predicted.predicted_id) begin
            mismatch_details = {mismatch_details,
                               $sformatf("\\n  ID: actual=%0h, predicted=%0h",
                                        actual.id, predicted.predicted_id)};
            id_mismatches++;
            match = 0;
        end
        
        // Check response
        if (actual.resp != predicted.predicted_response) begin
            mismatch_details = {mismatch_details,
                               $sformatf("\\n  Response: actual=%s, predicted=%s",
                                        actual.resp.name(), predicted.predicted_response.name())};
            response_mismatches++;
            match = 0;
        end
        
        // Check data (for reads)
        if (actual.trans_type == AXI4_READ && actual.data.size() > 0) begin
            foreach (actual.data[i]) begin
                if (actual.data[i] != predicted.data[i]) begin
                    mismatch_details = {mismatch_details,
                                       $sformatf("\\n  Data[%0d]: actual=%0h, predicted=%0h",
                                                i, actual.data[i], predicted.data[i])};
                    data_mismatches++;
                    match = 0;
                    break;
                end
            end
        end
        
        // Report result
        if (match) begin
            match_count++;
            `uvm_info(get_name(), $sformatf("Transaction MATCH: %s", actual.convert2string()), UVM_HIGH)
        end else begin
            mismatch_count++;
            `uvm_error(get_name(), $sformatf("Transaction MISMATCH: %s%s",
                                            actual.convert2string(), mismatch_details))
        end
    endfunction
    
    // Check phase
    function void check_phase(uvm_phase phase);
        if (actual_queue.size() > 0) begin
            `uvm_error(get_name(), $sformatf("%0d unmatched actual transactions", actual_queue.size()))
        end
        
        if (predicted_queue.size() > 0) begin
            `uvm_error(get_name(), $sformatf("%0d unmatched predicted transactions", predicted_queue.size()))
        end
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_name(), "=== Reference Model Scoreboard Report ===", UVM_LOW)
        `uvm_info(get_name(), $sformatf("Total Checked: %0d", total_checked), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Matches: %0d (%.1f%%)", 
                                       match_count, real'(match_count)/total_checked*100.0), UVM_LOW)
        `uvm_info(get_name(), $sformatf("Mismatches: %0d", mismatch_count), UVM_LOW)
        
        if (mismatch_count > 0) begin
            `uvm_info(get_name(), "Mismatch Details:", UVM_LOW)
            `uvm_info(get_name(), $sformatf("  Routing: %0d", routing_mismatches), UVM_LOW)
            `uvm_info(get_name(), $sformatf("  ID Mapping: %0d", id_mismatches), UVM_LOW)
            `uvm_info(get_name(), $sformatf("  Response: %0d", response_mismatches), UVM_LOW)
            `uvm_info(get_name(), $sformatf("  Data: %0d", data_mismatches), UVM_LOW)
        end
        
        if (mismatch_count == 0 && match_count > 0) begin
            `uvm_info(get_name(), "ALL TRANSACTIONS MATCHED REFERENCE MODEL!", UVM_LOW)
        end
    endfunction
    
endclass
'''
        
        filepath = os.path.join(output_dir, "axi4_reference_scoreboard.sv")
        with open(filepath, 'w') as f:
            f.write(content)

def example_reference_model_generation():
    """Example of generating bus matrix reference model"""
    
    # Configuration must match GUI settings exactly
    config = {
        'num_masters': 4,
        'num_slaves': 4,
        'data_width': 128,
        'addr_width': 64,
        'id_width': 8,
        'user_width': 32,
        'memory_map': [
            {'slave_id': 0, 'base_addr': 0x00000000, 'size': 0x40000000, 'end_addr': 0x3FFFFFFF, 'name': 'ddr0'},
            {'slave_id': 1, 'base_addr': 0x40000000, 'size': 0x40000000, 'end_addr': 0x7FFFFFFF, 'name': 'ddr1'},
            {'slave_id': 2, 'base_addr': 0x80000000, 'size': 0x20000000, 'end_addr': 0x9FFFFFFF, 'name': 'sram'},
            {'slave_id': 3, 'base_addr': 0xA0000000, 'size': 0x60000000, 'end_addr': 0xFFFFFFFF, 'name': 'periph'}
        ],
        'arbitration_scheme': 'round_robin',
        'qos_enable': True,
        'support_exclusive': True
    }
    
    generator = VIPBusMatrixReferenceModel(config)
    output_dir = "vip_output/reference_model"
    os.makedirs(output_dir, exist_ok=True)
    
    print("Generating bus matrix reference model...")
    generator.generate_reference_model(output_dir)
    print("Reference model generation complete!")
    print(f"Configuration saved to: {output_dir}/reference_model_config.json")

if __name__ == "__main__":
    example_reference_model_generation()