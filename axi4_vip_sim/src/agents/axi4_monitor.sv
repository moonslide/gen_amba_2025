//==============================================================================
// AXI4 Monitor - Passive monitoring of AXI4 transactions
// Collects protocol compliance data and functional coverage
//==============================================================================

class axi4_monitor extends uvm_monitor;
    
    // Factory registration
    `uvm_component_utils(axi4_monitor)
    
    // Virtual interface handle
    virtual axi4_if.monitor vif;
    
    // Analysis port for sending transactions to scoreboard
    uvm_analysis_port #(axi4_transaction) ap;
    
    // Transaction tracking
    typedef struct {
        bit [7:0] id;
        bit [63:0] addr;
        bit [7:0] len;
        bit [2:0] size;
        bit [1:0] burst;
        bit [2:0] prot;
        bit [3:0] qos;
        bit [3:0] region;
        bit [3:0] cache;
        realtime start_time;
        axi4_transaction trans;
    } tracked_trans_t;
    
    tracked_trans_t outstanding_writes[bit [7:0]];  // Keyed by ID
    tracked_trans_t outstanding_reads[bit [7:0]];   // Keyed by ID
    
    // Statistics and coverage
    int num_write_transactions = 0;
    int num_read_transactions = 0;
    int num_protocol_violations = 0;
    int num_4kb_violations = 0;
    int num_exclusive_transactions = 0;
    
    real total_write_latency = 0.0;
    real total_read_latency = 0.0;
    real max_write_latency = 0.0;
    real max_read_latency = 0.0;
    
    // Coverage groups
    covergroup axi4_transaction_coverage;
        option.per_instance = 1;
        
        cp_burst_type: coverpoint vif.monitor_cb.awburst iff (vif.monitor_cb.awvalid && vif.monitor_cb.awready) {
            bins fixed = {2'b00};
            bins incr = {2'b01};
            bins wrap = {2'b10};
            illegal_bins reserved = {2'b11};
        }
        
        cp_burst_length: coverpoint vif.monitor_cb.awlen iff (vif.monitor_cb.awvalid && vif.monitor_cb.awready) {
            bins single = {0};
            bins short_burst = {[1:15]};
            bins long_burst = {[16:255]};
        }
        
        cp_transfer_size: coverpoint vif.monitor_cb.awsize iff (vif.monitor_cb.awvalid && vif.monitor_cb.awready) {
            bins byte_transfer = {0};
            bins halfword_transfer = {1};
            bins word_transfer = {2};
            bins doubleword_transfer = {3};
            bins large_transfer = {[4:7]};
        }
        
        cp_qos: coverpoint vif.monitor_cb.awqos iff (vif.monitor_cb.awvalid && vif.monitor_cb.awready) {
            bins low_priority = {[0:3]};
            bins med_priority = {[4:7]};
            bins high_priority = {[8:11]};
            bins critical_priority = {[12:15]};
        }
        
        cp_prot: coverpoint vif.monitor_cb.awprot iff (vif.monitor_cb.awvalid && vif.monitor_cb.awready) {
            bins unpriv_nonsecure_data = {3'b000};
            bins priv_nonsecure_data = {3'b001};
            bins unpriv_secure_data = {3'b010};
            bins priv_secure_data = {3'b011};
            bins unpriv_nonsecure_inst = {3'b100};
            bins priv_nonsecure_inst = {3'b101};
            bins unpriv_secure_inst = {3'b110};
            bins priv_secure_inst = {3'b111};
        }
        
        cp_cache: coverpoint vif.monitor_cb.awcache iff (vif.monitor_cb.awvalid && vif.monitor_cb.awready) {
            bins device_non_bufferable = {4'b0000};
            bins device_bufferable = {4'b0001};
            bins normal_non_cacheable_non_bufferable = {4'b0010};
            bins normal_non_cacheable_bufferable = {4'b0011};
            bins write_through_no_allocate = {4'b0110};
            bins write_through_read_allocate = {4'b0111};
            bins write_through_write_allocate = {4'b1010};
            bins write_through_both_allocate = {4'b1011};
            bins write_back_no_allocate = {4'b1110};
            bins write_back_read_allocate = {4'b1111};
            bins write_back_write_allocate = {4'b1110};
            bins write_back_both_allocate = {4'b1111};
        }
        
        // Cross coverage
        cross_burst_length_size: cross cp_burst_type, cp_burst_length, cp_transfer_size;
        cross_qos_prot: cross cp_qos, cp_prot;
    endgroup
    
    // Constructor
    function new(string name = "axi4_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
        axi4_transaction_coverage = new();
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi4_if.monitor)::get(this, "", "vif", vif)) begin
            `uvm_fatal("NOVIF", "Virtual interface must be set for: " + get_full_name())
        end
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        // Wait for reset release
        wait_for_reset_release();
        
        // Fork monitoring processes
        fork
            monitor_write_address_channel();
            monitor_write_data_channel();
            monitor_write_response_channel();
            monitor_read_address_channel();
            monitor_read_data_channel();
            check_protocol_violations();
        join_none
        
        // Keep alive
        wait fork;
    endtask
    
    // Wait for reset deassertion
    virtual task wait_for_reset_release();
        `uvm_info(get_type_name(), "Waiting for reset release", UVM_MEDIUM)
        wait (vif.aresetn === 1'b0);
        wait (vif.aresetn === 1'b1);
        repeat (2) @(vif.monitor_cb);
        `uvm_info(get_type_name(), "Reset released, monitoring started", UVM_MEDIUM)
    endtask
    
    // Monitor write address channel
    virtual task monitor_write_address_channel();
        tracked_trans_t tracked;
        
        forever begin
            @(vif.monitor_cb);
            
            if (vif.monitor_cb.awvalid && vif.monitor_cb.awready) begin
                // Sample coverage
                axi4_transaction_coverage.sample();
                
                // Create transaction tracking
                tracked.id = vif.monitor_cb.awid;
                tracked.addr = vif.monitor_cb.awaddr;
                tracked.len = vif.monitor_cb.awlen;
                tracked.size = vif.monitor_cb.awsize;
                tracked.burst = vif.monitor_cb.awburst;
                tracked.prot = vif.monitor_cb.awprot;
                tracked.qos = vif.monitor_cb.awqos;
                tracked.region = vif.monitor_cb.awregion;
                tracked.cache = vif.monitor_cb.awcache;
                tracked.start_time = $realtime;
                
                // Create transaction object
                tracked.trans = axi4_transaction::type_id::create("write_trans");
                tracked.trans.trans_type = axi4_transaction::WRITE_TRANS;
                tracked.trans.id = tracked.id;
                tracked.trans.addr = tracked.addr;
                tracked.trans.len = tracked.len;
                tracked.trans.size = tracked.size;
                tracked.trans.burst_type = axi4_transaction::burst_type_e'(tracked.burst);
                tracked.trans.cache = tracked.cache;
                tracked.trans.qos = tracked.qos;
                tracked.trans.region = tracked.region;
                tracked.trans.user = vif.monitor_cb.awuser;
                
                // Extract protection bits
                tracked.trans.privilege = axi4_transaction::privilege_e'(tracked.prot[0]);
                tracked.trans.security = axi4_transaction::security_e'(tracked.prot[1]);
                tracked.trans.access_type = axi4_transaction::access_type_e'(tracked.prot[2]);
                
                // Initialize data arrays
                tracked.trans.data = new[tracked.len + 1];
                tracked.trans.strb = new[tracked.len + 1];
                tracked.trans.wuser = new[tracked.len + 1];
                
                // Check for 4KB boundary violation
                if (check_4kb_boundary_violation(tracked.addr, tracked.len, tracked.size)) begin
                    num_4kb_violations++;
                    `uvm_error(get_type_name(), $sformatf("4KB boundary violation detected: ID=0x%0h, Addr=0x%0h, Len=%0d, Size=%0d", 
                                                          tracked.id, tracked.addr, tracked.len, tracked.size))
                end
                
                // Store in outstanding transactions
                outstanding_writes[tracked.id] = tracked;
                num_write_transactions++;
                
                `uvm_info(get_type_name(), $sformatf("Write address captured: ID=0x%0h, Addr=0x%0h, Len=%0d, QoS=%0d", 
                                                     tracked.id, tracked.addr, tracked.len+1, tracked.qos), UVM_HIGH)
            end
        end
    endtask
    
    // Monitor write data channel
    virtual task monitor_write_data_channel();
        bit [7:0] current_beat[bit [7:0]]; // Track beat count per ID
        
        forever begin
            @(vif.monitor_cb);
            
            if (vif.monitor_cb.wvalid && vif.monitor_cb.wready) begin
                // Find transaction by matching with outstanding writes
                // In a real implementation, we'd need more sophisticated ID tracking
                foreach (outstanding_writes[id]) begin
                    if (current_beat.exists(id) || current_beat[id] == 0) begin
                        // Capture data
                        outstanding_writes[id].trans.data[current_beat[id]] = vif.monitor_cb.wdata;
                        outstanding_writes[id].trans.strb[current_beat[id]] = vif.monitor_cb.wstrb;
                        outstanding_writes[id].trans.wuser[current_beat[id]] = vif.monitor_cb.wuser;
                        
                        `uvm_info(get_type_name(), $sformatf("Write data captured: ID=0x%0h, Beat=%0d, Data=0x%0h, WLAST=%0b", 
                                                             id, current_beat[id], vif.monitor_cb.wdata, vif.monitor_cb.wlast), UVM_HIGH)
                        
                        current_beat[id]++;
                        
                        // Check for last beat
                        if (vif.monitor_cb.wlast) begin
                            if (current_beat[id] != (outstanding_writes[id].len + 1)) begin
                                `uvm_error(get_type_name(), $sformatf("WLAST mismatch: ID=0x%0h, Expected beats=%0d, Actual beats=%0d", 
                                                                      id, outstanding_writes[id].len + 1, current_beat[id]))
                                num_protocol_violations++;
                            end
                            current_beat.delete(id);
                            break;
                        end
                    end
                end
            end
        end
    endtask
    
    // Monitor write response channel
    virtual task monitor_write_response_channel();
        real latency;
        
        forever begin
            @(vif.monitor_cb);
            
            if (vif.monitor_cb.bvalid && vif.monitor_cb.bready) begin
                if (outstanding_writes.exists(vif.monitor_cb.bid)) begin
                    // Calculate latency
                    latency = ($realtime - outstanding_writes[vif.monitor_cb.bid].start_time) / 1ns;
                    total_write_latency += latency;
                    if (latency > max_write_latency) max_write_latency = latency;
                    
                    // Complete transaction
                    outstanding_writes[vif.monitor_cb.bid].trans.bresp = axi4_transaction::resp_type_e'(vif.monitor_cb.bresp);
                    outstanding_writes[vif.monitor_cb.bid].trans.buser = vif.monitor_cb.buser;
                    
                    // Send to scoreboard
                    ap.write(outstanding_writes[vif.monitor_cb.bid].trans);
                    
                    `uvm_info(get_type_name(), $sformatf("Write transaction completed: ID=0x%0h, BRESP=%s, Latency=%.2f ns", 
                                                         vif.monitor_cb.bid, get_response_name(vif.monitor_cb.bresp), latency), UVM_HIGH)
                    
                    // Remove from outstanding
                    outstanding_writes.delete(vif.monitor_cb.bid);
                end else begin
                    `uvm_error(get_type_name(), $sformatf("Unexpected write response for ID=0x%0h", vif.monitor_cb.bid))
                    num_protocol_violations++;
                end
            end
        end
    endtask
    
    // Monitor read address channel
    virtual task monitor_read_address_channel();
        tracked_trans_t tracked;
        
        forever begin
            @(vif.monitor_cb);
            
            if (vif.monitor_cb.arvalid && vif.monitor_cb.arready) begin
                // Create transaction tracking
                tracked.id = vif.monitor_cb.arid;
                tracked.addr = vif.monitor_cb.araddr;
                tracked.len = vif.monitor_cb.arlen;
                tracked.size = vif.monitor_cb.arsize;
                tracked.burst = vif.monitor_cb.arburst;
                tracked.prot = vif.monitor_cb.arprot;
                tracked.qos = vif.monitor_cb.arqos;
                tracked.region = vif.monitor_cb.arregion;
                tracked.cache = vif.monitor_cb.arcache;
                tracked.start_time = $realtime;
                
                // Create transaction object
                tracked.trans = axi4_transaction::type_id::create("read_trans");
                tracked.trans.trans_type = axi4_transaction::READ_TRANS;
                tracked.trans.id = tracked.id;
                tracked.trans.addr = tracked.addr;
                tracked.trans.len = tracked.len;
                tracked.trans.size = tracked.size;
                tracked.trans.burst_type = axi4_transaction::burst_type_e'(tracked.burst);
                tracked.trans.cache = tracked.cache;
                tracked.trans.qos = tracked.qos;
                tracked.trans.region = tracked.region;
                tracked.trans.user = vif.monitor_cb.aruser;
                
                // Extract protection bits
                tracked.trans.privilege = axi4_transaction::privilege_e'(tracked.prot[0]);
                tracked.trans.security = axi4_transaction::security_e'(tracked.prot[1]);
                tracked.trans.access_type = axi4_transaction::access_type_e'(tracked.prot[2]);
                
                // Initialize data arrays
                tracked.trans.rdata = new[tracked.len + 1];
                tracked.trans.rresp = new[tracked.len + 1];
                tracked.trans.ruser = new[tracked.len + 1];
                
                // Check for 4KB boundary violation
                if (check_4kb_boundary_violation(tracked.addr, tracked.len, tracked.size)) begin
                    num_4kb_violations++;
                    `uvm_error(get_type_name(), $sformatf("4KB boundary violation detected: ID=0x%0h, Addr=0x%0h, Len=%0d, Size=%0d", 
                                                          tracked.id, tracked.addr, tracked.len, tracked.size))
                end
                
                // Store in outstanding transactions
                outstanding_reads[tracked.id] = tracked;
                num_read_transactions++;
                
                `uvm_info(get_type_name(), $sformatf("Read address captured: ID=0x%0h, Addr=0x%0h, Len=%0d, QoS=%0d", 
                                                     tracked.id, tracked.addr, tracked.len+1, tracked.qos), UVM_HIGH)
            end
        end
    endtask
    
    // Monitor read data channel
    virtual task monitor_read_data_channel();
        bit [7:0] current_beat[bit [7:0]]; // Track beat count per ID
        real latency;
        
        forever begin
            @(vif.monitor_cb);
            
            if (vif.monitor_cb.rvalid && vif.monitor_cb.rready) begin
                if (outstanding_reads.exists(vif.monitor_cb.rid)) begin
                    // Capture data
                    if (!current_beat.exists(vif.monitor_cb.rid)) current_beat[vif.monitor_cb.rid] = 0;
                    
                    outstanding_reads[vif.monitor_cb.rid].trans.rdata[current_beat[vif.monitor_cb.rid]] = vif.monitor_cb.rdata;
                    outstanding_reads[vif.monitor_cb.rid].trans.rresp[current_beat[vif.monitor_cb.rid]] = axi4_transaction::resp_type_e'(vif.monitor_cb.rresp);
                    outstanding_reads[vif.monitor_cb.rid].trans.ruser[current_beat[vif.monitor_cb.rid]] = vif.monitor_cb.ruser;
                    
                    `uvm_info(get_type_name(), $sformatf("Read data captured: ID=0x%0h, Beat=%0d, Data=0x%0h, RLAST=%0b", 
                                                         vif.monitor_cb.rid, current_beat[vif.monitor_cb.rid], vif.monitor_cb.rdata, vif.monitor_cb.rlast), UVM_HIGH)
                    
                    current_beat[vif.monitor_cb.rid]++;
                    
                    // Check for last beat
                    if (vif.monitor_cb.rlast) begin
                        if (current_beat[vif.monitor_cb.rid] != (outstanding_reads[vif.monitor_cb.rid].len + 1)) begin
                            `uvm_error(get_type_name(), $sformatf("RLAST mismatch: ID=0x%0h, Expected beats=%0d, Actual beats=%0d", 
                                                                  vif.monitor_cb.rid, outstanding_reads[vif.monitor_cb.rid].len + 1, current_beat[vif.monitor_cb.rid]))
                            num_protocol_violations++;
                        end
                        
                        // Calculate latency
                        latency = ($realtime - outstanding_reads[vif.monitor_cb.rid].start_time) / 1ns;
                        total_read_latency += latency;
                        if (latency > max_read_latency) max_read_latency = latency;
                        
                        // Send to scoreboard
                        ap.write(outstanding_reads[vif.monitor_cb.rid].trans);
                        
                        `uvm_info(get_type_name(), $sformatf("Read transaction completed: ID=0x%0h, Latency=%.2f ns", 
                                                             vif.monitor_cb.rid, latency), UVM_HIGH)
                        
                        // Cleanup
                        outstanding_reads.delete(vif.monitor_cb.rid);
                        current_beat.delete(vif.monitor_cb.rid);
                    end
                end else begin
                    `uvm_error(get_type_name(), $sformatf("Unexpected read data for ID=0x%0h", vif.monitor_cb.rid))
                    num_protocol_violations++;
                end
            end
        end
    endtask
    
    // Protocol violation checker
    virtual task check_protocol_violations();
        bit awvalid_prev = 0, awready_prev = 0;
        bit arvalid_prev = 0, arready_prev = 0;
        bit wvalid_prev = 0, wready_prev = 0;
        bit rvalid_prev = 0, rready_prev = 0;
        bit bvalid_prev = 0, bready_prev = 0;
        
        forever begin
            @(vif.monitor_cb);
            
            // Check VALID-READY handshake stability
            if (awvalid_prev && !vif.monitor_cb.awready && !vif.monitor_cb.awvalid) begin
                `uvm_error(get_type_name(), "AWVALID deasserted before AWREADY")
                num_protocol_violations++;
            end
            
            if (arvalid_prev && !vif.monitor_cb.arready && !vif.monitor_cb.arvalid) begin
                `uvm_error(get_type_name(), "ARVALID deasserted before ARREADY")
                num_protocol_violations++;
            end
            
            if (wvalid_prev && !vif.monitor_cb.wready && !vif.monitor_cb.wvalid) begin
                `uvm_error(get_type_name(), "WVALID deasserted before WREADY")
                num_protocol_violations++;
            end
            
            if (rvalid_prev && !vif.monitor_cb.rready && !vif.monitor_cb.rvalid) begin
                `uvm_error(get_type_name(), "RVALID deasserted before RREADY")
                num_protocol_violations++;
            end
            
            if (bvalid_prev && !vif.monitor_cb.bready && !vif.monitor_cb.bvalid) begin
                `uvm_error(get_type_name(), "BVALID deasserted before BREADY")
                num_protocol_violations++;
            end
            
            // Update previous values
            awvalid_prev = vif.monitor_cb.awvalid;
            awready_prev = vif.monitor_cb.awready;
            arvalid_prev = vif.monitor_cb.arvalid;
            arready_prev = vif.monitor_cb.arready;
            wvalid_prev = vif.monitor_cb.wvalid;
            wready_prev = vif.monitor_cb.wready;
            rvalid_prev = vif.monitor_cb.rvalid;
            rready_prev = vif.monitor_cb.rready;
            bvalid_prev = vif.monitor_cb.bvalid;
            bready_prev = vif.monitor_cb.bready;
        end
    endtask
    
    // Utility functions
    function bit check_4kb_boundary_violation(bit [63:0] addr, bit [7:0] len, bit [2:0] size);
        bit [63:0] start_addr = addr;
        bit [63:0] end_addr = addr + ((len + 1) * (1 << size)) - 1;
        return (start_addr[63:12] != end_addr[63:12]);
    endfunction
    
    function string get_response_name(bit [1:0] resp);
        case (resp)
            2'b00: return "OKAY";
            2'b01: return "EXOKAY";
            2'b10: return "SLVERR";
            2'b11: return "DECERR";
            default: return "UNKNOWN";
        endcase
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        real avg_write_latency = (num_write_transactions > 0) ? total_write_latency / num_write_transactions : 0.0;
        real avg_read_latency = (num_read_transactions > 0) ? total_read_latency / num_read_transactions : 0.0;
        
        `uvm_info(get_type_name(), $sformatf("Monitor Statistics:"), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Write Transactions: %0d", num_write_transactions), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Read Transactions: %0d", num_read_transactions), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Protocol Violations: %0d", num_protocol_violations), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  4KB Violations: %0d", num_4kb_violations), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Exclusive Transactions: %0d", num_exclusive_transactions), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Avg Write Latency: %.2f ns", avg_write_latency), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Max Write Latency: %.2f ns", max_write_latency), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Avg Read Latency: %.2f ns", avg_read_latency), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Max Read Latency: %.2f ns", max_read_latency), UVM_LOW)
    endfunction
    
endclass : axi4_monitor