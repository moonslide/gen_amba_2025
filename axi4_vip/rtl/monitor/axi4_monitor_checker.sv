//==============================================================================
// AXI4 Monitor and Checker
// 
// Description: Monitors AXI4 transactions and checks protocol compliance
// Includes comprehensive assertions and coverage collection
//==============================================================================

`include "../common/axi4_defines.sv"

module axi4_monitor_checker #(
    parameter axi4_config_t CFG = '{
        ADDR_WIDTH: 32,
        DATA_WIDTH: 64,
        ID_WIDTH: 4,
        AWUSER_WIDTH: 0,
        WUSER_WIDTH: 0,
        BUSER_WIDTH: 0,
        ARUSER_WIDTH: 0,
        RUSER_WIDTH: 0,
        SUPPORT_USER_SIGNALS: 0,
        SUPPORT_REGION: 1,
        SUPPORT_QOS: 1,
        SUPPORT_EXCLUSIVE: 1
    },
    parameter bit ENABLE_ASSERTIONS = 1,
    parameter bit ENABLE_COVERAGE = 1,
    parameter bit ENABLE_TRANSACTION_LOG = 1
)(
    // AXI4 interface to monitor
    axi4_if.monitor axi,
    
    // Transaction output interface
    output logic                   trans_valid,
    output axi4_transaction_t      trans_out,
    input logic                    trans_ready,
    
    // Protocol violation outputs
    output logic                   protocol_error,
    output logic [31:0]            error_count,
    output string                  error_message,
    
    // Statistics
    output logic [31:0]            write_trans_count,
    output logic [31:0]            read_trans_count,
    output logic [31:0]            total_data_bytes
);

    // Transaction reconstruction queues
    axi4_transaction_t write_addr_queue[2**CFG.ID_WIDTH][$];
    axi4_transaction_t write_data_queue[$];
    axi4_transaction_t read_addr_queue[2**CFG.ID_WIDTH][$];
    logic [7:0] write_beat_count[2**CFG.ID_WIDTH];
    logic [7:0] read_beat_count[2**CFG.ID_WIDTH];
    
    // Error tracking
    logic [31:0] internal_error_count;
    string last_error_message;
    
    // Monitor write address channel
    always_ff @(posedge axi.aclk or negedge axi.aresetn) begin
        if (!axi.aresetn) begin
            for (int i = 0; i < 2**CFG.ID_WIDTH; i++) begin
                write_addr_queue[i].delete();
            end
        end else begin
            if (axi.awvalid && axi.awready) begin
                axi4_transaction_t trans;
                trans.id = axi.awid;
                trans.addr = axi.awaddr;
                trans.len = axi.awlen;
                trans.size = axi.awsize;
                trans.burst = axi4_burst_t'(axi.awburst);
                trans.lock = axi4_lock_t'(axi.awlock);
                trans.prot = '{axi.awprot[2], axi.awprot[1], axi.awprot[0]};
                trans.cache = '{axi.awcache[3], axi.awcache[2], axi.awcache[1], axi.awcache[0]};
                trans.qos = axi.awqos;
                trans.region = axi.awregion;
                trans.is_write = 1'b1;
                trans.start_time = $realtime;
                if (CFG.SUPPORT_USER_SIGNALS && CFG.AWUSER_WIDTH > 0)
                    trans.awuser = axi.awuser;
                
                write_addr_queue[axi.awid].push_back(trans);
                
                if (ENABLE_TRANSACTION_LOG) begin
                    $display("[%t] AXI_MON: Write Addr - ID=%0h ADDR=%0h LEN=%0d SIZE=%0d",
                             $time, trans.id, trans.addr, trans.len+1, trans.size);
                end
            end
        end
    end
    
    // Monitor write data channel
    always_ff @(posedge axi.aclk or negedge axi.aresetn) begin
        if (!axi.aresetn) begin
            for (int i = 0; i < 2**CFG.ID_WIDTH; i++) begin
                write_beat_count[i] <= '0;
            end
        end else begin
            if (axi.wvalid && axi.wready) begin
                // Store write data (need to match with address later)
                // This is simplified - proper implementation would track by ID
                
                if (ENABLE_TRANSACTION_LOG) begin
                    $display("[%t] AXI_MON: Write Data - STRB=%0h LAST=%b",
                             $time, axi.wstrb, axi.wlast);
                end
            end
        end
    end
    
    // Monitor write response channel
    always_ff @(posedge axi.aclk or negedge axi.aresetn) begin
        if (!axi.aresetn) begin
            write_trans_count <= '0;
        end else begin
            if (axi.bvalid && axi.bready) begin
                axi4_transaction_t trans;
                
                // Match with address phase
                if (write_addr_queue[axi.bid].size() > 0) begin
                    trans = write_addr_queue[axi.bid][0];
                    write_addr_queue[axi.bid].pop_front();
                    
                    trans.resp[0] = axi4_resp_t'(axi.bresp);
                    trans.end_time = $realtime;
                    if (CFG.SUPPORT_USER_SIGNALS && CFG.BUSER_WIDTH > 0)
                        trans.buser = axi.buser;
                    
                    // Output completed transaction
                    output_transaction(trans);
                    write_trans_count <= write_trans_count + 1;
                    
                    if (ENABLE_TRANSACTION_LOG) begin
                        $display("[%t] AXI_MON: Write Resp - ID=%0h RESP=%0s",
                                 $time, axi.bid, axi.bresp == 0 ? "OKAY" :
                                 axi.bresp == 1 ? "EXOKAY" :
                                 axi.bresp == 2 ? "SLVERR" : "DECERR");
                    end
                end
            end
        end
    end
    
    // Monitor read address channel
    always_ff @(posedge axi.aclk or negedge axi.aresetn) begin
        if (!axi.aresetn) begin
            for (int i = 0; i < 2**CFG.ID_WIDTH; i++) begin
                read_addr_queue[i].delete();
                read_beat_count[i] <= '0;
            end
        end else begin
            if (axi.arvalid && axi.arready) begin
                axi4_transaction_t trans;
                trans.id = axi.arid;
                trans.addr = axi.araddr;
                trans.len = axi.arlen;
                trans.size = axi.arsize;
                trans.burst = axi4_burst_t'(axi.arburst);
                trans.lock = axi4_lock_t'(axi.arlock);
                trans.prot = '{axi.arprot[2], axi.arprot[1], axi.arprot[0]};
                trans.cache = '{axi.arcache[3], axi.arcache[2], axi.arcache[1], axi.arcache[0]};
                trans.qos = axi.arqos;
                trans.region = axi.arregion;
                trans.is_write = 1'b0;
                trans.start_time = $realtime;
                if (CFG.SUPPORT_USER_SIGNALS && CFG.ARUSER_WIDTH > 0)
                    trans.aruser = axi.aruser;
                
                read_addr_queue[axi.arid].push_back(trans);
                
                if (ENABLE_TRANSACTION_LOG) begin
                    $display("[%t] AXI_MON: Read Addr - ID=%0h ADDR=%0h LEN=%0d SIZE=%0d",
                             $time, trans.id, trans.addr, trans.len+1, trans.size);
                end
            end
        end
    end
    
    // Monitor read data channel
    always_ff @(posedge axi.aclk or negedge axi.aresetn) begin
        if (!axi.aresetn) begin
            read_trans_count <= '0;
        end else begin
            if (axi.rvalid && axi.rready) begin
                int id = axi.rid;
                
                // Store read data
                if (read_addr_queue[id].size() > 0) begin
                    axi4_transaction_t trans = read_addr_queue[id][0];
                    
                    trans.data[read_beat_count[id]] = axi.rdata;
                    trans.resp[read_beat_count[id]] = axi4_resp_t'(axi.rresp);
                    if (CFG.SUPPORT_USER_SIGNALS && CFG.RUSER_WIDTH > 0)
                        trans.ruser[read_beat_count[id]] = axi.ruser;
                    
                    if (axi.rlast) begin
                        trans.end_time = $realtime;
                        read_addr_queue[id].pop_front();
                        read_beat_count[id] <= '0;
                        
                        // Output completed transaction
                        output_transaction(trans);
                        read_trans_count <= read_trans_count + 1;
                    end else begin
                        read_beat_count[id] <= read_beat_count[id] + 1;
                    end
                    
                    if (ENABLE_TRANSACTION_LOG) begin
                        $display("[%t] AXI_MON: Read Data - ID=%0h RESP=%0s LAST=%b",
                                 $time, axi.rid, axi.rresp == 0 ? "OKAY" :
                                 axi.rresp == 1 ? "EXOKAY" :
                                 axi.rresp == 2 ? "SLVERR" : "DECERR", axi.rlast);
                    end
                end
            end
        end
    end
    
    // Transaction output queue
    axi4_transaction_t output_queue[$];
    
    task output_transaction(axi4_transaction_t trans);
        output_queue.push_back(trans);
        
        // Calculate data bytes
        int bytes = (trans.len + 1) * (1 << trans.size);
        total_data_bytes <= total_data_bytes + bytes;
    endtask
    
    // Output interface
    always_ff @(posedge axi.aclk or negedge axi.aresetn) begin
        if (!axi.aresetn) begin
            trans_valid <= 1'b0;
            trans_out <= '0;
        end else begin
            if (trans_valid && trans_ready) begin
                trans_valid <= 1'b0;
                output_queue.pop_front();
            end
            
            if (!trans_valid && output_queue.size() > 0) begin
                trans_valid <= 1'b1;
                trans_out <= output_queue[0];
            end
        end
    end
    
    // Protocol error detection
    always_comb begin
        protocol_error = internal_error_count > 0;
        error_count = internal_error_count;
        error_message = last_error_message;
    end
    
    // Helper function to report errors
    function void report_error(string msg);
        internal_error_count = internal_error_count + 1;
        last_error_message = msg;
        $error("[%t] AXI_CHECKER: %s", $time, msg);
    endfunction
    
    // Protocol Assertions
    generate if (ENABLE_ASSERTIONS) begin : assertions
        
        // AW channel assertions
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.awvalid && !axi.awready |=> axi.awvalid)
        else report_error("AWVALID deasserted before AWREADY");
        
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.awvalid && !axi.awready |=> $stable(axi.awaddr))
        else report_error("AWADDR changed while waiting for AWREADY");
        
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.awvalid |-> !axi4_crosses_4kb(axi.awaddr, axi.awlen + 1, axi.awsize))
        else report_error("Write burst crosses 4KB boundary");
        
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            (axi.awvalid && axi.awburst == AXI4_BURST_WRAP) |->
            (axi.awlen == 1 || axi.awlen == 3 || axi.awlen == 7 || axi.awlen == 15))
        else report_error("Invalid WRAP burst length");
        
        // W channel assertions
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.wvalid && !axi.wready |=> axi.wvalid)
        else report_error("WVALID deasserted before WREADY");
        
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.wvalid && !axi.wready |=> $stable(axi.wdata))
        else report_error("WDATA changed while waiting for WREADY");
        
        // B channel assertions
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.bvalid && !axi.bready |=> axi.bvalid)
        else report_error("BVALID deasserted before BREADY");
        
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.bvalid && !axi.bready |=> $stable(axi.bid))
        else report_error("BID changed while waiting for BREADY");
        
        // AR channel assertions
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.arvalid && !axi.arready |=> axi.arvalid)
        else report_error("ARVALID deasserted before ARREADY");
        
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.arvalid && !axi.arready |=> $stable(axi.araddr))
        else report_error("ARADDR changed while waiting for ARREADY");
        
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.arvalid |-> !axi4_crosses_4kb(axi.araddr, axi.arlen + 1, axi.arsize))
        else report_error("Read burst crosses 4KB boundary");
        
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            (axi.arvalid && axi.arburst == AXI4_BURST_WRAP) |->
            (axi.arlen == 1 || axi.arlen == 3 || axi.arlen == 7 || axi.arlen == 15))
        else report_error("Invalid WRAP burst length");
        
        // R channel assertions
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.rvalid && !axi.rready |=> axi.rvalid)
        else report_error("RVALID deasserted before RREADY");
        
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            axi.rvalid && !axi.rready |=> $stable(axi.rid))
        else report_error("RID changed while waiting for RREADY");
        
        // Exclusive access assertions
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            (axi.awvalid && axi.awlock == AXI4_LOCK_EXCLUSIVE) |->
            ((axi.awlen + 1) * (1 << axi.awsize) <= `AXI4_EXCLUSIVE_MAX_BYTES))
        else report_error("Exclusive write exceeds maximum size");
        
        assert property (@(posedge axi.aclk) disable iff (!axi.aresetn)
            (axi.arvalid && axi.arlock == AXI4_LOCK_EXCLUSIVE) |->
            ((axi.arlen + 1) * (1 << axi.arsize) <= `AXI4_EXCLUSIVE_MAX_BYTES))
        else report_error("Exclusive read exceeds maximum size");
        
    end endgenerate
    
    // Coverage Collection
    generate if (ENABLE_COVERAGE) begin : coverage
        
        covergroup axi_transaction_cg @(posedge axi.aclk);
            // Write address coverage
            aw_burst: coverpoint axi.awburst iff (axi.awvalid && axi.awready) {
                bins fixed = {AXI4_BURST_FIXED};
                bins incr  = {AXI4_BURST_INCR};
                bins wrap  = {AXI4_BURST_WRAP};
            }
            
            aw_size: coverpoint axi.awsize iff (axi.awvalid && axi.awready) {
                bins sizes[] = {[0:$clog2(CFG.DATA_WIDTH/8)]};
            }
            
            aw_len: coverpoint axi.awlen iff (axi.awvalid && axi.awready) {
                bins single = {0};
                bins short_burst = {[1:15]};
                bins long_burst = {[16:255]};
            }
            
            aw_lock: coverpoint axi.awlock iff (axi.awvalid && axi.awready) {
                bins normal = {AXI4_LOCK_NORMAL};
                bins exclusive = {AXI4_LOCK_EXCLUSIVE};
            }
            
            // Read address coverage
            ar_burst: coverpoint axi.arburst iff (axi.arvalid && axi.arready) {
                bins fixed = {AXI4_BURST_FIXED};
                bins incr  = {AXI4_BURST_INCR};
                bins wrap  = {AXI4_BURST_WRAP};
            }
            
            ar_size: coverpoint axi.arsize iff (axi.arvalid && axi.arready) {
                bins sizes[] = {[0:$clog2(CFG.DATA_WIDTH/8)]};
            }
            
            ar_len: coverpoint axi.arlen iff (axi.arvalid && axi.arready) {
                bins single = {0};
                bins short_burst = {[1:15]};
                bins long_burst = {[16:255]};
            }
            
            // Response coverage
            bresp: coverpoint axi.bresp iff (axi.bvalid && axi.bready) {
                bins okay   = {AXI4_RESP_OKAY};
                bins exokay = {AXI4_RESP_EXOKAY};
                bins slverr = {AXI4_RESP_SLVERR};
                bins decerr = {AXI4_RESP_DECERR};
            }
            
            rresp: coverpoint axi.rresp iff (axi.rvalid && axi.rready) {
                bins okay   = {AXI4_RESP_OKAY};
                bins exokay = {AXI4_RESP_EXOKAY};
                bins slverr = {AXI4_RESP_SLVERR};
                bins decerr = {AXI4_RESP_DECERR};
            }
            
            // Cross coverage
            write_burst_x_size: cross aw_burst, aw_size;
            read_burst_x_size: cross ar_burst, ar_size;
            
        endgroup
        
        axi_transaction_cg axi_cov = new();
        
    end endgenerate
    
endmodule : axi4_monitor_checker