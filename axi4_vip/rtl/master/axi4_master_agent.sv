//==============================================================================
// AXI4 Master Agent
// 
// Description: Complete AXI4 master agent with driver, sequencer interface
// Supports all AXI4 features including exclusive access, QoS, regions, etc.
//==============================================================================

`include "../common/axi4_defines.sv"

module axi4_master_agent #(
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
    }
)(
    // Clock and reset
    input logic clk,
    input logic rst_n,
    
    // AXI4 interface
    axi4_if.master axi,
    
    // Transaction interface
    input logic                    req_valid,
    output logic                   req_ready,
    input axi4_transaction_t       req_trans,
    
    output logic                   resp_valid,
    input logic                    resp_ready,
    output axi4_transaction_t      resp_trans,
    
    // Configuration
    input logic [31:0]             max_outstanding_writes,
    input logic [31:0]             max_outstanding_reads,
    input logic                    enable_resp_reordering,
    input logic [7:0]              aw_delay_min,
    input logic [7:0]              aw_delay_max,
    input logic [7:0]              w_delay_min,
    input logic [7:0]              w_delay_max,
    input logic [7:0]              ar_delay_min,
    input logic [7:0]              ar_delay_max
);

    // Local parameters
    localparam int STRB_WIDTH = CFG.DATA_WIDTH / 8;
    
    // Internal FIFOs for transaction management
    axi4_transaction_t write_addr_fifo[$];
    axi4_transaction_t write_data_fifo[$];
    axi4_transaction_t write_resp_fifo[$];
    axi4_transaction_t read_addr_fifo[$];
    axi4_transaction_t read_data_fifo[$];
    
    // Outstanding transaction tracking
    int outstanding_writes;
    int outstanding_reads;
    
    // Delay counters
    logic [7:0] aw_delay_cnt;
    logic [7:0] w_delay_cnt;
    logic [7:0] ar_delay_cnt;
    logic       aw_delay_active;
    logic       w_delay_active;
    logic       ar_delay_active;
    
    // Transaction acceptance
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            req_ready <= 1'b0;
        end else begin
            req_ready <= 1'b1;  // Always ready for now
        end
    end
    
    // Transaction queueing
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            write_addr_fifo.delete();
            write_data_fifo.delete();
            read_addr_fifo.delete();
        end else begin
            if (req_valid && req_ready) begin
                if (req_trans.is_write) begin
                    write_addr_fifo.push_back(req_trans);
                    write_data_fifo.push_back(req_trans);
                end else begin
                    read_addr_fifo.push_back(req_trans);
                end
            end
        end
    end
    
    // Write address channel driver
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi.awvalid <= 1'b0;
            axi.awid <= '0;
            axi.awaddr <= '0;
            axi.awlen <= '0;
            axi.awsize <= '0;
            axi.awburst <= '0;
            axi.awlock <= '0;
            axi.awcache <= '0;
            axi.awprot <= '0;
            axi.awqos <= '0;
            axi.awregion <= '0;
            axi.awuser <= '0;
            aw_delay_active <= 1'b0;
            aw_delay_cnt <= '0;
        end else begin
            // Clear valid on handshake
            if (axi.awvalid && axi.awready) begin
                axi.awvalid <= 1'b0;
                outstanding_writes <= outstanding_writes + 1;
            end
            
            // Handle delay
            if (aw_delay_active) begin
                if (aw_delay_cnt > 0) begin
                    aw_delay_cnt <= aw_delay_cnt - 1;
                end else begin
                    aw_delay_active <= 1'b0;
                end
            end
            
            // Drive new transaction
            if (!axi.awvalid && !aw_delay_active && 
                write_addr_fifo.size() > 0 &&
                outstanding_writes < max_outstanding_writes) begin
                
                axi4_transaction_t trans = write_addr_fifo[0];
                
                // Apply random delay
                logic [7:0] delay = $urandom_range(aw_delay_max, aw_delay_min);
                if (delay > 0) begin
                    aw_delay_active <= 1'b1;
                    aw_delay_cnt <= delay - 1;
                end else begin
                    axi.awvalid <= 1'b1;
                    axi.awid <= trans.id[CFG.ID_WIDTH-1:0];
                    axi.awaddr <= trans.addr[CFG.ADDR_WIDTH-1:0];
                    axi.awlen <= trans.len;
                    axi.awsize <= trans.size;
                    axi.awburst <= trans.burst;
                    axi.awlock <= trans.lock;
                    axi.awcache <= {trans.cache.allocate, trans.cache.other_alloc,
                                   trans.cache.modifiable, trans.cache.bufferable};
                    axi.awprot <= {trans.prot.instruction, trans.prot.nonsecure,
                                  trans.prot.privileged};
                    if (CFG.SUPPORT_QOS) axi.awqos <= trans.qos;
                    if (CFG.SUPPORT_REGION) axi.awregion <= trans.region;
                    if (CFG.SUPPORT_USER_SIGNALS && CFG.AWUSER_WIDTH > 0)
                        axi.awuser <= trans.awuser[CFG.AWUSER_WIDTH-1:0];
                    
                    write_addr_fifo.pop_front();
                end
            end
        end
    end
    
    // Write data channel driver
    logic [7:0] w_beat_count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi.wvalid <= 1'b0;
            axi.wdata <= '0;
            axi.wstrb <= '0;
            axi.wlast <= '0;
            axi.wuser <= '0;
            w_delay_active <= 1'b0;
            w_delay_cnt <= '0;
            w_beat_count <= '0;
        end else begin
            // Clear valid on handshake
            if (axi.wvalid && axi.wready) begin
                axi.wvalid <= 1'b0;
                
                if (axi.wlast) begin
                    w_beat_count <= '0;
                    write_data_fifo.pop_front();
                end else begin
                    w_beat_count <= w_beat_count + 1;
                end
            end
            
            // Handle delay
            if (w_delay_active) begin
                if (w_delay_cnt > 0) begin
                    w_delay_cnt <= w_delay_cnt - 1;
                end else begin
                    w_delay_active <= 1'b0;
                end
            end
            
            // Drive new data beat
            if (!axi.wvalid && !w_delay_active && write_data_fifo.size() > 0) begin
                axi4_transaction_t trans = write_data_fifo[0];
                
                // Apply random delay
                logic [7:0] delay = $urandom_range(w_delay_max, w_delay_min);
                if (delay > 0) begin
                    w_delay_active <= 1'b1;
                    w_delay_cnt <= delay - 1;
                end else begin
                    axi.wvalid <= 1'b1;
                    axi.wdata <= trans.data[w_beat_count][CFG.DATA_WIDTH-1:0];
                    axi.wstrb <= trans.strb[w_beat_count][STRB_WIDTH-1:0];
                    axi.wlast <= (w_beat_count == trans.len);
                    if (CFG.SUPPORT_USER_SIGNALS && CFG.WUSER_WIDTH > 0)
                        axi.wuser <= trans.wuser[w_beat_count][CFG.WUSER_WIDTH-1:0];
                end
            end
        end
    end
    
    // Write response channel handler
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi.bready <= 1'b0;
            write_resp_fifo.delete();
        end else begin
            // Always ready to accept responses
            axi.bready <= 1'b1;
            
            // Capture response
            if (axi.bvalid && axi.bready) begin
                axi4_transaction_t resp;
                resp.id = axi.bid;
                resp.resp[0] = axi4_resp_t'(axi.bresp);
                resp.is_write = 1'b1;
                if (CFG.SUPPORT_USER_SIGNALS && CFG.BUSER_WIDTH > 0)
                    resp.buser = axi.buser;
                
                write_resp_fifo.push_back(resp);
                outstanding_writes <= outstanding_writes - 1;
            end
        end
    end
    
    // Read address channel driver
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi.arvalid <= 1'b0;
            axi.arid <= '0;
            axi.araddr <= '0;
            axi.arlen <= '0;
            axi.arsize <= '0;
            axi.arburst <= '0;
            axi.arlock <= '0;
            axi.arcache <= '0;
            axi.arprot <= '0;
            axi.arqos <= '0;
            axi.arregion <= '0;
            axi.aruser <= '0;
            ar_delay_active <= 1'b0;
            ar_delay_cnt <= '0;
        end else begin
            // Clear valid on handshake
            if (axi.arvalid && axi.arready) begin
                axi.arvalid <= 1'b0;
                outstanding_reads <= outstanding_reads + 1;
            end
            
            // Handle delay
            if (ar_delay_active) begin
                if (ar_delay_cnt > 0) begin
                    ar_delay_cnt <= ar_delay_cnt - 1;
                end else begin
                    ar_delay_active <= 1'b0;
                end
            end
            
            // Drive new transaction
            if (!axi.arvalid && !ar_delay_active && 
                read_addr_fifo.size() > 0 &&
                outstanding_reads < max_outstanding_reads) begin
                
                axi4_transaction_t trans = read_addr_fifo[0];
                
                // Apply random delay
                logic [7:0] delay = $urandom_range(ar_delay_max, ar_delay_min);
                if (delay > 0) begin
                    ar_delay_active <= 1'b1;
                    ar_delay_cnt <= delay - 1;
                end else begin
                    axi.arvalid <= 1'b1;
                    axi.arid <= trans.id[CFG.ID_WIDTH-1:0];
                    axi.araddr <= trans.addr[CFG.ADDR_WIDTH-1:0];
                    axi.arlen <= trans.len;
                    axi.arsize <= trans.size;
                    axi.arburst <= trans.burst;
                    axi.arlock <= trans.lock;
                    axi.arcache <= {trans.cache.allocate, trans.cache.other_alloc,
                                   trans.cache.modifiable, trans.cache.bufferable};
                    axi.arprot <= {trans.prot.instruction, trans.prot.nonsecure,
                                  trans.prot.privileged};
                    if (CFG.SUPPORT_QOS) axi.arqos <= trans.qos;
                    if (CFG.SUPPORT_REGION) axi.arregion <= trans.region;
                    if (CFG.SUPPORT_USER_SIGNALS && CFG.ARUSER_WIDTH > 0)
                        axi.aruser <= trans.aruser[CFG.ARUSER_WIDTH-1:0];
                    
                    read_addr_fifo.pop_front();
                end
            end
        end
    end
    
    // Read data channel handler
    logic [7:0] r_beat_count[2**CFG.ID_WIDTH];
    axi4_transaction_t read_resp_buffer[2**CFG.ID_WIDTH];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi.rready <= 1'b0;
            read_data_fifo.delete();
            for (int i = 0; i < 2**CFG.ID_WIDTH; i++) begin
                r_beat_count[i] <= '0;
            end
        end else begin
            // Always ready to accept data
            axi.rready <= 1'b1;
            
            // Capture read data
            if (axi.rvalid && axi.rready) begin
                int id_idx = axi.rid;
                
                // First beat - initialize response
                if (r_beat_count[id_idx] == 0) begin
                    read_resp_buffer[id_idx].id = axi.rid;
                    read_resp_buffer[id_idx].is_write = 1'b0;
                end
                
                // Store data and response
                read_resp_buffer[id_idx].data[r_beat_count[id_idx]] = axi.rdata;
                read_resp_buffer[id_idx].resp[r_beat_count[id_idx]] = axi4_resp_t'(axi.rresp);
                if (CFG.SUPPORT_USER_SIGNALS && CFG.RUSER_WIDTH > 0)
                    read_resp_buffer[id_idx].ruser[r_beat_count[id_idx]] = axi.ruser;
                
                if (axi.rlast) begin
                    read_data_fifo.push_back(read_resp_buffer[id_idx]);
                    r_beat_count[id_idx] <= '0;
                    outstanding_reads <= outstanding_reads - 1;
                end else begin
                    r_beat_count[id_idx] <= r_beat_count[id_idx] + 1;
                end
            end
        end
    end
    
    // Response output
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            resp_valid <= 1'b0;
            resp_trans <= '0;
        end else begin
            if (resp_valid && resp_ready) begin
                resp_valid <= 1'b0;
            end
            
            if (!resp_valid) begin
                if (write_resp_fifo.size() > 0) begin
                    resp_valid <= 1'b1;
                    resp_trans <= write_resp_fifo[0];
                    write_resp_fifo.pop_front();
                end else if (read_data_fifo.size() > 0) begin
                    resp_valid <= 1'b1;
                    resp_trans <= read_data_fifo[0];
                    read_data_fifo.pop_front();
                end
            end
        end
    end
    
endmodule : axi4_master_agent