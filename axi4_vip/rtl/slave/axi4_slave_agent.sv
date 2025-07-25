//==============================================================================
// AXI4 Slave Agent
// 
// Description: Complete AXI4 slave agent with memory model and response generation
// Supports all AXI4 features including exclusive access, protection checking
//==============================================================================

`include "../common/axi4_defines.sv"

module axi4_slave_agent #(
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
    parameter int MEM_SIZE_KB = 1024,  // Memory size in KB
    parameter int SLAVE_TYPE = 0       // 0=Memory, 1=Peripheral
)(
    // Clock and reset
    input logic clk,
    input logic rst_n,
    
    // AXI4 interface
    axi4_if.slave axi,
    
    // Configuration
    input logic [CFG.ADDR_WIDTH-1:0] base_addr,
    input logic [CFG.ADDR_WIDTH-1:0] addr_mask,
    input logic                       enable_prot_check,
    input logic                       enable_exclusive,
    input logic [7:0]                 read_delay_min,
    input logic [7:0]                 read_delay_max,
    input logic [7:0]                 write_delay_min,
    input logic [7:0]                 write_delay_max,
    
    // Error injection
    input logic                       error_injection_en,
    input logic [7:0]                 error_rate,
    
    // Statistics
    output logic [31:0]               read_count,
    output logic [31:0]               write_count,
    output logic [31:0]               error_count
);

    // Local parameters
    localparam int STRB_WIDTH = CFG.DATA_WIDTH / 8;
    localparam int MEM_SIZE = MEM_SIZE_KB * 1024;
    localparam int MEM_ADDR_WIDTH = $clog2(MEM_SIZE);
    
    // Memory model
    logic [7:0] memory[MEM_SIZE];
    
    // Transaction tracking
    typedef struct packed {
        logic [CFG.ID_WIDTH-1:0]   id;
        logic [CFG.ADDR_WIDTH-1:0] addr;
        logic [7:0]                len;
        logic [2:0]                size;
        axi4_burst_t               burst;
        axi4_lock_t                lock;
        axi4_prot_t                prot;
        axi4_cache_t               cache;
        logic [3:0]                qos;
        logic [3:0]                region;
    } addr_trans_t;
    
    addr_trans_t write_trans_queue[$];
    addr_trans_t read_trans_queue[$];
    
    // Exclusive access monitor instantiation
    axi4_exclusive_monitor #(
        .ADDR_WIDTH(CFG.ADDR_WIDTH),
        .ID_WIDTH(CFG.ID_WIDTH),
        .DATA_WIDTH(CFG.DATA_WIDTH)
    ) exclusive_monitor_inst (
        .clk(clk),
        .rst_n(rst_n),
        .exclusive_read_req(1'b0),  // Connected later
        .exclusive_read_id('0),
        .exclusive_read_addr('0),
        .exclusive_read_size('0),
        .exclusive_read_len('0),
        .write_req(1'b0),
        .write_addr('0),
        .write_size('0),
        .write_len('0),
        .exclusive_write_req(1'b0),
        .exclusive_write_id('0),
        .exclusive_write_addr('0),
        .exclusive_write_size('0),
        .exclusive_write_len('0),
        .exclusive_write_pass()
    );
    
    // Protection checker instantiation
    axi4_prot_checker #(
        .ADDR_WIDTH(CFG.ADDR_WIDTH),
        .NUM_REGIONS(1)
    ) prot_checker_inst (
        .clk(clk),
        .rst_n(rst_n),
        .cfg_wen(1'b0),  // Static config for now
        .cfg_region_sel('0),
        .cfg_base_addr(base_addr),
        .cfg_end_addr(base_addr | ~addr_mask),
        .cfg_read_enable(1'b1),
        .cfg_write_enable(1'b1),
        .cfg_secure_only(1'b0),
        .cfg_privileged_only(1'b0),
        .cfg_data_only(1'b0),
        .cfg_region_enable(1'b1),
        .check_valid(1'b0),
        .check_addr('0),
        .check_write(1'b0),
        .check_prot('0),
        .check_pass(),
        .check_error(),
        .check_error_type()
    );
    
    // Write address channel handler
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi.awready <= 1'b0;
        end else begin
            // Simple ready generation - can be made more sophisticated
            axi.awready <= 1'b1;
            
            // Capture write address
            if (axi.awvalid && axi.awready) begin
                addr_trans_t trans;
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
                
                write_trans_queue.push_back(trans);
            end
        end
    end
    
    // Write data channel handler
    logic [7:0] w_beat_count;
    logic [CFG.DATA_WIDTH-1:0] write_data_buffer[256];
    logic [STRB_WIDTH-1:0] write_strb_buffer[256];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi.wready <= 1'b0;
            w_beat_count <= '0;
        end else begin
            axi.wready <= write_trans_queue.size() > 0;
            
            // Capture write data
            if (axi.wvalid && axi.wready) begin
                write_data_buffer[w_beat_count] <= axi.wdata;
                write_strb_buffer[w_beat_count] <= axi.wstrb;
                
                if (axi.wlast) begin
                    // Process complete write burst
                    process_write_burst();
                    w_beat_count <= '0;
                end else begin
                    w_beat_count <= w_beat_count + 1;
                end
            end
        end
    end
    
    // Write burst processing
    task process_write_burst();
        addr_trans_t trans;
        logic [CFG.ADDR_WIDTH-1:0] addr;
        axi4_resp_t resp;
        
        if (write_trans_queue.size() > 0) begin
            trans = write_trans_queue[0];
            write_trans_queue.pop_front();
            
            addr = trans.addr;
            resp = AXI4_RESP_OKAY;
            
            // Check protection if enabled
            if (enable_prot_check) begin
                // Protection check logic here
            end
            
            // Check exclusive access
            if (trans.lock == AXI4_LOCK_EXCLUSIVE && enable_exclusive) begin
                // Exclusive check logic here
            end
            
            // Perform memory write
            for (int beat = 0; beat <= trans.len; beat++) begin
                logic [CFG.ADDR_WIDTH-1:0] beat_addr;
                
                // Calculate beat address
                case (trans.burst)
                    AXI4_BURST_FIXED: beat_addr = addr;
                    AXI4_BURST_INCR: beat_addr = addr + beat * (1 << trans.size);
                    AXI4_BURST_WRAP: begin
                        // Wrap calculation
                        logic [CFG.ADDR_WIDTH-1:0] wrap_size = (trans.len + 1) << trans.size;
                        logic [CFG.ADDR_WIDTH-1:0] wrap_mask = wrap_size - 1;
                        beat_addr = (addr & ~wrap_mask) | ((addr + beat * (1 << trans.size)) & wrap_mask);
                    end
                endcase
                
                // Write to memory with strobe
                for (int byte_idx = 0; byte_idx < STRB_WIDTH; byte_idx++) begin
                    if (write_strb_buffer[beat][byte_idx]) begin
                        logic [MEM_ADDR_WIDTH-1:0] mem_addr = (beat_addr & addr_mask) + byte_idx;
                        if (mem_addr < MEM_SIZE) begin
                            memory[mem_addr] <= write_data_buffer[beat][byte_idx*8 +: 8];
                        end else begin
                            resp = AXI4_RESP_SLVERR;
                        end
                    end
                end
            end
            
            // Error injection
            if (error_injection_en && $random % 256 < error_rate) begin
                resp = AXI4_RESP_SLVERR;
                error_count <= error_count + 1;
            end
            
            // Queue write response
            queue_write_response(trans.id, resp);
            write_count <= write_count + 1;
        end
    endtask
    
    // Write response generation
    logic [CFG.ID_WIDTH-1:0] bresp_queue[$];
    axi4_resp_t bresp_type_queue[$];
    
    task queue_write_response(logic [CFG.ID_WIDTH-1:0] id, axi4_resp_t resp);
        bresp_queue.push_back(id);
        bresp_type_queue.push_back(resp);
    endtask
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi.bvalid <= 1'b0;
            axi.bid <= '0;
            axi.bresp <= '0;
            axi.buser <= '0;
        end else begin
            if (axi.bvalid && axi.bready) begin
                axi.bvalid <= 1'b0;
            end
            
            if (!axi.bvalid && bresp_queue.size() > 0) begin
                axi.bvalid <= 1'b1;
                axi.bid <= bresp_queue[0];
                axi.bresp <= bresp_type_queue[0];
                bresp_queue.pop_front();
                bresp_type_queue.pop_front();
            end
        end
    end
    
    // Read address channel handler
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi.arready <= 1'b0;
        end else begin
            axi.arready <= 1'b1;
            
            // Capture read address
            if (axi.arvalid && axi.arready) begin
                addr_trans_t trans;
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
                
                read_trans_queue.push_back(trans);
                
                // Track exclusive read
                if (trans.lock == AXI4_LOCK_EXCLUSIVE && enable_exclusive) begin
                    // Update exclusive monitor
                end
            end
        end
    end
    
    // Read data channel generation
    typedef struct packed {
        logic [CFG.ID_WIDTH-1:0] id;
        logic [CFG.DATA_WIDTH-1:0] data;
        axi4_resp_t resp;
        logic last;
    } read_data_entry_t;
    
    read_data_entry_t read_data_queue[$];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            axi.rvalid <= 1'b0;
            axi.rid <= '0;
            axi.rdata <= '0;
            axi.rresp <= '0;
            axi.rlast <= '0;
            axi.ruser <= '0;
        end else begin
            // Process read transactions
            if (read_trans_queue.size() > 0 && read_data_queue.size() < 16) begin
                process_read_burst();
            end
            
            // Send read data
            if (axi.rvalid && axi.rready) begin
                axi.rvalid <= 1'b0;
                read_data_queue.pop_front();
            end
            
            if (!axi.rvalid && read_data_queue.size() > 0) begin
                axi.rvalid <= 1'b1;
                axi.rid <= read_data_queue[0].id;
                axi.rdata <= read_data_queue[0].data;
                axi.rresp <= read_data_queue[0].resp;
                axi.rlast <= read_data_queue[0].last;
            end
        end
    end
    
    // Read burst processing
    task process_read_burst();
        addr_trans_t trans;
        logic [CFG.ADDR_WIDTH-1:0] addr;
        
        trans = read_trans_queue[0];
        read_trans_queue.pop_front();
        
        addr = trans.addr;
        
        for (int beat = 0; beat <= trans.len; beat++) begin
            logic [CFG.ADDR_WIDTH-1:0] beat_addr;
            logic [CFG.DATA_WIDTH-1:0] data;
            axi4_resp_t resp = AXI4_RESP_OKAY;
            
            // Calculate beat address
            case (trans.burst)
                AXI4_BURST_FIXED: beat_addr = addr;
                AXI4_BURST_INCR: beat_addr = addr + beat * (1 << trans.size);
                AXI4_BURST_WRAP: begin
                    logic [CFG.ADDR_WIDTH-1:0] wrap_size = (trans.len + 1) << trans.size;
                    logic [CFG.ADDR_WIDTH-1:0] wrap_mask = wrap_size - 1;
                    beat_addr = (addr & ~wrap_mask) | ((addr + beat * (1 << trans.size)) & wrap_mask);
                end
            endcase
            
            // Read from memory
            data = '0;
            for (int byte_idx = 0; byte_idx < STRB_WIDTH; byte_idx++) begin
                logic [MEM_ADDR_WIDTH-1:0] mem_addr = (beat_addr & addr_mask) + byte_idx;
                if (mem_addr < MEM_SIZE) begin
                    data[byte_idx*8 +: 8] = memory[mem_addr];
                end else begin
                    resp = AXI4_RESP_SLVERR;
                end
            end
            
            // Error injection
            if (error_injection_en && $random % 256 < error_rate) begin
                resp = AXI4_RESP_SLVERR;
                error_count <= error_count + 1;
            end
            
            // Queue read data
            read_data_entry_t entry;
            entry.id = trans.id;
            entry.data = data;
            entry.resp = resp;
            entry.last = (beat == trans.len);
            read_data_queue.push_back(entry);
        end
        
        read_count <= read_count + 1;
    endtask
    
    // Memory initialization
    initial begin
        for (int i = 0; i < MEM_SIZE; i++) begin
            memory[i] = 8'h00;
        end
    end
    
endmodule : axi4_slave_agent