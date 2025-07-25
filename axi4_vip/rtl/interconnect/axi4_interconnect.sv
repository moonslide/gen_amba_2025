//==============================================================================
// AXI4 Interconnect Model
// 
// Description: N-to-M AXI4 interconnect with configurable routing and arbitration
// Supports all AXI4 features with QoS-based arbitration
//==============================================================================

`include "../common/axi4_defines.sv"

module axi4_interconnect #(
    parameter int NUM_MASTERS = 2,
    parameter int NUM_SLAVES = 3,
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
    parameter int INTERCONNECT_ID_WIDTH = CFG.ID_WIDTH + $clog2(NUM_MASTERS)
)(
    input logic clk,
    input logic rst_n,
    
    // Master interfaces
    axi4_if.slave master_if[NUM_MASTERS],
    
    // Slave interfaces  
    axi4_if.master slave_if[NUM_SLAVES],
    
    // Address mapping configuration
    input logic [CFG.ADDR_WIDTH-1:0] slave_base_addr[NUM_SLAVES],
    input logic [CFG.ADDR_WIDTH-1:0] slave_addr_mask[NUM_SLAVES],
    
    // Arbitration configuration
    input logic [1:0] arb_mode,  // 0=Fixed, 1=RR, 2=QoS, 3=WRR
    input logic [3:0] master_weight[NUM_MASTERS]
);

    // Local parameters
    localparam int MASTER_ID_WIDTH = $clog2(NUM_MASTERS);
    
    // Internal interfaces for arbitration
    axi4_if #(
        .ADDR_WIDTH(CFG.ADDR_WIDTH),
        .DATA_WIDTH(CFG.DATA_WIDTH),
        .ID_WIDTH(INTERCONNECT_ID_WIDTH),
        .AWUSER_WIDTH(CFG.AWUSER_WIDTH),
        .WUSER_WIDTH(CFG.WUSER_WIDTH),
        .BUSER_WIDTH(CFG.BUSER_WIDTH),
        .ARUSER_WIDTH(CFG.ARUSER_WIDTH),
        .RUSER_WIDTH(CFG.RUSER_WIDTH)
    ) arb_write_if(clk, rst_n);
    
    axi4_if #(
        .ADDR_WIDTH(CFG.ADDR_WIDTH),
        .DATA_WIDTH(CFG.DATA_WIDTH),
        .ID_WIDTH(INTERCONNECT_ID_WIDTH),
        .AWUSER_WIDTH(CFG.AWUSER_WIDTH),
        .WUSER_WIDTH(CFG.WUSER_WIDTH),
        .BUSER_WIDTH(CFG.BUSER_WIDTH),
        .ARUSER_WIDTH(CFG.ARUSER_WIDTH),
        .RUSER_WIDTH(CFG.RUSER_WIDTH)
    ) arb_read_if(clk, rst_n);
    
    // Write address channel arbitration
    logic [NUM_MASTERS-1:0] aw_req_valid;
    logic [3:0] aw_req_qos[NUM_MASTERS];
    logic [CFG.ID_WIDTH-1:0] aw_req_id[NUM_MASTERS];
    logic [CFG.ADDR_WIDTH-1:0] aw_req_addr[NUM_MASTERS];
    logic [NUM_MASTERS-1:0] aw_req_ready;
    logic aw_grant_valid;
    logic [MASTER_ID_WIDTH-1:0] aw_grant_master;
    
    // Collect write address requests
    always_comb begin
        for (int m = 0; m < NUM_MASTERS; m++) begin
            aw_req_valid[m] = master_if[m].awvalid;
            aw_req_qos[m] = master_if[m].awqos;
            aw_req_id[m] = master_if[m].awid;
            aw_req_addr[m] = master_if[m].awaddr;
            master_if[m].awready = aw_req_ready[m];
        end
    end
    
    // Write address arbiter
    axi4_qos_arbiter #(
        .NUM_MASTERS(NUM_MASTERS),
        .ID_WIDTH(CFG.ID_WIDTH),
        .ADDR_WIDTH(CFG.ADDR_WIDTH)
    ) write_addr_arbiter (
        .clk(clk),
        .rst_n(rst_n),
        .arb_mode(arb_mode),
        .weight(master_weight),
        .req_valid(aw_req_valid),
        .req_qos(aw_req_qos),
        .req_id(aw_req_id),
        .req_addr(aw_req_addr),
        .req_ready(aw_req_ready),
        .grant_valid(aw_grant_valid),
        .grant_master(aw_grant_master),
        .grant_ready(arb_write_if.awready),
        .grant_count(),
        .wait_cycles()
    );
    
    // Write address mux
    always_comb begin
        arb_write_if.awvalid = aw_grant_valid;
        if (aw_grant_valid) begin
            int m = aw_grant_master;
            arb_write_if.awid = {aw_grant_master, master_if[m].awid};
            arb_write_if.awaddr = master_if[m].awaddr;
            arb_write_if.awlen = master_if[m].awlen;
            arb_write_if.awsize = master_if[m].awsize;
            arb_write_if.awburst = master_if[m].awburst;
            arb_write_if.awlock = master_if[m].awlock;
            arb_write_if.awcache = master_if[m].awcache;
            arb_write_if.awprot = master_if[m].awprot;
            arb_write_if.awqos = master_if[m].awqos;
            arb_write_if.awregion = master_if[m].awregion;
            if (CFG.SUPPORT_USER_SIGNALS && CFG.AWUSER_WIDTH > 0)
                arb_write_if.awuser = master_if[m].awuser;
        end else begin
            arb_write_if.awid = '0;
            arb_write_if.awaddr = '0;
            arb_write_if.awlen = '0;
            arb_write_if.awsize = '0;
            arb_write_if.awburst = '0;
            arb_write_if.awlock = '0;
            arb_write_if.awcache = '0;
            arb_write_if.awprot = '0;
            arb_write_if.awqos = '0;
            arb_write_if.awregion = '0;
            arb_write_if.awuser = '0;
        end
    end
    
    // Write data channel routing
    logic [MASTER_ID_WIDTH-1:0] w_active_master;
    logic w_channel_busy;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            w_active_master <= '0;
            w_channel_busy <= 1'b0;
        end else begin
            if (arb_write_if.awvalid && arb_write_if.awready) begin
                w_active_master <= arb_write_if.awid[INTERCONNECT_ID_WIDTH-1:CFG.ID_WIDTH];
                w_channel_busy <= 1'b1;
            end else if (arb_write_if.wvalid && arb_write_if.wready && arb_write_if.wlast) begin
                w_channel_busy <= 1'b0;
            end
        end
    end
    
    // Write data mux
    always_comb begin
        arb_write_if.wvalid = 1'b0;
        arb_write_if.wdata = '0;
        arb_write_if.wstrb = '0;
        arb_write_if.wlast = 1'b0;
        arb_write_if.wuser = '0;
        
        for (int m = 0; m < NUM_MASTERS; m++) begin
            master_if[m].wready = 1'b0;
        end
        
        if (w_channel_busy) begin
            int m = w_active_master;
            arb_write_if.wvalid = master_if[m].wvalid;
            arb_write_if.wdata = master_if[m].wdata;
            arb_write_if.wstrb = master_if[m].wstrb;
            arb_write_if.wlast = master_if[m].wlast;
            if (CFG.SUPPORT_USER_SIGNALS && CFG.WUSER_WIDTH > 0)
                arb_write_if.wuser = master_if[m].wuser;
            master_if[m].wready = arb_write_if.wready;
        end
    end
    
    // Read address channel arbitration
    logic [NUM_MASTERS-1:0] ar_req_valid;
    logic [3:0] ar_req_qos[NUM_MASTERS];
    logic [CFG.ID_WIDTH-1:0] ar_req_id[NUM_MASTERS];
    logic [CFG.ADDR_WIDTH-1:0] ar_req_addr[NUM_MASTERS];
    logic [NUM_MASTERS-1:0] ar_req_ready;
    logic ar_grant_valid;
    logic [MASTER_ID_WIDTH-1:0] ar_grant_master;
    
    // Collect read address requests
    always_comb begin
        for (int m = 0; m < NUM_MASTERS; m++) begin
            ar_req_valid[m] = master_if[m].arvalid;
            ar_req_qos[m] = master_if[m].arqos;
            ar_req_id[m] = master_if[m].arid;
            ar_req_addr[m] = master_if[m].araddr;
            master_if[m].arready = ar_req_ready[m];
        end
    end
    
    // Read address arbiter
    axi4_qos_arbiter #(
        .NUM_MASTERS(NUM_MASTERS),
        .ID_WIDTH(CFG.ID_WIDTH),
        .ADDR_WIDTH(CFG.ADDR_WIDTH)
    ) read_addr_arbiter (
        .clk(clk),
        .rst_n(rst_n),
        .arb_mode(arb_mode),
        .weight(master_weight),
        .req_valid(ar_req_valid),
        .req_qos(ar_req_qos),
        .req_id(ar_req_id),
        .req_addr(ar_req_addr),
        .req_ready(ar_req_ready),
        .grant_valid(ar_grant_valid),
        .grant_master(ar_grant_master),
        .grant_ready(arb_read_if.arready),
        .grant_count(),
        .wait_cycles()
    );
    
    // Read address mux
    always_comb begin
        arb_read_if.arvalid = ar_grant_valid;
        if (ar_grant_valid) begin
            int m = ar_grant_master;
            arb_read_if.arid = {ar_grant_master, master_if[m].arid};
            arb_read_if.araddr = master_if[m].araddr;
            arb_read_if.arlen = master_if[m].arlen;
            arb_read_if.arsize = master_if[m].arsize;
            arb_read_if.arburst = master_if[m].arburst;
            arb_read_if.arlock = master_if[m].arlock;
            arb_read_if.arcache = master_if[m].arcache;
            arb_read_if.arprot = master_if[m].arprot;
            arb_read_if.arqos = master_if[m].arqos;
            arb_read_if.arregion = master_if[m].arregion;
            if (CFG.SUPPORT_USER_SIGNALS && CFG.ARUSER_WIDTH > 0)
                arb_read_if.aruser = master_if[m].aruser;
        end else begin
            arb_read_if.arid = '0;
            arb_read_if.araddr = '0;
            arb_read_if.arlen = '0;
            arb_read_if.arsize = '0;
            arb_read_if.arburst = '0;
            arb_read_if.arlock = '0;
            arb_read_if.arcache = '0;
            arb_read_if.arprot = '0;
            arb_read_if.arqos = '0;
            arb_read_if.arregion = '0;
            arb_read_if.aruser = '0;
        end
    end
    
    // Address decoder for slave selection
    function automatic int decode_slave_write(logic [CFG.ADDR_WIDTH-1:0] addr);
        for (int s = 0; s < NUM_SLAVES; s++) begin
            if ((addr & ~slave_addr_mask[s]) == slave_base_addr[s]) begin
                return s;
            end
        end
        return -1;  // No match - will generate DECERR
    endfunction
    
    function automatic int decode_slave_read(logic [CFG.ADDR_WIDTH-1:0] addr);
        for (int s = 0; s < NUM_SLAVES; s++) begin
            if ((addr & ~slave_addr_mask[s]) == slave_base_addr[s]) begin
                return s;
            end
        end
        return -1;  // No match - will generate DECERR
    endfunction
    
    // Write channel routing to slaves
    logic [$clog2(NUM_SLAVES+1)-1:0] aw_target_slave;
    logic aw_decode_error;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            aw_target_slave <= '0;
            aw_decode_error <= 1'b0;
        end else begin
            if (arb_write_if.awvalid && arb_write_if.awready) begin
                int target = decode_slave_write(arb_write_if.awaddr);
                if (target >= 0) begin
                    aw_target_slave <= target;
                    aw_decode_error <= 1'b0;
                end else begin
                    aw_target_slave <= '0;
                    aw_decode_error <= 1'b1;
                end
            end
        end
    end
    
    // Connect to slave write channels
    always_comb begin
        // Default all slave inputs to 0
        for (int s = 0; s < NUM_SLAVES; s++) begin
            slave_if[s].awvalid = 1'b0;
            slave_if[s].awid = '0;
            slave_if[s].awaddr = '0;
            slave_if[s].awlen = '0;
            slave_if[s].awsize = '0;
            slave_if[s].awburst = '0;
            slave_if[s].awlock = '0;
            slave_if[s].awcache = '0;
            slave_if[s].awprot = '0;
            slave_if[s].awqos = '0;
            slave_if[s].awregion = '0;
            slave_if[s].awuser = '0;
            slave_if[s].wvalid = 1'b0;
            slave_if[s].wdata = '0;
            slave_if[s].wstrb = '0;
            slave_if[s].wlast = 1'b0;
            slave_if[s].wuser = '0;
        end
        
        // Route to selected slave
        if (!aw_decode_error && aw_target_slave < NUM_SLAVES) begin
            int s = aw_target_slave;
            
            // Write address
            slave_if[s].awvalid = arb_write_if.awvalid;
            slave_if[s].awid = arb_write_if.awid[CFG.ID_WIDTH-1:0];
            slave_if[s].awaddr = arb_write_if.awaddr;
            slave_if[s].awlen = arb_write_if.awlen;
            slave_if[s].awsize = arb_write_if.awsize;
            slave_if[s].awburst = arb_write_if.awburst;
            slave_if[s].awlock = arb_write_if.awlock;
            slave_if[s].awcache = arb_write_if.awcache;
            slave_if[s].awprot = arb_write_if.awprot;
            slave_if[s].awqos = arb_write_if.awqos;
            slave_if[s].awregion = arb_write_if.awregion;
            if (CFG.SUPPORT_USER_SIGNALS && CFG.AWUSER_WIDTH > 0)
                slave_if[s].awuser = arb_write_if.awuser;
            arb_write_if.awready = slave_if[s].awready;
            
            // Write data
            slave_if[s].wvalid = arb_write_if.wvalid;
            slave_if[s].wdata = arb_write_if.wdata;
            slave_if[s].wstrb = arb_write_if.wstrb;
            slave_if[s].wlast = arb_write_if.wlast;
            if (CFG.SUPPORT_USER_SIGNALS && CFG.WUSER_WIDTH > 0)
                slave_if[s].wuser = arb_write_if.wuser;
            arb_write_if.wready = slave_if[s].wready;
        end else begin
            // Generate DECERR
            arb_write_if.awready = 1'b1;
            arb_write_if.wready = 1'b1;
        end
    end
    
    // Read channel routing to slaves
    logic [$clog2(NUM_SLAVES+1)-1:0] ar_target_slave;
    logic ar_decode_error;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ar_target_slave <= '0;
            ar_decode_error <= 1'b0;
        end else begin
            if (arb_read_if.arvalid && arb_read_if.arready) begin
                int target = decode_slave_read(arb_read_if.araddr);
                if (target >= 0) begin
                    ar_target_slave <= target;
                    ar_decode_error <= 1'b0;
                end else begin
                    ar_target_slave <= '0;
                    ar_decode_error <= 1'b1;
                end
            end
        end
    end
    
    // Connect to slave read channels
    always_comb begin
        // Default all slave inputs to 0
        for (int s = 0; s < NUM_SLAVES; s++) begin
            slave_if[s].arvalid = 1'b0;
            slave_if[s].arid = '0;
            slave_if[s].araddr = '0;
            slave_if[s].arlen = '0;
            slave_if[s].arsize = '0;
            slave_if[s].arburst = '0;
            slave_if[s].arlock = '0;
            slave_if[s].arcache = '0;
            slave_if[s].arprot = '0;
            slave_if[s].arqos = '0;
            slave_if[s].arregion = '0;
            slave_if[s].aruser = '0;
        end
        
        // Route to selected slave
        if (!ar_decode_error && ar_target_slave < NUM_SLAVES) begin
            int s = ar_target_slave;
            
            slave_if[s].arvalid = arb_read_if.arvalid;
            slave_if[s].arid = arb_read_if.arid[CFG.ID_WIDTH-1:0];
            slave_if[s].araddr = arb_read_if.araddr;
            slave_if[s].arlen = arb_read_if.arlen;
            slave_if[s].arsize = arb_read_if.arsize;
            slave_if[s].arburst = arb_read_if.arburst;
            slave_if[s].arlock = arb_read_if.arlock;
            slave_if[s].arcache = arb_read_if.arcache;
            slave_if[s].arprot = arb_read_if.arprot;
            slave_if[s].arqos = arb_read_if.arqos;
            slave_if[s].arregion = arb_read_if.arregion;
            if (CFG.SUPPORT_USER_SIGNALS && CFG.ARUSER_WIDTH > 0)
                slave_if[s].aruser = arb_read_if.aruser;
            arb_read_if.arready = slave_if[s].arready;
        end else begin
            // Generate DECERR
            arb_read_if.arready = 1'b1;
        end
    end
    
    // Response channel routing back to masters
    // Write response
    always_comb begin
        arb_write_if.bvalid = 1'b0;
        arb_write_if.bid = '0;
        arb_write_if.bresp = '0;
        arb_write_if.buser = '0;
        
        for (int s = 0; s < NUM_SLAVES; s++) begin
            slave_if[s].bready = 1'b0;
        end
        
        if (aw_decode_error) begin
            // Generate DECERR response
            arb_write_if.bvalid = 1'b1;
            arb_write_if.bid = '0;  // TODO: track proper ID
            arb_write_if.bresp = AXI4_RESP_DECERR;
        end else if (aw_target_slave < NUM_SLAVES) begin
            int s = aw_target_slave;
            arb_write_if.bvalid = slave_if[s].bvalid;
            arb_write_if.bid = {w_active_master, slave_if[s].bid};
            arb_write_if.bresp = slave_if[s].bresp;
            if (CFG.SUPPORT_USER_SIGNALS && CFG.BUSER_WIDTH > 0)
                arb_write_if.buser = slave_if[s].buser;
            slave_if[s].bready = arb_write_if.bready;
        end
    end
    
    // Route write responses back to masters
    always_comb begin
        for (int m = 0; m < NUM_MASTERS; m++) begin
            master_if[m].bvalid = 1'b0;
            master_if[m].bid = '0;
            master_if[m].bresp = '0;
            master_if[m].buser = '0;
        end
        
        arb_write_if.bready = 1'b0;
        
        if (arb_write_if.bvalid) begin
            int m = arb_write_if.bid[INTERCONNECT_ID_WIDTH-1:CFG.ID_WIDTH];
            master_if[m].bvalid = 1'b1;
            master_if[m].bid = arb_write_if.bid[CFG.ID_WIDTH-1:0];
            master_if[m].bresp = arb_write_if.bresp;
            if (CFG.SUPPORT_USER_SIGNALS && CFG.BUSER_WIDTH > 0)
                master_if[m].buser = arb_write_if.buser;
            arb_write_if.bready = master_if[m].bready;
        end
    end
    
    // Read response routing
    always_comb begin
        arb_read_if.rvalid = 1'b0;
        arb_read_if.rid = '0;
        arb_read_if.rdata = '0;
        arb_read_if.rresp = '0;
        arb_read_if.rlast = 1'b0;
        arb_read_if.ruser = '0;
        
        for (int s = 0; s < NUM_SLAVES; s++) begin
            slave_if[s].rready = 1'b0;
        end
        
        if (ar_decode_error) begin
            // Generate DECERR response
            arb_read_if.rvalid = 1'b1;
            arb_read_if.rid = '0;  // TODO: track proper ID
            arb_read_if.rdata = '0;
            arb_read_if.rresp = AXI4_RESP_DECERR;
            arb_read_if.rlast = 1'b1;
        end else if (ar_target_slave < NUM_SLAVES) begin
            int s = ar_target_slave;
            arb_read_if.rvalid = slave_if[s].rvalid;
            arb_read_if.rid = {ar_grant_master, slave_if[s].rid};  // TODO: track properly
            arb_read_if.rdata = slave_if[s].rdata;
            arb_read_if.rresp = slave_if[s].rresp;
            arb_read_if.rlast = slave_if[s].rlast;
            if (CFG.SUPPORT_USER_SIGNALS && CFG.RUSER_WIDTH > 0)
                arb_read_if.ruser = slave_if[s].ruser;
            slave_if[s].rready = arb_read_if.rready;
        end
    end
    
    // Route read responses back to masters
    always_comb begin
        for (int m = 0; m < NUM_MASTERS; m++) begin
            master_if[m].rvalid = 1'b0;
            master_if[m].rid = '0;
            master_if[m].rdata = '0;
            master_if[m].rresp = '0;
            master_if[m].rlast = 1'b0;
            master_if[m].ruser = '0;
        end
        
        arb_read_if.rready = 1'b0;
        
        if (arb_read_if.rvalid) begin
            int m = arb_read_if.rid[INTERCONNECT_ID_WIDTH-1:CFG.ID_WIDTH];
            master_if[m].rvalid = 1'b1;
            master_if[m].rid = arb_read_if.rid[CFG.ID_WIDTH-1:0];
            master_if[m].rdata = arb_read_if.rdata;
            master_if[m].rresp = arb_read_if.rresp;
            master_if[m].rlast = arb_read_if.rlast;
            if (CFG.SUPPORT_USER_SIGNALS && CFG.RUSER_WIDTH > 0)
                master_if[m].ruser = arb_read_if.ruser;
            arb_read_if.rready = master_if[m].rready;
        end
    end
    
endmodule : axi4_interconnect