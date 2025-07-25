// Auto-generated RTL Wrapper for Tool-Generated AXI4 Interconnect
// This wrapper connects tim_axi4_vip to the generated RTL interconnect
// Configuration: 2 Masters, 3 Slaves

module dut_wrapper #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 64,
    parameter ID_WIDTH   = 4
) (
    input  logic clk,
    input  logic rst_n,
    axi4_if.slave axi_if  // tim_axi4_vip interface
);

    // Internal signals for additional masters
    // Master 1 signals (terminated)
    logic [3:0]    m1_awid;
    logic [31:0]  m1_awaddr;
    logic [7:0]              m1_awlen;
    logic [2:0]              m1_awsize;
    logic [1:0]              m1_awburst;
    logic                    m1_awlock;
    logic [3:0]              m1_awcache;
    logic [2:0]              m1_awprot;
    logic [3:0]              m1_awqos;
    logic                    m1_awvalid;
    logic                    m1_awready;
    
    logic [63:0]  m1_wdata;
    logic [7.0:0] m1_wstrb;
    logic                    m1_wlast;
    logic                    m1_wvalid;
    logic                    m1_wready;
    
    logic [3:0]    m1_bid;
    logic [1:0]              m1_bresp;
    logic                    m1_bvalid;
    logic                    m1_bready;
    
    logic [3:0]    m1_arid;
    logic [31:0]  m1_araddr;
    logic [7:0]              m1_arlen;
    logic [2:0]              m1_arsize;
    logic [1:0]              m1_arburst;
    logic                    m1_arlock;
    logic [3:0]              m1_arcache;
    logic [2:0]              m1_arprot;
    logic [3:0]              m1_arqos;
    logic                    m1_arvalid;
    logic                    m1_arready;
    
    logic [3:0]    m1_rid;
    logic [63:0]  m1_rdata;
    logic [1:0]              m1_rresp;
    logic                    m1_rlast;
    logic                    m1_rvalid;
    logic                    m1_rready;
    // Internal signals for slave interfaces
    // Slave 0 signals
    logic [3:0]    s0_awid;
    logic [31:0]  s0_awaddr;
    logic [7:0]              s0_awlen;
    logic [2:0]              s0_awsize;
    logic [1:0]              s0_awburst;
    logic                    s0_awlock;
    logic [3:0]              s0_awcache;
    logic [2:0]              s0_awprot;
    logic [3:0]              s0_awqos;
    logic                    s0_awvalid;
    logic                    s0_awready;
    
    logic [63:0]  s0_wdata;
    logic [7.0:0] s0_wstrb;
    logic                    s0_wlast;
    logic                    s0_wvalid;
    logic                    s0_wready;
    
    logic [3:0]    s0_bid;
    logic [1:0]              s0_bresp;
    logic                    s0_bvalid;
    logic                    s0_bready;
    
    logic [3:0]    s0_arid;
    logic [31:0]  s0_araddr;
    logic [7:0]              s0_arlen;
    logic [2:0]              s0_arsize;
    logic [1:0]              s0_arburst;
    logic                    s0_arlock;
    logic [3:0]              s0_arcache;
    logic [2:0]              s0_arprot;
    logic [3:0]              s0_arqos;
    logic                    s0_arvalid;
    logic                    s0_arready;
    
    logic [3:0]    s0_rid;
    logic [63:0]  s0_rdata;
    logic [1:0]              s0_rresp;
    logic                    s0_rlast;
    logic                    s0_rvalid;
    logic                    s0_rready;
    // Slave 1 signals
    logic [3:0]    s1_awid;
    logic [31:0]  s1_awaddr;
    logic [7:0]              s1_awlen;
    logic [2:0]              s1_awsize;
    logic [1:0]              s1_awburst;
    logic                    s1_awlock;
    logic [3:0]              s1_awcache;
    logic [2:0]              s1_awprot;
    logic [3:0]              s1_awqos;
    logic                    s1_awvalid;
    logic                    s1_awready;
    
    logic [63:0]  s1_wdata;
    logic [7.0:0] s1_wstrb;
    logic                    s1_wlast;
    logic                    s1_wvalid;
    logic                    s1_wready;
    
    logic [3:0]    s1_bid;
    logic [1:0]              s1_bresp;
    logic                    s1_bvalid;
    logic                    s1_bready;
    
    logic [3:0]    s1_arid;
    logic [31:0]  s1_araddr;
    logic [7:0]              s1_arlen;
    logic [2:0]              s1_arsize;
    logic [1:0]              s1_arburst;
    logic                    s1_arlock;
    logic [3:0]              s1_arcache;
    logic [2:0]              s1_arprot;
    logic [3:0]              s1_arqos;
    logic                    s1_arvalid;
    logic                    s1_arready;
    
    logic [3:0]    s1_rid;
    logic [63:0]  s1_rdata;
    logic [1:0]              s1_rresp;
    logic                    s1_rlast;
    logic                    s1_rvalid;
    logic                    s1_rready;
    // Slave 2 signals
    logic [3:0]    s2_awid;
    logic [31:0]  s2_awaddr;
    logic [7:0]              s2_awlen;
    logic [2:0]              s2_awsize;
    logic [1:0]              s2_awburst;
    logic                    s2_awlock;
    logic [3:0]              s2_awcache;
    logic [2:0]              s2_awprot;
    logic [3:0]              s2_awqos;
    logic                    s2_awvalid;
    logic                    s2_awready;
    
    logic [63:0]  s2_wdata;
    logic [7.0:0] s2_wstrb;
    logic                    s2_wlast;
    logic                    s2_wvalid;
    logic                    s2_wready;
    
    logic [3:0]    s2_bid;
    logic [1:0]              s2_bresp;
    logic                    s2_bvalid;
    logic                    s2_bready;
    
    logic [3:0]    s2_arid;
    logic [31:0]  s2_araddr;
    logic [7:0]              s2_arlen;
    logic [2:0]              s2_arsize;
    logic [1:0]              s2_arburst;
    logic                    s2_arlock;
    logic [3:0]              s2_arcache;
    logic [2:0]              s2_arprot;
    logic [3:0]              s2_arqos;
    logic                    s2_arvalid;
    logic                    s2_arready;
    
    logic [3:0]    s2_rid;
    logic [63:0]  s2_rdata;
    logic [1:0]              s2_rresp;
    logic                    s2_rlast;
    logic                    s2_rvalid;
    logic                    s2_rready;
    // =========================================
    // INTERCONNECT INSTANTIATION
    // =========================================
    
    axi4_interconnect_m2s3 #(
        .DATA_WIDTH(64),
        .ADDR_WIDTH(32),
        .ID_WIDTH(4),
        .USER_WIDTH(1)
    ) generated_interconnect (
        // Clock and Reset
        .aclk(clk),
        .aresetn(rst_n),
        
        // Master 0 Interface (connected to VIP)
        .m0_awid(axi_if.awid),
        .m0_awaddr(axi_if.awaddr),
        .m0_awlen(axi_if.awlen),
        .m0_awsize(axi_if.awsize),
        .m0_awburst(axi_if.awburst),
        .m0_awlock(axi_if.awlock),
        .m0_awcache(axi_if.awcache),
        .m0_awprot(axi_if.awprot),
        .m0_awqos(axi_if.awqos),
        .m0_awvalid(axi_if.awvalid),
        .m0_awready(axi_if.awready),
        
        .m0_wdata(axi_if.wdata),
        .m0_wstrb(axi_if.wstrb),
        .m0_wlast(axi_if.wlast),
        .m0_wvalid(axi_if.wvalid),
        .m0_wready(axi_if.wready),
        
        .m0_bid(axi_if.bid),
        .m0_bresp(axi_if.bresp),
        .m0_bvalid(axi_if.bvalid),
        .m0_bready(axi_if.bready),
        
        .m0_arid(axi_if.arid),
        .m0_araddr(axi_if.araddr),
        .m0_arlen(axi_if.arlen),
        .m0_arsize(axi_if.arsize),
        .m0_arburst(axi_if.arburst),
        .m0_arlock(axi_if.arlock),
        .m0_arcache(axi_if.arcache),
        .m0_arprot(axi_if.arprot),
        .m0_arqos(axi_if.arqos),
        .m0_arvalid(axi_if.arvalid),
        .m0_arready(axi_if.arready),
        
        .m0_rid(axi_if.rid),
        .m0_rdata(axi_if.rdata),
        .m0_rresp(axi_if.rresp),
        .m0_rlast(axi_if.rlast),
        .m0_rvalid(axi_if.rvalid),
        .m0_rready(axi_if.rready),
        // Master 1 Interface (terminated)
        .m1_awid(m1_awid),
        .m1_awaddr(m1_awaddr),
        .m1_awlen(m1_awlen),
        .m1_awsize(m1_awsize),
        .m1_awburst(m1_awburst),
        .m1_awlock(m1_awlock),
        .m1_awcache(m1_awcache),
        .m1_awprot(m1_awprot),
        .m1_awqos(m1_awqos),
        .m1_awvalid(m1_awvalid),
        .m1_awready(m1_awready),
        
        .m1_wdata(m1_wdata),
        .m1_wstrb(m1_wstrb),
        .m1_wlast(m1_wlast),
        .m1_wvalid(m1_wvalid),
        .m1_wready(m1_wready),
        
        .m1_bid(m1_bid),
        .m1_bresp(m1_bresp),
        .m1_bvalid(m1_bvalid),
        .m1_bready(m1_bready),
        
        .m1_arid(m1_arid),
        .m1_araddr(m1_araddr),
        .m1_arlen(m1_arlen),
        .m1_arsize(m1_arsize),
        .m1_arburst(m1_arburst),
        .m1_arlock(m1_arlock),
        .m1_arcache(m1_arcache),
        .m1_arprot(m1_arprot),
        .m1_arqos(m1_arqos),
        .m1_arvalid(m1_arvalid),
        .m1_arready(m1_arready),
        
        .m1_rid(m1_rid),
        .m1_rdata(m1_rdata),
        .m1_rresp(m1_rresp),
        .m1_rlast(m1_rlast),
        .m1_rvalid(m1_rvalid),
        .m1_rready(m1_rready),
        // Slave 0 Interface
        .s0_awid(s0_awid),
        .s0_awaddr(s0_awaddr),
        .s0_awlen(s0_awlen),
        .s0_awsize(s0_awsize),
        .s0_awburst(s0_awburst),
        .s0_awlock(s0_awlock),
        .s0_awcache(s0_awcache),
        .s0_awprot(s0_awprot),
        .s0_awqos(s0_awqos),
        .s0_awvalid(s0_awvalid),
        .s0_awready(s0_awready),
        
        .s0_wdata(s0_wdata),
        .s0_wstrb(s0_wstrb),
        .s0_wlast(s0_wlast),
        .s0_wvalid(s0_wvalid),
        .s0_wready(s0_wready),
        
        .s0_bid(s0_bid),
        .s0_bresp(s0_bresp),
        .s0_bvalid(s0_bvalid),
        .s0_bready(s0_bready),
        
        .s0_arid(s0_arid),
        .s0_araddr(s0_araddr),
        .s0_arlen(s0_arlen),
        .s0_arsize(s0_arsize),
        .s0_arburst(s0_arburst),
        .s0_arlock(s0_arlock),
        .s0_arcache(s0_arcache),
        .s0_arprot(s0_arprot),
        .s0_arqos(s0_arqos),
        .s0_arvalid(s0_arvalid),
        .s0_arready(s0_arready),
        
        .s0_rid(s0_rid),
        .s0_rdata(s0_rdata),
        .s0_rresp(s0_rresp),
        .s0_rlast(s0_rlast),
        .s0_rvalid(s0_rvalid),
        .s0_rready(s0_rready),
        // Slave 1 Interface
        .s1_awid(s1_awid),
        .s1_awaddr(s1_awaddr),
        .s1_awlen(s1_awlen),
        .s1_awsize(s1_awsize),
        .s1_awburst(s1_awburst),
        .s1_awlock(s1_awlock),
        .s1_awcache(s1_awcache),
        .s1_awprot(s1_awprot),
        .s1_awqos(s1_awqos),
        .s1_awvalid(s1_awvalid),
        .s1_awready(s1_awready),
        
        .s1_wdata(s1_wdata),
        .s1_wstrb(s1_wstrb),
        .s1_wlast(s1_wlast),
        .s1_wvalid(s1_wvalid),
        .s1_wready(s1_wready),
        
        .s1_bid(s1_bid),
        .s1_bresp(s1_bresp),
        .s1_bvalid(s1_bvalid),
        .s1_bready(s1_bready),
        
        .s1_arid(s1_arid),
        .s1_araddr(s1_araddr),
        .s1_arlen(s1_arlen),
        .s1_arsize(s1_arsize),
        .s1_arburst(s1_arburst),
        .s1_arlock(s1_arlock),
        .s1_arcache(s1_arcache),
        .s1_arprot(s1_arprot),
        .s1_arqos(s1_arqos),
        .s1_arvalid(s1_arvalid),
        .s1_arready(s1_arready),
        
        .s1_rid(s1_rid),
        .s1_rdata(s1_rdata),
        .s1_rresp(s1_rresp),
        .s1_rlast(s1_rlast),
        .s1_rvalid(s1_rvalid),
        .s1_rready(s1_rready),
        // Slave 2 Interface
        .s2_awid(s2_awid),
        .s2_awaddr(s2_awaddr),
        .s2_awlen(s2_awlen),
        .s2_awsize(s2_awsize),
        .s2_awburst(s2_awburst),
        .s2_awlock(s2_awlock),
        .s2_awcache(s2_awcache),
        .s2_awprot(s2_awprot),
        .s2_awqos(s2_awqos),
        .s2_awvalid(s2_awvalid),
        .s2_awready(s2_awready),
        
        .s2_wdata(s2_wdata),
        .s2_wstrb(s2_wstrb),
        .s2_wlast(s2_wlast),
        .s2_wvalid(s2_wvalid),
        .s2_wready(s2_wready),
        
        .s2_bid(s2_bid),
        .s2_bresp(s2_bresp),
        .s2_bvalid(s2_bvalid),
        .s2_bready(s2_bready),
        
        .s2_arid(s2_arid),
        .s2_araddr(s2_araddr),
        .s2_arlen(s2_arlen),
        .s2_arsize(s2_arsize),
        .s2_arburst(s2_arburst),
        .s2_arlock(s2_arlock),
        .s2_arcache(s2_arcache),
        .s2_arprot(s2_arprot),
        .s2_arqos(s2_arqos),
        .s2_arvalid(s2_arvalid),
        .s2_arready(s2_arready),
        
        .s2_rid(s2_rid),
        .s2_rdata(s2_rdata),
        .s2_rresp(s2_rresp),
        .s2_rlast(s2_rlast),
        .s2_rvalid(s2_rvalid),
        .s2_rready(s2_rready)
    );

    // Slave termination logic for testing

    // Slave 0 (DDR_Controller) - Simple memory model
    always @(posedge clk) begin
        if (!rst_n) begin
            s0_awready <= 1'b0;
            s0_wready  <= 1'b0;
            s0_bvalid  <= 1'b0;
            s0_arready <= 1'b0;
            s0_rvalid  <= 1'b0;
        end else begin
            // Simple handshaking
            s0_awready <= 1'b1;
            s0_wready  <= 1'b1;
            s0_arready <= 1'b1;
            
            // Write response
            if (s0_awvalid && s0_awready && s0_wvalid && s0_wready && s0_wlast) begin
                s0_bvalid <= 1'b1;
                s0_bid    <= s0_awid;
                s0_bresp  <= 2'b00; // OKAY
            end else if (s0_bready && s0_bvalid) begin
                s0_bvalid <= 1'b0;
            end
            
            // Read response (single beat for now)
            if (s0_arvalid && s0_arready) begin
                s0_rvalid <= 1'b1;
                s0_rid    <= s0_arid;
                s0_rdata  <= {{DATA_WIDTH{1'b0}}}; // Return zeros
                s0_rresp  <= 2'b00; // OKAY
                s0_rlast  <= 1'b1;  // Single beat
            end else if (s0_rready && s0_rvalid) begin
                s0_rvalid <= 1'b0;
            end
        end
    end

    // Slave 1 (SRAM) - Simple memory model
    always @(posedge clk) begin
        if (!rst_n) begin
            s1_awready <= 1'b0;
            s1_wready  <= 1'b0;
            s1_bvalid  <= 1'b0;
            s1_arready <= 1'b0;
            s1_rvalid  <= 1'b0;
        end else begin
            // Simple handshaking
            s1_awready <= 1'b1;
            s1_wready  <= 1'b1;
            s1_arready <= 1'b1;
            
            // Write response
            if (s1_awvalid && s1_awready && s1_wvalid && s1_wready && s1_wlast) begin
                s1_bvalid <= 1'b1;
                s1_bid    <= s1_awid;
                s1_bresp  <= 2'b00; // OKAY
            end else if (s1_bready && s1_bvalid) begin
                s1_bvalid <= 1'b0;
            end
            
            // Read response (single beat for now)
            if (s1_arvalid && s1_arready) begin
                s1_rvalid <= 1'b1;
                s1_rid    <= s1_arid;
                s1_rdata  <= {{DATA_WIDTH{1'b0}}}; // Return zeros
                s1_rresp  <= 2'b00; // OKAY
                s1_rlast  <= 1'b1;  // Single beat
            end else if (s1_rready && s1_rvalid) begin
                s1_rvalid <= 1'b0;
            end
        end
    end

    // Slave 2 (Peripherals) - Simple memory model
    always @(posedge clk) begin
        if (!rst_n) begin
            s2_awready <= 1'b0;
            s2_wready  <= 1'b0;
            s2_bvalid  <= 1'b0;
            s2_arready <= 1'b0;
            s2_rvalid  <= 1'b0;
        end else begin
            // Simple handshaking
            s2_awready <= 1'b1;
            s2_wready  <= 1'b1;
            s2_arready <= 1'b1;
            
            // Write response
            if (s2_awvalid && s2_awready && s2_wvalid && s2_wready && s2_wlast) begin
                s2_bvalid <= 1'b1;
                s2_bid    <= s2_awid;
                s2_bresp  <= 2'b00; // OKAY
            end else if (s2_bready && s2_bvalid) begin
                s2_bvalid <= 1'b0;
            end
            
            // Read response (single beat for now)
            if (s2_arvalid && s2_arready) begin
                s2_rvalid <= 1'b1;
                s2_rid    <= s2_arid;
                s2_rdata  <= {{DATA_WIDTH{1'b0}}}; // Return zeros
                s2_rresp  <= 2'b00; // OKAY
                s2_rlast  <= 1'b1;  // Single beat
            end else if (s2_rready && s2_rvalid) begin
                s2_rvalid <= 1'b0;
            end
        end
    end

    // Terminate unused master interfaces
    assign m1_awvalid = 1'b0;
    assign m1_wvalid  = 1'b0;
    assign m1_bready  = 1'b1;
    assign m1_arvalid = 1'b0;
    assign m1_rready  = 1'b1;

    // =========================================
    // AUTO-GENERATED WRAPPER
    // =========================================
    // This wrapper was automatically generated for the
    // tool-generated interconnect with proper connections
    // for all masters and slaves.
    
endmodule
