//==============================================================================
// Testbench for AXI4 Interconnect
//==============================================================================

`timescale 1ns/1ps

module tb_axi4_interconnect;

parameter DATA_WIDTH = 64;
parameter ADDR_WIDTH = 32;
parameter ID_WIDTH = 4;

reg aclk;
reg aresetn;

// Master 0 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     m0_awid;
wire [ADDR_WIDTH-1:0]   m0_awaddr;
wire [7:0]              m0_awlen;
wire [2:0]              m0_awsize;
wire [1:0]              m0_awburst;
wire                    m0_awlock;
wire [3:0]              m0_awcache;
wire [2:0]              m0_awprot;
wire [3:0]              m0_awqos;
wire                    m0_awvalid;
wire                    m0_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   m0_wdata;
wire [DATA_WIDTH/8-1:0] m0_wstrb;
wire                    m0_wlast;
wire                    m0_wvalid;
wire                    m0_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     m0_bid;
wire [1:0]              m0_bresp;
wire                    m0_bvalid;
wire                    m0_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     m0_arid;
wire [ADDR_WIDTH-1:0]   m0_araddr;
wire [7:0]              m0_arlen;
wire [2:0]              m0_arsize;
wire [1:0]              m0_arburst;
wire                    m0_arlock;
wire [3:0]              m0_arcache;
wire [2:0]              m0_arprot;
wire [3:0]              m0_arqos;
wire                    m0_arvalid;
wire                    m0_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     m0_rid;
wire [DATA_WIDTH-1:0]   m0_rdata;
wire [1:0]              m0_rresp;
wire                    m0_rlast;
wire                    m0_rvalid;
wire                    m0_rready;

// Master 1 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     m1_awid;
wire [ADDR_WIDTH-1:0]   m1_awaddr;
wire [7:0]              m1_awlen;
wire [2:0]              m1_awsize;
wire [1:0]              m1_awburst;
wire                    m1_awlock;
wire [3:0]              m1_awcache;
wire [2:0]              m1_awprot;
wire [3:0]              m1_awqos;
wire                    m1_awvalid;
wire                    m1_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   m1_wdata;
wire [DATA_WIDTH/8-1:0] m1_wstrb;
wire                    m1_wlast;
wire                    m1_wvalid;
wire                    m1_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     m1_bid;
wire [1:0]              m1_bresp;
wire                    m1_bvalid;
wire                    m1_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     m1_arid;
wire [ADDR_WIDTH-1:0]   m1_araddr;
wire [7:0]              m1_arlen;
wire [2:0]              m1_arsize;
wire [1:0]              m1_arburst;
wire                    m1_arlock;
wire [3:0]              m1_arcache;
wire [2:0]              m1_arprot;
wire [3:0]              m1_arqos;
wire                    m1_arvalid;
wire                    m1_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     m1_rid;
wire [DATA_WIDTH-1:0]   m1_rdata;
wire [1:0]              m1_rresp;
wire                    m1_rlast;
wire                    m1_rvalid;
wire                    m1_rready;

// Slave 0 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     s0_awid;
wire [ADDR_WIDTH-1:0]   s0_awaddr;
wire [7:0]              s0_awlen;
wire [2:0]              s0_awsize;
wire [1:0]              s0_awburst;
wire                    s0_awlock;
wire [3:0]              s0_awcache;
wire [2:0]              s0_awprot;
wire [3:0]              s0_awqos;
wire                    s0_awvalid;
wire                    s0_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   s0_wdata;
wire [DATA_WIDTH/8-1:0] s0_wstrb;
wire                    s0_wlast;
wire                    s0_wvalid;
wire                    s0_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     s0_bid;
wire [1:0]              s0_bresp;
wire                    s0_bvalid;
wire                    s0_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     s0_arid;
wire [ADDR_WIDTH-1:0]   s0_araddr;
wire [7:0]              s0_arlen;
wire [2:0]              s0_arsize;
wire [1:0]              s0_arburst;
wire                    s0_arlock;
wire [3:0]              s0_arcache;
wire [2:0]              s0_arprot;
wire [3:0]              s0_arqos;
wire                    s0_arvalid;
wire                    s0_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     s0_rid;
wire [DATA_WIDTH-1:0]   s0_rdata;
wire [1:0]              s0_rresp;
wire                    s0_rlast;
wire                    s0_rvalid;
wire                    s0_rready;

// Slave 1 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     s1_awid;
wire [ADDR_WIDTH-1:0]   s1_awaddr;
wire [7:0]              s1_awlen;
wire [2:0]              s1_awsize;
wire [1:0]              s1_awburst;
wire                    s1_awlock;
wire [3:0]              s1_awcache;
wire [2:0]              s1_awprot;
wire [3:0]              s1_awqos;
wire                    s1_awvalid;
wire                    s1_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   s1_wdata;
wire [DATA_WIDTH/8-1:0] s1_wstrb;
wire                    s1_wlast;
wire                    s1_wvalid;
wire                    s1_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     s1_bid;
wire [1:0]              s1_bresp;
wire                    s1_bvalid;
wire                    s1_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     s1_arid;
wire [ADDR_WIDTH-1:0]   s1_araddr;
wire [7:0]              s1_arlen;
wire [2:0]              s1_arsize;
wire [1:0]              s1_arburst;
wire                    s1_arlock;
wire [3:0]              s1_arcache;
wire [2:0]              s1_arprot;
wire [3:0]              s1_arqos;
wire                    s1_arvalid;
wire                    s1_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     s1_rid;
wire [DATA_WIDTH-1:0]   s1_rdata;
wire [1:0]              s1_rresp;
wire                    s1_rlast;
wire                    s1_rvalid;
wire                    s1_rready;

// Slave 2 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     s2_awid;
wire [ADDR_WIDTH-1:0]   s2_awaddr;
wire [7:0]              s2_awlen;
wire [2:0]              s2_awsize;
wire [1:0]              s2_awburst;
wire                    s2_awlock;
wire [3:0]              s2_awcache;
wire [2:0]              s2_awprot;
wire [3:0]              s2_awqos;
wire                    s2_awvalid;
wire                    s2_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   s2_wdata;
wire [DATA_WIDTH/8-1:0] s2_wstrb;
wire                    s2_wlast;
wire                    s2_wvalid;
wire                    s2_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     s2_bid;
wire [1:0]              s2_bresp;
wire                    s2_bvalid;
wire                    s2_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     s2_arid;
wire [ADDR_WIDTH-1:0]   s2_araddr;
wire [7:0]              s2_arlen;
wire [2:0]              s2_arsize;
wire [1:0]              s2_arburst;
wire                    s2_arlock;
wire [3:0]              s2_arcache;
wire [2:0]              s2_arprot;
wire [3:0]              s2_arqos;
wire                    s2_arvalid;
wire                    s2_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     s2_rid;
wire [DATA_WIDTH-1:0]   s2_rdata;
wire [1:0]              s2_rresp;
wire                    s2_rlast;
wire                    s2_rvalid;
wire                    s2_rready;

// Tie off master 0 inputs
assign m0_awid = {ID_WIDTH{1'b0}};
assign m0_awaddr = {ADDR_WIDTH{1'b0}};
assign m0_awlen = 8'd0;
assign m0_awsize = 3'd0;
assign m0_awburst = 2'b01;
assign m0_awlock = 1'b0;
assign m0_awcache = 4'b0000;
assign m0_awprot = 3'b000;
assign m0_awqos = 4'b0000;
assign m0_awvalid = 1'b0;
assign m0_wdata = {DATA_WIDTH{1'b0}};
assign m0_wstrb = {(DATA_WIDTH/8){1'b0}};
assign m0_wlast = 1'b0;
assign m0_wvalid = 1'b0;
assign m0_bready = 1'b1;
assign m0_arid = {ID_WIDTH{1'b0}};
assign m0_araddr = {ADDR_WIDTH{1'b0}};
assign m0_arlen = 8'd0;
assign m0_arsize = 3'd0;
assign m0_arburst = 2'b01;
assign m0_arlock = 1'b0;
assign m0_arcache = 4'b0000;
assign m0_arprot = 3'b000;
assign m0_arqos = 4'b0000;
assign m0_arvalid = 1'b0;
assign m0_rready = 1'b1;

// Tie off master 1 inputs
assign m1_awid = {ID_WIDTH{1'b0}};
assign m1_awaddr = {ADDR_WIDTH{1'b0}};
assign m1_awlen = 8'd0;
assign m1_awsize = 3'd0;
assign m1_awburst = 2'b01;
assign m1_awlock = 1'b0;
assign m1_awcache = 4'b0000;
assign m1_awprot = 3'b000;
assign m1_awqos = 4'b0000;
assign m1_awvalid = 1'b0;
assign m1_wdata = {DATA_WIDTH{1'b0}};
assign m1_wstrb = {(DATA_WIDTH/8){1'b0}};
assign m1_wlast = 1'b0;
assign m1_wvalid = 1'b0;
assign m1_bready = 1'b1;
assign m1_arid = {ID_WIDTH{1'b0}};
assign m1_araddr = {ADDR_WIDTH{1'b0}};
assign m1_arlen = 8'd0;
assign m1_arsize = 3'd0;
assign m1_arburst = 2'b01;
assign m1_arlock = 1'b0;
assign m1_arcache = 4'b0000;
assign m1_arprot = 3'b000;
assign m1_arqos = 4'b0000;
assign m1_arvalid = 1'b0;
assign m1_rready = 1'b1;

// Tie off slave 0 outputs
assign s0_awready = 1'b0;
assign s0_wready = 1'b0;
assign s0_bid = {ID_WIDTH{1'b0}};
assign s0_bresp = 2'b00;
assign s0_bvalid = 1'b0;
assign s0_arready = 1'b0;
assign s0_rid = {ID_WIDTH{1'b0}};
assign s0_rdata = {DATA_WIDTH{1'b0}};
assign s0_rresp = 2'b00;
assign s0_rlast = 1'b0;
assign s0_rvalid = 1'b0;

// Tie off slave 1 outputs
assign s1_awready = 1'b0;
assign s1_wready = 1'b0;
assign s1_bid = {ID_WIDTH{1'b0}};
assign s1_bresp = 2'b00;
assign s1_bvalid = 1'b0;
assign s1_arready = 1'b0;
assign s1_rid = {ID_WIDTH{1'b0}};
assign s1_rdata = {DATA_WIDTH{1'b0}};
assign s1_rresp = 2'b00;
assign s1_rlast = 1'b0;
assign s1_rvalid = 1'b0;

// Tie off slave 2 outputs
assign s2_awready = 1'b0;
assign s2_wready = 1'b0;
assign s2_bid = {ID_WIDTH{1'b0}};
assign s2_bresp = 2'b00;
assign s2_bvalid = 1'b0;
assign s2_arready = 1'b0;
assign s2_rid = {ID_WIDTH{1'b0}};
assign s2_rdata = {DATA_WIDTH{1'b0}};
assign s2_rresp = 2'b00;
assign s2_rlast = 1'b0;
assign s2_rvalid = 1'b0;

// Clock generation
initial begin
    aclk = 0;
    forever #5 aclk = ~aclk;
end

// Reset generation
initial begin
    aresetn = 0;
    #100;
    aresetn = 1;
end

// DUT instantiation
axi4_interconnect_m2s3 #(
    .DATA_WIDTH(DATA_WIDTH),
    .ADDR_WIDTH(ADDR_WIDTH),
    .ID_WIDTH(ID_WIDTH),
    .USER_WIDTH(1)
) dut (
    .aclk(aclk),
    .aresetn(aresetn),
    // Master 0 interface
    .m0_awid(m0_awid),
    .m0_awaddr(m0_awaddr),
    .m0_awlen(m0_awlen),
    .m0_awsize(m0_awsize),
    .m0_awburst(m0_awburst),
    .m0_awlock(m0_awlock),
    .m0_awcache(m0_awcache),
    .m0_awprot(m0_awprot),
    .m0_awqos(m0_awqos),
    .m0_awvalid(m0_awvalid),
    .m0_awready(m0_awready),
    .m0_wdata(m0_wdata),
    .m0_wstrb(m0_wstrb),
    .m0_wlast(m0_wlast),
    .m0_wvalid(m0_wvalid),
    .m0_wready(m0_wready),
    .m0_bid(m0_bid),
    .m0_bresp(m0_bresp),
    .m0_bvalid(m0_bvalid),
    .m0_bready(m0_bready),
    .m0_arid(m0_arid),
    .m0_araddr(m0_araddr),
    .m0_arlen(m0_arlen),
    .m0_arsize(m0_arsize),
    .m0_arburst(m0_arburst),
    .m0_arlock(m0_arlock),
    .m0_arcache(m0_arcache),
    .m0_arprot(m0_arprot),
    .m0_arqos(m0_arqos),
    .m0_arvalid(m0_arvalid),
    .m0_arready(m0_arready),
    .m0_rid(m0_rid),
    .m0_rdata(m0_rdata),
    .m0_rresp(m0_rresp),
    .m0_rlast(m0_rlast),
    .m0_rvalid(m0_rvalid),
    .m0_rready(m0_rready),
    // Master 1 interface
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
    // Slave 0 interface
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
    // Slave 1 interface
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
    // Slave 2 interface
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

// Test sequences
initial begin
    $dumpfile("axi4_interconnect.vcd");
    $dumpvars(0, tb_axi4_interconnect);
    
    // Wait for reset
    @(posedge aresetn);
    repeat(10) @(posedge aclk);
    
    // Test 1: Basic write transaction
    $display("Test 1: Basic write transaction");
    
    // Test 2: Basic read transaction
    $display("Test 2: Basic read transaction");
    
    // Test 3: 4KB boundary test
    $display("Test 3: 4KB boundary test");
    
    // Test 4: Access permission test
    $display("Test 4: Access permission test");
    
    // Test 5: QoS arbitration test
    $display("Test 5: QoS arbitration test");
    
    #1000;
    $finish;
end

endmodule
