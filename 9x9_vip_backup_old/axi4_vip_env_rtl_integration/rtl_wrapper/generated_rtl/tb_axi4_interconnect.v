//==============================================================================
// Testbench for AXI4 Interconnect
//==============================================================================

`timescale 1ns/1ps

module tb_axi4_interconnect;

parameter DATA_WIDTH = 128;
parameter ADDR_WIDTH = 40;
parameter ID_WIDTH = 6;

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

// Master 2 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     m2_awid;
wire [ADDR_WIDTH-1:0]   m2_awaddr;
wire [7:0]              m2_awlen;
wire [2:0]              m2_awsize;
wire [1:0]              m2_awburst;
wire                    m2_awlock;
wire [3:0]              m2_awcache;
wire [2:0]              m2_awprot;
wire [3:0]              m2_awqos;
wire                    m2_awvalid;
wire                    m2_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   m2_wdata;
wire [DATA_WIDTH/8-1:0] m2_wstrb;
wire                    m2_wlast;
wire                    m2_wvalid;
wire                    m2_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     m2_bid;
wire [1:0]              m2_bresp;
wire                    m2_bvalid;
wire                    m2_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     m2_arid;
wire [ADDR_WIDTH-1:0]   m2_araddr;
wire [7:0]              m2_arlen;
wire [2:0]              m2_arsize;
wire [1:0]              m2_arburst;
wire                    m2_arlock;
wire [3:0]              m2_arcache;
wire [2:0]              m2_arprot;
wire [3:0]              m2_arqos;
wire                    m2_arvalid;
wire                    m2_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     m2_rid;
wire [DATA_WIDTH-1:0]   m2_rdata;
wire [1:0]              m2_rresp;
wire                    m2_rlast;
wire                    m2_rvalid;
wire                    m2_rready;

// Master 3 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     m3_awid;
wire [ADDR_WIDTH-1:0]   m3_awaddr;
wire [7:0]              m3_awlen;
wire [2:0]              m3_awsize;
wire [1:0]              m3_awburst;
wire                    m3_awlock;
wire [3:0]              m3_awcache;
wire [2:0]              m3_awprot;
wire [3:0]              m3_awqos;
wire                    m3_awvalid;
wire                    m3_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   m3_wdata;
wire [DATA_WIDTH/8-1:0] m3_wstrb;
wire                    m3_wlast;
wire                    m3_wvalid;
wire                    m3_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     m3_bid;
wire [1:0]              m3_bresp;
wire                    m3_bvalid;
wire                    m3_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     m3_arid;
wire [ADDR_WIDTH-1:0]   m3_araddr;
wire [7:0]              m3_arlen;
wire [2:0]              m3_arsize;
wire [1:0]              m3_arburst;
wire                    m3_arlock;
wire [3:0]              m3_arcache;
wire [2:0]              m3_arprot;
wire [3:0]              m3_arqos;
wire                    m3_arvalid;
wire                    m3_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     m3_rid;
wire [DATA_WIDTH-1:0]   m3_rdata;
wire [1:0]              m3_rresp;
wire                    m3_rlast;
wire                    m3_rvalid;
wire                    m3_rready;

// Master 4 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     m4_awid;
wire [ADDR_WIDTH-1:0]   m4_awaddr;
wire [7:0]              m4_awlen;
wire [2:0]              m4_awsize;
wire [1:0]              m4_awburst;
wire                    m4_awlock;
wire [3:0]              m4_awcache;
wire [2:0]              m4_awprot;
wire [3:0]              m4_awqos;
wire                    m4_awvalid;
wire                    m4_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   m4_wdata;
wire [DATA_WIDTH/8-1:0] m4_wstrb;
wire                    m4_wlast;
wire                    m4_wvalid;
wire                    m4_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     m4_bid;
wire [1:0]              m4_bresp;
wire                    m4_bvalid;
wire                    m4_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     m4_arid;
wire [ADDR_WIDTH-1:0]   m4_araddr;
wire [7:0]              m4_arlen;
wire [2:0]              m4_arsize;
wire [1:0]              m4_arburst;
wire                    m4_arlock;
wire [3:0]              m4_arcache;
wire [2:0]              m4_arprot;
wire [3:0]              m4_arqos;
wire                    m4_arvalid;
wire                    m4_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     m4_rid;
wire [DATA_WIDTH-1:0]   m4_rdata;
wire [1:0]              m4_rresp;
wire                    m4_rlast;
wire                    m4_rvalid;
wire                    m4_rready;

// Master 5 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     m5_awid;
wire [ADDR_WIDTH-1:0]   m5_awaddr;
wire [7:0]              m5_awlen;
wire [2:0]              m5_awsize;
wire [1:0]              m5_awburst;
wire                    m5_awlock;
wire [3:0]              m5_awcache;
wire [2:0]              m5_awprot;
wire [3:0]              m5_awqos;
wire                    m5_awvalid;
wire                    m5_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   m5_wdata;
wire [DATA_WIDTH/8-1:0] m5_wstrb;
wire                    m5_wlast;
wire                    m5_wvalid;
wire                    m5_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     m5_bid;
wire [1:0]              m5_bresp;
wire                    m5_bvalid;
wire                    m5_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     m5_arid;
wire [ADDR_WIDTH-1:0]   m5_araddr;
wire [7:0]              m5_arlen;
wire [2:0]              m5_arsize;
wire [1:0]              m5_arburst;
wire                    m5_arlock;
wire [3:0]              m5_arcache;
wire [2:0]              m5_arprot;
wire [3:0]              m5_arqos;
wire                    m5_arvalid;
wire                    m5_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     m5_rid;
wire [DATA_WIDTH-1:0]   m5_rdata;
wire [1:0]              m5_rresp;
wire                    m5_rlast;
wire                    m5_rvalid;
wire                    m5_rready;

// Master 6 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     m6_awid;
wire [ADDR_WIDTH-1:0]   m6_awaddr;
wire [7:0]              m6_awlen;
wire [2:0]              m6_awsize;
wire [1:0]              m6_awburst;
wire                    m6_awlock;
wire [3:0]              m6_awcache;
wire [2:0]              m6_awprot;
wire [3:0]              m6_awqos;
wire                    m6_awvalid;
wire                    m6_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   m6_wdata;
wire [DATA_WIDTH/8-1:0] m6_wstrb;
wire                    m6_wlast;
wire                    m6_wvalid;
wire                    m6_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     m6_bid;
wire [1:0]              m6_bresp;
wire                    m6_bvalid;
wire                    m6_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     m6_arid;
wire [ADDR_WIDTH-1:0]   m6_araddr;
wire [7:0]              m6_arlen;
wire [2:0]              m6_arsize;
wire [1:0]              m6_arburst;
wire                    m6_arlock;
wire [3:0]              m6_arcache;
wire [2:0]              m6_arprot;
wire [3:0]              m6_arqos;
wire                    m6_arvalid;
wire                    m6_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     m6_rid;
wire [DATA_WIDTH-1:0]   m6_rdata;
wire [1:0]              m6_rresp;
wire                    m6_rlast;
wire                    m6_rvalid;
wire                    m6_rready;

// Master 7 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     m7_awid;
wire [ADDR_WIDTH-1:0]   m7_awaddr;
wire [7:0]              m7_awlen;
wire [2:0]              m7_awsize;
wire [1:0]              m7_awburst;
wire                    m7_awlock;
wire [3:0]              m7_awcache;
wire [2:0]              m7_awprot;
wire [3:0]              m7_awqos;
wire                    m7_awvalid;
wire                    m7_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   m7_wdata;
wire [DATA_WIDTH/8-1:0] m7_wstrb;
wire                    m7_wlast;
wire                    m7_wvalid;
wire                    m7_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     m7_bid;
wire [1:0]              m7_bresp;
wire                    m7_bvalid;
wire                    m7_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     m7_arid;
wire [ADDR_WIDTH-1:0]   m7_araddr;
wire [7:0]              m7_arlen;
wire [2:0]              m7_arsize;
wire [1:0]              m7_arburst;
wire                    m7_arlock;
wire [3:0]              m7_arcache;
wire [2:0]              m7_arprot;
wire [3:0]              m7_arqos;
wire                    m7_arvalid;
wire                    m7_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     m7_rid;
wire [DATA_WIDTH-1:0]   m7_rdata;
wire [1:0]              m7_rresp;
wire                    m7_rlast;
wire                    m7_rvalid;
wire                    m7_rready;

// Master 8 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     m8_awid;
wire [ADDR_WIDTH-1:0]   m8_awaddr;
wire [7:0]              m8_awlen;
wire [2:0]              m8_awsize;
wire [1:0]              m8_awburst;
wire                    m8_awlock;
wire [3:0]              m8_awcache;
wire [2:0]              m8_awprot;
wire [3:0]              m8_awqos;
wire                    m8_awvalid;
wire                    m8_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   m8_wdata;
wire [DATA_WIDTH/8-1:0] m8_wstrb;
wire                    m8_wlast;
wire                    m8_wvalid;
wire                    m8_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     m8_bid;
wire [1:0]              m8_bresp;
wire                    m8_bvalid;
wire                    m8_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     m8_arid;
wire [ADDR_WIDTH-1:0]   m8_araddr;
wire [7:0]              m8_arlen;
wire [2:0]              m8_arsize;
wire [1:0]              m8_arburst;
wire                    m8_arlock;
wire [3:0]              m8_arcache;
wire [2:0]              m8_arprot;
wire [3:0]              m8_arqos;
wire                    m8_arvalid;
wire                    m8_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     m8_rid;
wire [DATA_WIDTH-1:0]   m8_rdata;
wire [1:0]              m8_rresp;
wire                    m8_rlast;
wire                    m8_rvalid;
wire                    m8_rready;

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

// Slave 3 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     s3_awid;
wire [ADDR_WIDTH-1:0]   s3_awaddr;
wire [7:0]              s3_awlen;
wire [2:0]              s3_awsize;
wire [1:0]              s3_awburst;
wire                    s3_awlock;
wire [3:0]              s3_awcache;
wire [2:0]              s3_awprot;
wire [3:0]              s3_awqos;
wire                    s3_awvalid;
wire                    s3_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   s3_wdata;
wire [DATA_WIDTH/8-1:0] s3_wstrb;
wire                    s3_wlast;
wire                    s3_wvalid;
wire                    s3_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     s3_bid;
wire [1:0]              s3_bresp;
wire                    s3_bvalid;
wire                    s3_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     s3_arid;
wire [ADDR_WIDTH-1:0]   s3_araddr;
wire [7:0]              s3_arlen;
wire [2:0]              s3_arsize;
wire [1:0]              s3_arburst;
wire                    s3_arlock;
wire [3:0]              s3_arcache;
wire [2:0]              s3_arprot;
wire [3:0]              s3_arqos;
wire                    s3_arvalid;
wire                    s3_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     s3_rid;
wire [DATA_WIDTH-1:0]   s3_rdata;
wire [1:0]              s3_rresp;
wire                    s3_rlast;
wire                    s3_rvalid;
wire                    s3_rready;

// Slave 4 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     s4_awid;
wire [ADDR_WIDTH-1:0]   s4_awaddr;
wire [7:0]              s4_awlen;
wire [2:0]              s4_awsize;
wire [1:0]              s4_awburst;
wire                    s4_awlock;
wire [3:0]              s4_awcache;
wire [2:0]              s4_awprot;
wire [3:0]              s4_awqos;
wire                    s4_awvalid;
wire                    s4_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   s4_wdata;
wire [DATA_WIDTH/8-1:0] s4_wstrb;
wire                    s4_wlast;
wire                    s4_wvalid;
wire                    s4_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     s4_bid;
wire [1:0]              s4_bresp;
wire                    s4_bvalid;
wire                    s4_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     s4_arid;
wire [ADDR_WIDTH-1:0]   s4_araddr;
wire [7:0]              s4_arlen;
wire [2:0]              s4_arsize;
wire [1:0]              s4_arburst;
wire                    s4_arlock;
wire [3:0]              s4_arcache;
wire [2:0]              s4_arprot;
wire [3:0]              s4_arqos;
wire                    s4_arvalid;
wire                    s4_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     s4_rid;
wire [DATA_WIDTH-1:0]   s4_rdata;
wire [1:0]              s4_rresp;
wire                    s4_rlast;
wire                    s4_rvalid;
wire                    s4_rready;

// Slave 5 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     s5_awid;
wire [ADDR_WIDTH-1:0]   s5_awaddr;
wire [7:0]              s5_awlen;
wire [2:0]              s5_awsize;
wire [1:0]              s5_awburst;
wire                    s5_awlock;
wire [3:0]              s5_awcache;
wire [2:0]              s5_awprot;
wire [3:0]              s5_awqos;
wire                    s5_awvalid;
wire                    s5_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   s5_wdata;
wire [DATA_WIDTH/8-1:0] s5_wstrb;
wire                    s5_wlast;
wire                    s5_wvalid;
wire                    s5_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     s5_bid;
wire [1:0]              s5_bresp;
wire                    s5_bvalid;
wire                    s5_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     s5_arid;
wire [ADDR_WIDTH-1:0]   s5_araddr;
wire [7:0]              s5_arlen;
wire [2:0]              s5_arsize;
wire [1:0]              s5_arburst;
wire                    s5_arlock;
wire [3:0]              s5_arcache;
wire [2:0]              s5_arprot;
wire [3:0]              s5_arqos;
wire                    s5_arvalid;
wire                    s5_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     s5_rid;
wire [DATA_WIDTH-1:0]   s5_rdata;
wire [1:0]              s5_rresp;
wire                    s5_rlast;
wire                    s5_rvalid;
wire                    s5_rready;

// Slave 6 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     s6_awid;
wire [ADDR_WIDTH-1:0]   s6_awaddr;
wire [7:0]              s6_awlen;
wire [2:0]              s6_awsize;
wire [1:0]              s6_awburst;
wire                    s6_awlock;
wire [3:0]              s6_awcache;
wire [2:0]              s6_awprot;
wire [3:0]              s6_awqos;
wire                    s6_awvalid;
wire                    s6_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   s6_wdata;
wire [DATA_WIDTH/8-1:0] s6_wstrb;
wire                    s6_wlast;
wire                    s6_wvalid;
wire                    s6_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     s6_bid;
wire [1:0]              s6_bresp;
wire                    s6_bvalid;
wire                    s6_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     s6_arid;
wire [ADDR_WIDTH-1:0]   s6_araddr;
wire [7:0]              s6_arlen;
wire [2:0]              s6_arsize;
wire [1:0]              s6_arburst;
wire                    s6_arlock;
wire [3:0]              s6_arcache;
wire [2:0]              s6_arprot;
wire [3:0]              s6_arqos;
wire                    s6_arvalid;
wire                    s6_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     s6_rid;
wire [DATA_WIDTH-1:0]   s6_rdata;
wire [1:0]              s6_rresp;
wire                    s6_rlast;
wire                    s6_rvalid;
wire                    s6_rready;

// Slave 7 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     s7_awid;
wire [ADDR_WIDTH-1:0]   s7_awaddr;
wire [7:0]              s7_awlen;
wire [2:0]              s7_awsize;
wire [1:0]              s7_awburst;
wire                    s7_awlock;
wire [3:0]              s7_awcache;
wire [2:0]              s7_awprot;
wire [3:0]              s7_awqos;
wire                    s7_awvalid;
wire                    s7_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   s7_wdata;
wire [DATA_WIDTH/8-1:0] s7_wstrb;
wire                    s7_wlast;
wire                    s7_wvalid;
wire                    s7_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     s7_bid;
wire [1:0]              s7_bresp;
wire                    s7_bvalid;
wire                    s7_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     s7_arid;
wire [ADDR_WIDTH-1:0]   s7_araddr;
wire [7:0]              s7_arlen;
wire [2:0]              s7_arsize;
wire [1:0]              s7_arburst;
wire                    s7_arlock;
wire [3:0]              s7_arcache;
wire [2:0]              s7_arprot;
wire [3:0]              s7_arqos;
wire                    s7_arvalid;
wire                    s7_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     s7_rid;
wire [DATA_WIDTH-1:0]   s7_rdata;
wire [1:0]              s7_rresp;
wire                    s7_rlast;
wire                    s7_rvalid;
wire                    s7_rready;

// Slave 8 interface signals
// Write Address Channel
wire [ID_WIDTH-1:0]     s8_awid;
wire [ADDR_WIDTH-1:0]   s8_awaddr;
wire [7:0]              s8_awlen;
wire [2:0]              s8_awsize;
wire [1:0]              s8_awburst;
wire                    s8_awlock;
wire [3:0]              s8_awcache;
wire [2:0]              s8_awprot;
wire [3:0]              s8_awqos;
wire                    s8_awvalid;
wire                    s8_awready;

// Write Data Channel
wire [DATA_WIDTH-1:0]   s8_wdata;
wire [DATA_WIDTH/8-1:0] s8_wstrb;
wire                    s8_wlast;
wire                    s8_wvalid;
wire                    s8_wready;

// Write Response Channel
wire [ID_WIDTH-1:0]     s8_bid;
wire [1:0]              s8_bresp;
wire                    s8_bvalid;
wire                    s8_bready;

// Read Address Channel
wire [ID_WIDTH-1:0]     s8_arid;
wire [ADDR_WIDTH-1:0]   s8_araddr;
wire [7:0]              s8_arlen;
wire [2:0]              s8_arsize;
wire [1:0]              s8_arburst;
wire                    s8_arlock;
wire [3:0]              s8_arcache;
wire [2:0]              s8_arprot;
wire [3:0]              s8_arqos;
wire                    s8_arvalid;
wire                    s8_arready;

// Read Data Channel
wire [ID_WIDTH-1:0]     s8_rid;
wire [DATA_WIDTH-1:0]   s8_rdata;
wire [1:0]              s8_rresp;
wire                    s8_rlast;
wire                    s8_rvalid;
wire                    s8_rready;

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

// Tie off master 2 inputs
assign m2_awid = {ID_WIDTH{1'b0}};
assign m2_awaddr = {ADDR_WIDTH{1'b0}};
assign m2_awlen = 8'd0;
assign m2_awsize = 3'd0;
assign m2_awburst = 2'b01;
assign m2_awlock = 1'b0;
assign m2_awcache = 4'b0000;
assign m2_awprot = 3'b000;
assign m2_awqos = 4'b0000;
assign m2_awvalid = 1'b0;
assign m2_wdata = {DATA_WIDTH{1'b0}};
assign m2_wstrb = {(DATA_WIDTH/8){1'b0}};
assign m2_wlast = 1'b0;
assign m2_wvalid = 1'b0;
assign m2_bready = 1'b1;
assign m2_arid = {ID_WIDTH{1'b0}};
assign m2_araddr = {ADDR_WIDTH{1'b0}};
assign m2_arlen = 8'd0;
assign m2_arsize = 3'd0;
assign m2_arburst = 2'b01;
assign m2_arlock = 1'b0;
assign m2_arcache = 4'b0000;
assign m2_arprot = 3'b000;
assign m2_arqos = 4'b0000;
assign m2_arvalid = 1'b0;
assign m2_rready = 1'b1;

// Tie off master 3 inputs
assign m3_awid = {ID_WIDTH{1'b0}};
assign m3_awaddr = {ADDR_WIDTH{1'b0}};
assign m3_awlen = 8'd0;
assign m3_awsize = 3'd0;
assign m3_awburst = 2'b01;
assign m3_awlock = 1'b0;
assign m3_awcache = 4'b0000;
assign m3_awprot = 3'b000;
assign m3_awqos = 4'b0000;
assign m3_awvalid = 1'b0;
assign m3_wdata = {DATA_WIDTH{1'b0}};
assign m3_wstrb = {(DATA_WIDTH/8){1'b0}};
assign m3_wlast = 1'b0;
assign m3_wvalid = 1'b0;
assign m3_bready = 1'b1;
assign m3_arid = {ID_WIDTH{1'b0}};
assign m3_araddr = {ADDR_WIDTH{1'b0}};
assign m3_arlen = 8'd0;
assign m3_arsize = 3'd0;
assign m3_arburst = 2'b01;
assign m3_arlock = 1'b0;
assign m3_arcache = 4'b0000;
assign m3_arprot = 3'b000;
assign m3_arqos = 4'b0000;
assign m3_arvalid = 1'b0;
assign m3_rready = 1'b1;

// Tie off master 4 inputs
assign m4_awid = {ID_WIDTH{1'b0}};
assign m4_awaddr = {ADDR_WIDTH{1'b0}};
assign m4_awlen = 8'd0;
assign m4_awsize = 3'd0;
assign m4_awburst = 2'b01;
assign m4_awlock = 1'b0;
assign m4_awcache = 4'b0000;
assign m4_awprot = 3'b000;
assign m4_awqos = 4'b0000;
assign m4_awvalid = 1'b0;
assign m4_wdata = {DATA_WIDTH{1'b0}};
assign m4_wstrb = {(DATA_WIDTH/8){1'b0}};
assign m4_wlast = 1'b0;
assign m4_wvalid = 1'b0;
assign m4_bready = 1'b1;
assign m4_arid = {ID_WIDTH{1'b0}};
assign m4_araddr = {ADDR_WIDTH{1'b0}};
assign m4_arlen = 8'd0;
assign m4_arsize = 3'd0;
assign m4_arburst = 2'b01;
assign m4_arlock = 1'b0;
assign m4_arcache = 4'b0000;
assign m4_arprot = 3'b000;
assign m4_arqos = 4'b0000;
assign m4_arvalid = 1'b0;
assign m4_rready = 1'b1;

// Tie off master 5 inputs
assign m5_awid = {ID_WIDTH{1'b0}};
assign m5_awaddr = {ADDR_WIDTH{1'b0}};
assign m5_awlen = 8'd0;
assign m5_awsize = 3'd0;
assign m5_awburst = 2'b01;
assign m5_awlock = 1'b0;
assign m5_awcache = 4'b0000;
assign m5_awprot = 3'b000;
assign m5_awqos = 4'b0000;
assign m5_awvalid = 1'b0;
assign m5_wdata = {DATA_WIDTH{1'b0}};
assign m5_wstrb = {(DATA_WIDTH/8){1'b0}};
assign m5_wlast = 1'b0;
assign m5_wvalid = 1'b0;
assign m5_bready = 1'b1;
assign m5_arid = {ID_WIDTH{1'b0}};
assign m5_araddr = {ADDR_WIDTH{1'b0}};
assign m5_arlen = 8'd0;
assign m5_arsize = 3'd0;
assign m5_arburst = 2'b01;
assign m5_arlock = 1'b0;
assign m5_arcache = 4'b0000;
assign m5_arprot = 3'b000;
assign m5_arqos = 4'b0000;
assign m5_arvalid = 1'b0;
assign m5_rready = 1'b1;

// Tie off master 6 inputs
assign m6_awid = {ID_WIDTH{1'b0}};
assign m6_awaddr = {ADDR_WIDTH{1'b0}};
assign m6_awlen = 8'd0;
assign m6_awsize = 3'd0;
assign m6_awburst = 2'b01;
assign m6_awlock = 1'b0;
assign m6_awcache = 4'b0000;
assign m6_awprot = 3'b000;
assign m6_awqos = 4'b0000;
assign m6_awvalid = 1'b0;
assign m6_wdata = {DATA_WIDTH{1'b0}};
assign m6_wstrb = {(DATA_WIDTH/8){1'b0}};
assign m6_wlast = 1'b0;
assign m6_wvalid = 1'b0;
assign m6_bready = 1'b1;
assign m6_arid = {ID_WIDTH{1'b0}};
assign m6_araddr = {ADDR_WIDTH{1'b0}};
assign m6_arlen = 8'd0;
assign m6_arsize = 3'd0;
assign m6_arburst = 2'b01;
assign m6_arlock = 1'b0;
assign m6_arcache = 4'b0000;
assign m6_arprot = 3'b000;
assign m6_arqos = 4'b0000;
assign m6_arvalid = 1'b0;
assign m6_rready = 1'b1;

// Tie off master 7 inputs
assign m7_awid = {ID_WIDTH{1'b0}};
assign m7_awaddr = {ADDR_WIDTH{1'b0}};
assign m7_awlen = 8'd0;
assign m7_awsize = 3'd0;
assign m7_awburst = 2'b01;
assign m7_awlock = 1'b0;
assign m7_awcache = 4'b0000;
assign m7_awprot = 3'b000;
assign m7_awqos = 4'b0000;
assign m7_awvalid = 1'b0;
assign m7_wdata = {DATA_WIDTH{1'b0}};
assign m7_wstrb = {(DATA_WIDTH/8){1'b0}};
assign m7_wlast = 1'b0;
assign m7_wvalid = 1'b0;
assign m7_bready = 1'b1;
assign m7_arid = {ID_WIDTH{1'b0}};
assign m7_araddr = {ADDR_WIDTH{1'b0}};
assign m7_arlen = 8'd0;
assign m7_arsize = 3'd0;
assign m7_arburst = 2'b01;
assign m7_arlock = 1'b0;
assign m7_arcache = 4'b0000;
assign m7_arprot = 3'b000;
assign m7_arqos = 4'b0000;
assign m7_arvalid = 1'b0;
assign m7_rready = 1'b1;

// Tie off master 8 inputs
assign m8_awid = {ID_WIDTH{1'b0}};
assign m8_awaddr = {ADDR_WIDTH{1'b0}};
assign m8_awlen = 8'd0;
assign m8_awsize = 3'd0;
assign m8_awburst = 2'b01;
assign m8_awlock = 1'b0;
assign m8_awcache = 4'b0000;
assign m8_awprot = 3'b000;
assign m8_awqos = 4'b0000;
assign m8_awvalid = 1'b0;
assign m8_wdata = {DATA_WIDTH{1'b0}};
assign m8_wstrb = {(DATA_WIDTH/8){1'b0}};
assign m8_wlast = 1'b0;
assign m8_wvalid = 1'b0;
assign m8_bready = 1'b1;
assign m8_arid = {ID_WIDTH{1'b0}};
assign m8_araddr = {ADDR_WIDTH{1'b0}};
assign m8_arlen = 8'd0;
assign m8_arsize = 3'd0;
assign m8_arburst = 2'b01;
assign m8_arlock = 1'b0;
assign m8_arcache = 4'b0000;
assign m8_arprot = 3'b000;
assign m8_arqos = 4'b0000;
assign m8_arvalid = 1'b0;
assign m8_rready = 1'b1;

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

// Tie off slave 3 outputs
assign s3_awready = 1'b0;
assign s3_wready = 1'b0;
assign s3_bid = {ID_WIDTH{1'b0}};
assign s3_bresp = 2'b00;
assign s3_bvalid = 1'b0;
assign s3_arready = 1'b0;
assign s3_rid = {ID_WIDTH{1'b0}};
assign s3_rdata = {DATA_WIDTH{1'b0}};
assign s3_rresp = 2'b00;
assign s3_rlast = 1'b0;
assign s3_rvalid = 1'b0;

// Tie off slave 4 outputs
assign s4_awready = 1'b0;
assign s4_wready = 1'b0;
assign s4_bid = {ID_WIDTH{1'b0}};
assign s4_bresp = 2'b00;
assign s4_bvalid = 1'b0;
assign s4_arready = 1'b0;
assign s4_rid = {ID_WIDTH{1'b0}};
assign s4_rdata = {DATA_WIDTH{1'b0}};
assign s4_rresp = 2'b00;
assign s4_rlast = 1'b0;
assign s4_rvalid = 1'b0;

// Tie off slave 5 outputs
assign s5_awready = 1'b0;
assign s5_wready = 1'b0;
assign s5_bid = {ID_WIDTH{1'b0}};
assign s5_bresp = 2'b00;
assign s5_bvalid = 1'b0;
assign s5_arready = 1'b0;
assign s5_rid = {ID_WIDTH{1'b0}};
assign s5_rdata = {DATA_WIDTH{1'b0}};
assign s5_rresp = 2'b00;
assign s5_rlast = 1'b0;
assign s5_rvalid = 1'b0;

// Tie off slave 6 outputs
assign s6_awready = 1'b0;
assign s6_wready = 1'b0;
assign s6_bid = {ID_WIDTH{1'b0}};
assign s6_bresp = 2'b00;
assign s6_bvalid = 1'b0;
assign s6_arready = 1'b0;
assign s6_rid = {ID_WIDTH{1'b0}};
assign s6_rdata = {DATA_WIDTH{1'b0}};
assign s6_rresp = 2'b00;
assign s6_rlast = 1'b0;
assign s6_rvalid = 1'b0;

// Tie off slave 7 outputs
assign s7_awready = 1'b0;
assign s7_wready = 1'b0;
assign s7_bid = {ID_WIDTH{1'b0}};
assign s7_bresp = 2'b00;
assign s7_bvalid = 1'b0;
assign s7_arready = 1'b0;
assign s7_rid = {ID_WIDTH{1'b0}};
assign s7_rdata = {DATA_WIDTH{1'b0}};
assign s7_rresp = 2'b00;
assign s7_rlast = 1'b0;
assign s7_rvalid = 1'b0;

// Tie off slave 8 outputs
assign s8_awready = 1'b0;
assign s8_wready = 1'b0;
assign s8_bid = {ID_WIDTH{1'b0}};
assign s8_bresp = 2'b00;
assign s8_bvalid = 1'b0;
assign s8_arready = 1'b0;
assign s8_rid = {ID_WIDTH{1'b0}};
assign s8_rdata = {DATA_WIDTH{1'b0}};
assign s8_rresp = 2'b00;
assign s8_rlast = 1'b0;
assign s8_rvalid = 1'b0;

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
axi4_interconnect_m9s9 #(
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
    // Master 2 interface
    .m2_awid(m2_awid),
    .m2_awaddr(m2_awaddr),
    .m2_awlen(m2_awlen),
    .m2_awsize(m2_awsize),
    .m2_awburst(m2_awburst),
    .m2_awlock(m2_awlock),
    .m2_awcache(m2_awcache),
    .m2_awprot(m2_awprot),
    .m2_awqos(m2_awqos),
    .m2_awvalid(m2_awvalid),
    .m2_awready(m2_awready),
    .m2_wdata(m2_wdata),
    .m2_wstrb(m2_wstrb),
    .m2_wlast(m2_wlast),
    .m2_wvalid(m2_wvalid),
    .m2_wready(m2_wready),
    .m2_bid(m2_bid),
    .m2_bresp(m2_bresp),
    .m2_bvalid(m2_bvalid),
    .m2_bready(m2_bready),
    .m2_arid(m2_arid),
    .m2_araddr(m2_araddr),
    .m2_arlen(m2_arlen),
    .m2_arsize(m2_arsize),
    .m2_arburst(m2_arburst),
    .m2_arlock(m2_arlock),
    .m2_arcache(m2_arcache),
    .m2_arprot(m2_arprot),
    .m2_arqos(m2_arqos),
    .m2_arvalid(m2_arvalid),
    .m2_arready(m2_arready),
    .m2_rid(m2_rid),
    .m2_rdata(m2_rdata),
    .m2_rresp(m2_rresp),
    .m2_rlast(m2_rlast),
    .m2_rvalid(m2_rvalid),
    .m2_rready(m2_rready),
    // Master 3 interface
    .m3_awid(m3_awid),
    .m3_awaddr(m3_awaddr),
    .m3_awlen(m3_awlen),
    .m3_awsize(m3_awsize),
    .m3_awburst(m3_awburst),
    .m3_awlock(m3_awlock),
    .m3_awcache(m3_awcache),
    .m3_awprot(m3_awprot),
    .m3_awqos(m3_awqos),
    .m3_awvalid(m3_awvalid),
    .m3_awready(m3_awready),
    .m3_wdata(m3_wdata),
    .m3_wstrb(m3_wstrb),
    .m3_wlast(m3_wlast),
    .m3_wvalid(m3_wvalid),
    .m3_wready(m3_wready),
    .m3_bid(m3_bid),
    .m3_bresp(m3_bresp),
    .m3_bvalid(m3_bvalid),
    .m3_bready(m3_bready),
    .m3_arid(m3_arid),
    .m3_araddr(m3_araddr),
    .m3_arlen(m3_arlen),
    .m3_arsize(m3_arsize),
    .m3_arburst(m3_arburst),
    .m3_arlock(m3_arlock),
    .m3_arcache(m3_arcache),
    .m3_arprot(m3_arprot),
    .m3_arqos(m3_arqos),
    .m3_arvalid(m3_arvalid),
    .m3_arready(m3_arready),
    .m3_rid(m3_rid),
    .m3_rdata(m3_rdata),
    .m3_rresp(m3_rresp),
    .m3_rlast(m3_rlast),
    .m3_rvalid(m3_rvalid),
    .m3_rready(m3_rready),
    // Master 4 interface
    .m4_awid(m4_awid),
    .m4_awaddr(m4_awaddr),
    .m4_awlen(m4_awlen),
    .m4_awsize(m4_awsize),
    .m4_awburst(m4_awburst),
    .m4_awlock(m4_awlock),
    .m4_awcache(m4_awcache),
    .m4_awprot(m4_awprot),
    .m4_awqos(m4_awqos),
    .m4_awvalid(m4_awvalid),
    .m4_awready(m4_awready),
    .m4_wdata(m4_wdata),
    .m4_wstrb(m4_wstrb),
    .m4_wlast(m4_wlast),
    .m4_wvalid(m4_wvalid),
    .m4_wready(m4_wready),
    .m4_bid(m4_bid),
    .m4_bresp(m4_bresp),
    .m4_bvalid(m4_bvalid),
    .m4_bready(m4_bready),
    .m4_arid(m4_arid),
    .m4_araddr(m4_araddr),
    .m4_arlen(m4_arlen),
    .m4_arsize(m4_arsize),
    .m4_arburst(m4_arburst),
    .m4_arlock(m4_arlock),
    .m4_arcache(m4_arcache),
    .m4_arprot(m4_arprot),
    .m4_arqos(m4_arqos),
    .m4_arvalid(m4_arvalid),
    .m4_arready(m4_arready),
    .m4_rid(m4_rid),
    .m4_rdata(m4_rdata),
    .m4_rresp(m4_rresp),
    .m4_rlast(m4_rlast),
    .m4_rvalid(m4_rvalid),
    .m4_rready(m4_rready),
    // Master 5 interface
    .m5_awid(m5_awid),
    .m5_awaddr(m5_awaddr),
    .m5_awlen(m5_awlen),
    .m5_awsize(m5_awsize),
    .m5_awburst(m5_awburst),
    .m5_awlock(m5_awlock),
    .m5_awcache(m5_awcache),
    .m5_awprot(m5_awprot),
    .m5_awqos(m5_awqos),
    .m5_awvalid(m5_awvalid),
    .m5_awready(m5_awready),
    .m5_wdata(m5_wdata),
    .m5_wstrb(m5_wstrb),
    .m5_wlast(m5_wlast),
    .m5_wvalid(m5_wvalid),
    .m5_wready(m5_wready),
    .m5_bid(m5_bid),
    .m5_bresp(m5_bresp),
    .m5_bvalid(m5_bvalid),
    .m5_bready(m5_bready),
    .m5_arid(m5_arid),
    .m5_araddr(m5_araddr),
    .m5_arlen(m5_arlen),
    .m5_arsize(m5_arsize),
    .m5_arburst(m5_arburst),
    .m5_arlock(m5_arlock),
    .m5_arcache(m5_arcache),
    .m5_arprot(m5_arprot),
    .m5_arqos(m5_arqos),
    .m5_arvalid(m5_arvalid),
    .m5_arready(m5_arready),
    .m5_rid(m5_rid),
    .m5_rdata(m5_rdata),
    .m5_rresp(m5_rresp),
    .m5_rlast(m5_rlast),
    .m5_rvalid(m5_rvalid),
    .m5_rready(m5_rready),
    // Master 6 interface
    .m6_awid(m6_awid),
    .m6_awaddr(m6_awaddr),
    .m6_awlen(m6_awlen),
    .m6_awsize(m6_awsize),
    .m6_awburst(m6_awburst),
    .m6_awlock(m6_awlock),
    .m6_awcache(m6_awcache),
    .m6_awprot(m6_awprot),
    .m6_awqos(m6_awqos),
    .m6_awvalid(m6_awvalid),
    .m6_awready(m6_awready),
    .m6_wdata(m6_wdata),
    .m6_wstrb(m6_wstrb),
    .m6_wlast(m6_wlast),
    .m6_wvalid(m6_wvalid),
    .m6_wready(m6_wready),
    .m6_bid(m6_bid),
    .m6_bresp(m6_bresp),
    .m6_bvalid(m6_bvalid),
    .m6_bready(m6_bready),
    .m6_arid(m6_arid),
    .m6_araddr(m6_araddr),
    .m6_arlen(m6_arlen),
    .m6_arsize(m6_arsize),
    .m6_arburst(m6_arburst),
    .m6_arlock(m6_arlock),
    .m6_arcache(m6_arcache),
    .m6_arprot(m6_arprot),
    .m6_arqos(m6_arqos),
    .m6_arvalid(m6_arvalid),
    .m6_arready(m6_arready),
    .m6_rid(m6_rid),
    .m6_rdata(m6_rdata),
    .m6_rresp(m6_rresp),
    .m6_rlast(m6_rlast),
    .m6_rvalid(m6_rvalid),
    .m6_rready(m6_rready),
    // Master 7 interface
    .m7_awid(m7_awid),
    .m7_awaddr(m7_awaddr),
    .m7_awlen(m7_awlen),
    .m7_awsize(m7_awsize),
    .m7_awburst(m7_awburst),
    .m7_awlock(m7_awlock),
    .m7_awcache(m7_awcache),
    .m7_awprot(m7_awprot),
    .m7_awqos(m7_awqos),
    .m7_awvalid(m7_awvalid),
    .m7_awready(m7_awready),
    .m7_wdata(m7_wdata),
    .m7_wstrb(m7_wstrb),
    .m7_wlast(m7_wlast),
    .m7_wvalid(m7_wvalid),
    .m7_wready(m7_wready),
    .m7_bid(m7_bid),
    .m7_bresp(m7_bresp),
    .m7_bvalid(m7_bvalid),
    .m7_bready(m7_bready),
    .m7_arid(m7_arid),
    .m7_araddr(m7_araddr),
    .m7_arlen(m7_arlen),
    .m7_arsize(m7_arsize),
    .m7_arburst(m7_arburst),
    .m7_arlock(m7_arlock),
    .m7_arcache(m7_arcache),
    .m7_arprot(m7_arprot),
    .m7_arqos(m7_arqos),
    .m7_arvalid(m7_arvalid),
    .m7_arready(m7_arready),
    .m7_rid(m7_rid),
    .m7_rdata(m7_rdata),
    .m7_rresp(m7_rresp),
    .m7_rlast(m7_rlast),
    .m7_rvalid(m7_rvalid),
    .m7_rready(m7_rready),
    // Master 8 interface
    .m8_awid(m8_awid),
    .m8_awaddr(m8_awaddr),
    .m8_awlen(m8_awlen),
    .m8_awsize(m8_awsize),
    .m8_awburst(m8_awburst),
    .m8_awlock(m8_awlock),
    .m8_awcache(m8_awcache),
    .m8_awprot(m8_awprot),
    .m8_awqos(m8_awqos),
    .m8_awvalid(m8_awvalid),
    .m8_awready(m8_awready),
    .m8_wdata(m8_wdata),
    .m8_wstrb(m8_wstrb),
    .m8_wlast(m8_wlast),
    .m8_wvalid(m8_wvalid),
    .m8_wready(m8_wready),
    .m8_bid(m8_bid),
    .m8_bresp(m8_bresp),
    .m8_bvalid(m8_bvalid),
    .m8_bready(m8_bready),
    .m8_arid(m8_arid),
    .m8_araddr(m8_araddr),
    .m8_arlen(m8_arlen),
    .m8_arsize(m8_arsize),
    .m8_arburst(m8_arburst),
    .m8_arlock(m8_arlock),
    .m8_arcache(m8_arcache),
    .m8_arprot(m8_arprot),
    .m8_arqos(m8_arqos),
    .m8_arvalid(m8_arvalid),
    .m8_arready(m8_arready),
    .m8_rid(m8_rid),
    .m8_rdata(m8_rdata),
    .m8_rresp(m8_rresp),
    .m8_rlast(m8_rlast),
    .m8_rvalid(m8_rvalid),
    .m8_rready(m8_rready),
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
    .s2_rready(s2_rready),
    // Slave 3 interface
    .s3_awid(s3_awid),
    .s3_awaddr(s3_awaddr),
    .s3_awlen(s3_awlen),
    .s3_awsize(s3_awsize),
    .s3_awburst(s3_awburst),
    .s3_awlock(s3_awlock),
    .s3_awcache(s3_awcache),
    .s3_awprot(s3_awprot),
    .s3_awqos(s3_awqos),
    .s3_awvalid(s3_awvalid),
    .s3_awready(s3_awready),
    .s3_wdata(s3_wdata),
    .s3_wstrb(s3_wstrb),
    .s3_wlast(s3_wlast),
    .s3_wvalid(s3_wvalid),
    .s3_wready(s3_wready),
    .s3_bid(s3_bid),
    .s3_bresp(s3_bresp),
    .s3_bvalid(s3_bvalid),
    .s3_bready(s3_bready),
    .s3_arid(s3_arid),
    .s3_araddr(s3_araddr),
    .s3_arlen(s3_arlen),
    .s3_arsize(s3_arsize),
    .s3_arburst(s3_arburst),
    .s3_arlock(s3_arlock),
    .s3_arcache(s3_arcache),
    .s3_arprot(s3_arprot),
    .s3_arqos(s3_arqos),
    .s3_arvalid(s3_arvalid),
    .s3_arready(s3_arready),
    .s3_rid(s3_rid),
    .s3_rdata(s3_rdata),
    .s3_rresp(s3_rresp),
    .s3_rlast(s3_rlast),
    .s3_rvalid(s3_rvalid),
    .s3_rready(s3_rready),
    // Slave 4 interface
    .s4_awid(s4_awid),
    .s4_awaddr(s4_awaddr),
    .s4_awlen(s4_awlen),
    .s4_awsize(s4_awsize),
    .s4_awburst(s4_awburst),
    .s4_awlock(s4_awlock),
    .s4_awcache(s4_awcache),
    .s4_awprot(s4_awprot),
    .s4_awqos(s4_awqos),
    .s4_awvalid(s4_awvalid),
    .s4_awready(s4_awready),
    .s4_wdata(s4_wdata),
    .s4_wstrb(s4_wstrb),
    .s4_wlast(s4_wlast),
    .s4_wvalid(s4_wvalid),
    .s4_wready(s4_wready),
    .s4_bid(s4_bid),
    .s4_bresp(s4_bresp),
    .s4_bvalid(s4_bvalid),
    .s4_bready(s4_bready),
    .s4_arid(s4_arid),
    .s4_araddr(s4_araddr),
    .s4_arlen(s4_arlen),
    .s4_arsize(s4_arsize),
    .s4_arburst(s4_arburst),
    .s4_arlock(s4_arlock),
    .s4_arcache(s4_arcache),
    .s4_arprot(s4_arprot),
    .s4_arqos(s4_arqos),
    .s4_arvalid(s4_arvalid),
    .s4_arready(s4_arready),
    .s4_rid(s4_rid),
    .s4_rdata(s4_rdata),
    .s4_rresp(s4_rresp),
    .s4_rlast(s4_rlast),
    .s4_rvalid(s4_rvalid),
    .s4_rready(s4_rready),
    // Slave 5 interface
    .s5_awid(s5_awid),
    .s5_awaddr(s5_awaddr),
    .s5_awlen(s5_awlen),
    .s5_awsize(s5_awsize),
    .s5_awburst(s5_awburst),
    .s5_awlock(s5_awlock),
    .s5_awcache(s5_awcache),
    .s5_awprot(s5_awprot),
    .s5_awqos(s5_awqos),
    .s5_awvalid(s5_awvalid),
    .s5_awready(s5_awready),
    .s5_wdata(s5_wdata),
    .s5_wstrb(s5_wstrb),
    .s5_wlast(s5_wlast),
    .s5_wvalid(s5_wvalid),
    .s5_wready(s5_wready),
    .s5_bid(s5_bid),
    .s5_bresp(s5_bresp),
    .s5_bvalid(s5_bvalid),
    .s5_bready(s5_bready),
    .s5_arid(s5_arid),
    .s5_araddr(s5_araddr),
    .s5_arlen(s5_arlen),
    .s5_arsize(s5_arsize),
    .s5_arburst(s5_arburst),
    .s5_arlock(s5_arlock),
    .s5_arcache(s5_arcache),
    .s5_arprot(s5_arprot),
    .s5_arqos(s5_arqos),
    .s5_arvalid(s5_arvalid),
    .s5_arready(s5_arready),
    .s5_rid(s5_rid),
    .s5_rdata(s5_rdata),
    .s5_rresp(s5_rresp),
    .s5_rlast(s5_rlast),
    .s5_rvalid(s5_rvalid),
    .s5_rready(s5_rready),
    // Slave 6 interface
    .s6_awid(s6_awid),
    .s6_awaddr(s6_awaddr),
    .s6_awlen(s6_awlen),
    .s6_awsize(s6_awsize),
    .s6_awburst(s6_awburst),
    .s6_awlock(s6_awlock),
    .s6_awcache(s6_awcache),
    .s6_awprot(s6_awprot),
    .s6_awqos(s6_awqos),
    .s6_awvalid(s6_awvalid),
    .s6_awready(s6_awready),
    .s6_wdata(s6_wdata),
    .s6_wstrb(s6_wstrb),
    .s6_wlast(s6_wlast),
    .s6_wvalid(s6_wvalid),
    .s6_wready(s6_wready),
    .s6_bid(s6_bid),
    .s6_bresp(s6_bresp),
    .s6_bvalid(s6_bvalid),
    .s6_bready(s6_bready),
    .s6_arid(s6_arid),
    .s6_araddr(s6_araddr),
    .s6_arlen(s6_arlen),
    .s6_arsize(s6_arsize),
    .s6_arburst(s6_arburst),
    .s6_arlock(s6_arlock),
    .s6_arcache(s6_arcache),
    .s6_arprot(s6_arprot),
    .s6_arqos(s6_arqos),
    .s6_arvalid(s6_arvalid),
    .s6_arready(s6_arready),
    .s6_rid(s6_rid),
    .s6_rdata(s6_rdata),
    .s6_rresp(s6_rresp),
    .s6_rlast(s6_rlast),
    .s6_rvalid(s6_rvalid),
    .s6_rready(s6_rready),
    // Slave 7 interface
    .s7_awid(s7_awid),
    .s7_awaddr(s7_awaddr),
    .s7_awlen(s7_awlen),
    .s7_awsize(s7_awsize),
    .s7_awburst(s7_awburst),
    .s7_awlock(s7_awlock),
    .s7_awcache(s7_awcache),
    .s7_awprot(s7_awprot),
    .s7_awqos(s7_awqos),
    .s7_awvalid(s7_awvalid),
    .s7_awready(s7_awready),
    .s7_wdata(s7_wdata),
    .s7_wstrb(s7_wstrb),
    .s7_wlast(s7_wlast),
    .s7_wvalid(s7_wvalid),
    .s7_wready(s7_wready),
    .s7_bid(s7_bid),
    .s7_bresp(s7_bresp),
    .s7_bvalid(s7_bvalid),
    .s7_bready(s7_bready),
    .s7_arid(s7_arid),
    .s7_araddr(s7_araddr),
    .s7_arlen(s7_arlen),
    .s7_arsize(s7_arsize),
    .s7_arburst(s7_arburst),
    .s7_arlock(s7_arlock),
    .s7_arcache(s7_arcache),
    .s7_arprot(s7_arprot),
    .s7_arqos(s7_arqos),
    .s7_arvalid(s7_arvalid),
    .s7_arready(s7_arready),
    .s7_rid(s7_rid),
    .s7_rdata(s7_rdata),
    .s7_rresp(s7_rresp),
    .s7_rlast(s7_rlast),
    .s7_rvalid(s7_rvalid),
    .s7_rready(s7_rready),
    // Slave 8 interface
    .s8_awid(s8_awid),
    .s8_awaddr(s8_awaddr),
    .s8_awlen(s8_awlen),
    .s8_awsize(s8_awsize),
    .s8_awburst(s8_awburst),
    .s8_awlock(s8_awlock),
    .s8_awcache(s8_awcache),
    .s8_awprot(s8_awprot),
    .s8_awqos(s8_awqos),
    .s8_awvalid(s8_awvalid),
    .s8_awready(s8_awready),
    .s8_wdata(s8_wdata),
    .s8_wstrb(s8_wstrb),
    .s8_wlast(s8_wlast),
    .s8_wvalid(s8_wvalid),
    .s8_wready(s8_wready),
    .s8_bid(s8_bid),
    .s8_bresp(s8_bresp),
    .s8_bvalid(s8_bvalid),
    .s8_bready(s8_bready),
    .s8_arid(s8_arid),
    .s8_araddr(s8_araddr),
    .s8_arlen(s8_arlen),
    .s8_arsize(s8_arsize),
    .s8_arburst(s8_arburst),
    .s8_arlock(s8_arlock),
    .s8_arcache(s8_arcache),
    .s8_arprot(s8_arprot),
    .s8_arqos(s8_arqos),
    .s8_arvalid(s8_arvalid),
    .s8_arready(s8_arready),
    .s8_rid(s8_rid),
    .s8_rdata(s8_rdata),
    .s8_rresp(s8_rresp),
    .s8_rlast(s8_rlast),
    .s8_rvalid(s8_rvalid),
    .s8_rready(s8_rready)
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
