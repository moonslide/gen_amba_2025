// Slave 1
assign slave_if[1].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s1_awid};
assign slave_if[1].awaddr  = s1_awaddr;
assign slave_if[1].awlen   = s1_awlen;
assign slave_if[1].awsize  = s1_awsize;
assign slave_if[1].awburst = s1_awburst;
assign slave_if[1].awlock  = s1_awlock;
assign slave_if[1].awcache = s1_awcache;
assign slave_if[1].awprot  = s1_awprot;
assign slave_if[1].awqos   = s1_awqos;
assign slave_if[1].awvalid = s1_awvalid;
assign s1_awready  = slave_if[1].awready;

assign slave_if[1].wdata   = s1_wdata;
assign slave_if[1].wstrb   = s1_wstrb;
assign slave_if[1].wlast   = s1_wlast;
assign slave_if[1].wvalid  = s1_wvalid;
assign s1_wready   = slave_if[1].wready;

assign s1_bid      = slave_if[1].bid[RTL_ID_WIDTH-1:0];
assign s1_bresp    = slave_if[1].bresp;
assign s1_bvalid   = slave_if[1].bvalid;
assign slave_if[1].bready  = s1_bready;

assign slave_if[1].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s1_arid};
assign slave_if[1].araddr  = s1_araddr;
assign slave_if[1].arlen   = s1_arlen;
assign slave_if[1].arsize  = s1_arsize;
assign slave_if[1].arburst = s1_arburst;
assign slave_if[1].arlock  = s1_arlock;
assign slave_if[1].arcache = s1_arcache;
assign slave_if[1].arprot  = s1_arprot;
assign slave_if[1].arqos   = s1_arqos;
assign slave_if[1].arvalid = s1_arvalid;
assign s1_arready  = slave_if[1].arready;

assign s1_rid      = slave_if[1].rid[RTL_ID_WIDTH-1:0];
assign s1_rdata    = slave_if[1].rdata;
assign s1_rresp    = slave_if[1].rresp;
assign s1_rlast    = slave_if[1].rlast;
assign s1_rvalid   = slave_if[1].rvalid;
assign slave_if[1].rready  = s1_rready;

// Slave 2
assign slave_if[2].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s2_awid};
assign slave_if[2].awaddr  = s2_awaddr;
assign slave_if[2].awlen   = s2_awlen;
assign slave_if[2].awsize  = s2_awsize;
assign slave_if[2].awburst = s2_awburst;
assign slave_if[2].awlock  = s2_awlock;
assign slave_if[2].awcache = s2_awcache;
assign slave_if[2].awprot  = s2_awprot;
assign slave_if[2].awqos   = s2_awqos;
assign slave_if[2].awvalid = s2_awvalid;
assign s2_awready  = slave_if[2].awready;

assign slave_if[2].wdata   = s2_wdata;
assign slave_if[2].wstrb   = s2_wstrb;
assign slave_if[2].wlast   = s2_wlast;
assign slave_if[2].wvalid  = s2_wvalid;
assign s2_wready   = slave_if[2].wready;

assign s2_bid      = slave_if[2].bid[RTL_ID_WIDTH-1:0];
assign s2_bresp    = slave_if[2].bresp;
assign s2_bvalid   = slave_if[2].bvalid;
assign slave_if[2].bready  = s2_bready;

assign slave_if[2].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s2_arid};
assign slave_if[2].araddr  = s2_araddr;
assign slave_if[2].arlen   = s2_arlen;
assign slave_if[2].arsize  = s2_arsize;
assign slave_if[2].arburst = s2_arburst;
assign slave_if[2].arlock  = s2_arlock;
assign slave_if[2].arcache = s2_arcache;
assign slave_if[2].arprot  = s2_arprot;
assign slave_if[2].arqos   = s2_arqos;
assign slave_if[2].arvalid = s2_arvalid;
assign s2_arready  = slave_if[2].arready;

assign s2_rid      = slave_if[2].rid[RTL_ID_WIDTH-1:0];
assign s2_rdata    = slave_if[2].rdata;
assign s2_rresp    = slave_if[2].rresp;
assign s2_rlast    = slave_if[2].rlast;
assign s2_rvalid   = slave_if[2].rvalid;
assign slave_if[2].rready  = s2_rready;

// Slave 3
assign slave_if[3].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s3_awid};
assign slave_if[3].awaddr  = s3_awaddr;
assign slave_if[3].awlen   = s3_awlen;
assign slave_if[3].awsize  = s3_awsize;
assign slave_if[3].awburst = s3_awburst;
assign slave_if[3].awlock  = s3_awlock;
assign slave_if[3].awcache = s3_awcache;
assign slave_if[3].awprot  = s3_awprot;
assign slave_if[3].awqos   = s3_awqos;
assign slave_if[3].awvalid = s3_awvalid;
assign s3_awready  = slave_if[3].awready;

assign slave_if[3].wdata   = s3_wdata;
assign slave_if[3].wstrb   = s3_wstrb;
assign slave_if[3].wlast   = s3_wlast;
assign slave_if[3].wvalid  = s3_wvalid;
assign s3_wready   = slave_if[3].wready;

assign s3_bid      = slave_if[3].bid[RTL_ID_WIDTH-1:0];
assign s3_bresp    = slave_if[3].bresp;
assign s3_bvalid   = slave_if[3].bvalid;
assign slave_if[3].bready  = s3_bready;

assign slave_if[3].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s3_arid};
assign slave_if[3].araddr  = s3_araddr;
assign slave_if[3].arlen   = s3_arlen;
assign slave_if[3].arsize  = s3_arsize;
assign slave_if[3].arburst = s3_arburst;
assign slave_if[3].arlock  = s3_arlock;
assign slave_if[3].arcache = s3_arcache;
assign slave_if[3].arprot  = s3_arprot;
assign slave_if[3].arqos   = s3_arqos;
assign slave_if[3].arvalid = s3_arvalid;
assign s3_arready  = slave_if[3].arready;

assign s3_rid      = slave_if[3].rid[RTL_ID_WIDTH-1:0];
assign s3_rdata    = slave_if[3].rdata;
assign s3_rresp    = slave_if[3].rresp;
assign s3_rlast    = slave_if[3].rlast;
assign s3_rvalid   = slave_if[3].rvalid;
assign slave_if[3].rready  = s3_rready;

// Slave 4
assign slave_if[4].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s4_awid};
assign slave_if[4].awaddr  = s4_awaddr;
assign slave_if[4].awlen   = s4_awlen;
assign slave_if[4].awsize  = s4_awsize;
assign slave_if[4].awburst = s4_awburst;
assign slave_if[4].awlock  = s4_awlock;
assign slave_if[4].awcache = s4_awcache;
assign slave_if[4].awprot  = s4_awprot;
assign slave_if[4].awqos   = s4_awqos;
assign slave_if[4].awvalid = s4_awvalid;
assign s4_awready  = slave_if[4].awready;

assign slave_if[4].wdata   = s4_wdata;
assign slave_if[4].wstrb   = s4_wstrb;
assign slave_if[4].wlast   = s4_wlast;
assign slave_if[4].wvalid  = s4_wvalid;
assign s4_wready   = slave_if[4].wready;

assign s4_bid      = slave_if[4].bid[RTL_ID_WIDTH-1:0];
assign s4_bresp    = slave_if[4].bresp;
assign s4_bvalid   = slave_if[4].bvalid;
assign slave_if[4].bready  = s4_bready;

assign slave_if[4].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s4_arid};
assign slave_if[4].araddr  = s4_araddr;
assign slave_if[4].arlen   = s4_arlen;
assign slave_if[4].arsize  = s4_arsize;
assign slave_if[4].arburst = s4_arburst;
assign slave_if[4].arlock  = s4_arlock;
assign slave_if[4].arcache = s4_arcache;
assign slave_if[4].arprot  = s4_arprot;
assign slave_if[4].arqos   = s4_arqos;
assign slave_if[4].arvalid = s4_arvalid;
assign s4_arready  = slave_if[4].arready;

assign s4_rid      = slave_if[4].rid[RTL_ID_WIDTH-1:0];
assign s4_rdata    = slave_if[4].rdata;
assign s4_rresp    = slave_if[4].rresp;
assign s4_rlast    = slave_if[4].rlast;
assign s4_rvalid   = slave_if[4].rvalid;
assign slave_if[4].rready  = s4_rready;

// Slave 5
assign slave_if[5].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s5_awid};
assign slave_if[5].awaddr  = s5_awaddr;
assign slave_if[5].awlen   = s5_awlen;
assign slave_if[5].awsize  = s5_awsize;
assign slave_if[5].awburst = s5_awburst;
assign slave_if[5].awlock  = s5_awlock;
assign slave_if[5].awcache = s5_awcache;
assign slave_if[5].awprot  = s5_awprot;
assign slave_if[5].awqos   = s5_awqos;
assign slave_if[5].awvalid = s5_awvalid;
assign s5_awready  = slave_if[5].awready;

assign slave_if[5].wdata   = s5_wdata;
assign slave_if[5].wstrb   = s5_wstrb;
assign slave_if[5].wlast   = s5_wlast;
assign slave_if[5].wvalid  = s5_wvalid;
assign s5_wready   = slave_if[5].wready;

assign s5_bid      = slave_if[5].bid[RTL_ID_WIDTH-1:0];
assign s5_bresp    = slave_if[5].bresp;
assign s5_bvalid   = slave_if[5].bvalid;
assign slave_if[5].bready  = s5_bready;

assign slave_if[5].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s5_arid};
assign slave_if[5].araddr  = s5_araddr;
assign slave_if[5].arlen   = s5_arlen;
assign slave_if[5].arsize  = s5_arsize;
assign slave_if[5].arburst = s5_arburst;
assign slave_if[5].arlock  = s5_arlock;
assign slave_if[5].arcache = s5_arcache;
assign slave_if[5].arprot  = s5_arprot;
assign slave_if[5].arqos   = s5_arqos;
assign slave_if[5].arvalid = s5_arvalid;
assign s5_arready  = slave_if[5].arready;

assign s5_rid      = slave_if[5].rid[RTL_ID_WIDTH-1:0];
assign s5_rdata    = slave_if[5].rdata;
assign s5_rresp    = slave_if[5].rresp;
assign s5_rlast    = slave_if[5].rlast;
assign s5_rvalid   = slave_if[5].rvalid;
assign slave_if[5].rready  = s5_rready;

// Slave 6
assign slave_if[6].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s6_awid};
assign slave_if[6].awaddr  = s6_awaddr;
assign slave_if[6].awlen   = s6_awlen;
assign slave_if[6].awsize  = s6_awsize;
assign slave_if[6].awburst = s6_awburst;
assign slave_if[6].awlock  = s6_awlock;
assign slave_if[6].awcache = s6_awcache;
assign slave_if[6].awprot  = s6_awprot;
assign slave_if[6].awqos   = s6_awqos;
assign slave_if[6].awvalid = s6_awvalid;
assign s6_awready  = slave_if[6].awready;

assign slave_if[6].wdata   = s6_wdata;
assign slave_if[6].wstrb   = s6_wstrb;
assign slave_if[6].wlast   = s6_wlast;
assign slave_if[6].wvalid  = s6_wvalid;
assign s6_wready   = slave_if[6].wready;

assign s6_bid      = slave_if[6].bid[RTL_ID_WIDTH-1:0];
assign s6_bresp    = slave_if[6].bresp;
assign s6_bvalid   = slave_if[6].bvalid;
assign slave_if[6].bready  = s6_bready;

assign slave_if[6].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s6_arid};
assign slave_if[6].araddr  = s6_araddr;
assign slave_if[6].arlen   = s6_arlen;
assign slave_if[6].arsize  = s6_arsize;
assign slave_if[6].arburst = s6_arburst;
assign slave_if[6].arlock  = s6_arlock;
assign slave_if[6].arcache = s6_arcache;
assign slave_if[6].arprot  = s6_arprot;
assign slave_if[6].arqos   = s6_arqos;
assign slave_if[6].arvalid = s6_arvalid;
assign s6_arready  = slave_if[6].arready;

assign s6_rid      = slave_if[6].rid[RTL_ID_WIDTH-1:0];
assign s6_rdata    = slave_if[6].rdata;
assign s6_rresp    = slave_if[6].rresp;
assign s6_rlast    = slave_if[6].rlast;
assign s6_rvalid   = slave_if[6].rvalid;
assign slave_if[6].rready  = s6_rready;

// Slave 7
assign slave_if[7].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s7_awid};
assign slave_if[7].awaddr  = s7_awaddr;
assign slave_if[7].awlen   = s7_awlen;
assign slave_if[7].awsize  = s7_awsize;
assign slave_if[7].awburst = s7_awburst;
assign slave_if[7].awlock  = s7_awlock;
assign slave_if[7].awcache = s7_awcache;
assign slave_if[7].awprot  = s7_awprot;
assign slave_if[7].awqos   = s7_awqos;
assign slave_if[7].awvalid = s7_awvalid;
assign s7_awready  = slave_if[7].awready;

assign slave_if[7].wdata   = s7_wdata;
assign slave_if[7].wstrb   = s7_wstrb;
assign slave_if[7].wlast   = s7_wlast;
assign slave_if[7].wvalid  = s7_wvalid;
assign s7_wready   = slave_if[7].wready;

assign s7_bid      = slave_if[7].bid[RTL_ID_WIDTH-1:0];
assign s7_bresp    = slave_if[7].bresp;
assign s7_bvalid   = slave_if[7].bvalid;
assign slave_if[7].bready  = s7_bready;

assign slave_if[7].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s7_arid};
assign slave_if[7].araddr  = s7_araddr;
assign slave_if[7].arlen   = s7_arlen;
assign slave_if[7].arsize  = s7_arsize;
assign slave_if[7].arburst = s7_arburst;
assign slave_if[7].arlock  = s7_arlock;
assign slave_if[7].arcache = s7_arcache;
assign slave_if[7].arprot  = s7_arprot;
assign slave_if[7].arqos   = s7_arqos;
assign slave_if[7].arvalid = s7_arvalid;
assign s7_arready  = slave_if[7].arready;

assign s7_rid      = slave_if[7].rid[RTL_ID_WIDTH-1:0];
assign s7_rdata    = slave_if[7].rdata;
assign s7_rresp    = slave_if[7].rresp;
assign s7_rlast    = slave_if[7].rlast;
assign s7_rvalid   = slave_if[7].rvalid;
assign slave_if[7].rready  = s7_rready;

// Slave 8
assign slave_if[8].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s8_awid};
assign slave_if[8].awaddr  = s8_awaddr;
assign slave_if[8].awlen   = s8_awlen;
assign slave_if[8].awsize  = s8_awsize;
assign slave_if[8].awburst = s8_awburst;
assign slave_if[8].awlock  = s8_awlock;
assign slave_if[8].awcache = s8_awcache;
assign slave_if[8].awprot  = s8_awprot;
assign slave_if[8].awqos   = s8_awqos;
assign slave_if[8].awvalid = s8_awvalid;
assign s8_awready  = slave_if[8].awready;

assign slave_if[8].wdata   = s8_wdata;
assign slave_if[8].wstrb   = s8_wstrb;
assign slave_if[8].wlast   = s8_wlast;
assign slave_if[8].wvalid  = s8_wvalid;
assign s8_wready   = slave_if[8].wready;

assign s8_bid      = slave_if[8].bid[RTL_ID_WIDTH-1:0];
assign s8_bresp    = slave_if[8].bresp;
assign s8_bvalid   = slave_if[8].bvalid;
assign slave_if[8].bready  = s8_bready;

assign slave_if[8].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s8_arid};
assign slave_if[8].araddr  = s8_araddr;
assign slave_if[8].arlen   = s8_arlen;
assign slave_if[8].arsize  = s8_arsize;
assign slave_if[8].arburst = s8_arburst;
assign slave_if[8].arlock  = s8_arlock;
assign slave_if[8].arcache = s8_arcache;
assign slave_if[8].arprot  = s8_arprot;
assign slave_if[8].arqos   = s8_arqos;
assign slave_if[8].arvalid = s8_arvalid;
assign s8_arready  = slave_if[8].arready;

assign s8_rid      = slave_if[8].rid[RTL_ID_WIDTH-1:0];
assign s8_rdata    = slave_if[8].rdata;
assign s8_rresp    = slave_if[8].rresp;
assign s8_rlast    = slave_if[8].rlast;
assign s8_rvalid   = slave_if[8].rvalid;
assign slave_if[8].rready  = s8_rready;

// Slave 9
assign slave_if[9].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s9_awid};
assign slave_if[9].awaddr  = s9_awaddr;
assign slave_if[9].awlen   = s9_awlen;
assign slave_if[9].awsize  = s9_awsize;
assign slave_if[9].awburst = s9_awburst;
assign slave_if[9].awlock  = s9_awlock;
assign slave_if[9].awcache = s9_awcache;
assign slave_if[9].awprot  = s9_awprot;
assign slave_if[9].awqos   = s9_awqos;
assign slave_if[9].awvalid = s9_awvalid;
assign s9_awready  = slave_if[9].awready;

assign slave_if[9].wdata   = s9_wdata;
assign slave_if[9].wstrb   = s9_wstrb;
assign slave_if[9].wlast   = s9_wlast;
assign slave_if[9].wvalid  = s9_wvalid;
assign s9_wready   = slave_if[9].wready;

assign s9_bid      = slave_if[9].bid[RTL_ID_WIDTH-1:0];
assign s9_bresp    = slave_if[9].bresp;
assign s9_bvalid   = slave_if[9].bvalid;
assign slave_if[9].bready  = s9_bready;

assign slave_if[9].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s9_arid};
assign slave_if[9].araddr  = s9_araddr;
assign slave_if[9].arlen   = s9_arlen;
assign slave_if[9].arsize  = s9_arsize;
assign slave_if[9].arburst = s9_arburst;
assign slave_if[9].arlock  = s9_arlock;
assign slave_if[9].arcache = s9_arcache;
assign slave_if[9].arprot  = s9_arprot;
assign slave_if[9].arqos   = s9_arqos;
assign slave_if[9].arvalid = s9_arvalid;
assign s9_arready  = slave_if[9].arready;

assign s9_rid      = slave_if[9].rid[RTL_ID_WIDTH-1:0];
assign s9_rdata    = slave_if[9].rdata;
assign s9_rresp    = slave_if[9].rresp;
assign s9_rlast    = slave_if[9].rlast;
assign s9_rvalid   = slave_if[9].rvalid;
assign slave_if[9].rready  = s9_rready;

// Slave 10
assign slave_if[10].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s10_awid};
assign slave_if[10].awaddr  = s10_awaddr;
assign slave_if[10].awlen   = s10_awlen;
assign slave_if[10].awsize  = s10_awsize;
assign slave_if[10].awburst = s10_awburst;
assign slave_if[10].awlock  = s10_awlock;
assign slave_if[10].awcache = s10_awcache;
assign slave_if[10].awprot  = s10_awprot;
assign slave_if[10].awqos   = s10_awqos;
assign slave_if[10].awvalid = s10_awvalid;
assign s10_awready  = slave_if[10].awready;

assign slave_if[10].wdata   = s10_wdata;
assign slave_if[10].wstrb   = s10_wstrb;
assign slave_if[10].wlast   = s10_wlast;
assign slave_if[10].wvalid  = s10_wvalid;
assign s10_wready   = slave_if[10].wready;

assign s10_bid      = slave_if[10].bid[RTL_ID_WIDTH-1:0];
assign s10_bresp    = slave_if[10].bresp;
assign s10_bvalid   = slave_if[10].bvalid;
assign slave_if[10].bready  = s10_bready;

assign slave_if[10].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s10_arid};
assign slave_if[10].araddr  = s10_araddr;
assign slave_if[10].arlen   = s10_arlen;
assign slave_if[10].arsize  = s10_arsize;
assign slave_if[10].arburst = s10_arburst;
assign slave_if[10].arlock  = s10_arlock;
assign slave_if[10].arcache = s10_arcache;
assign slave_if[10].arprot  = s10_arprot;
assign slave_if[10].arqos   = s10_arqos;
assign slave_if[10].arvalid = s10_arvalid;
assign s10_arready  = slave_if[10].arready;

assign s10_rid      = slave_if[10].rid[RTL_ID_WIDTH-1:0];
assign s10_rdata    = slave_if[10].rdata;
assign s10_rresp    = slave_if[10].rresp;
assign s10_rlast    = slave_if[10].rlast;
assign s10_rvalid   = slave_if[10].rvalid;
assign slave_if[10].rready  = s10_rready;

// Slave 11
assign slave_if[11].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s11_awid};
assign slave_if[11].awaddr  = s11_awaddr;
assign slave_if[11].awlen   = s11_awlen;
assign slave_if[11].awsize  = s11_awsize;
assign slave_if[11].awburst = s11_awburst;
assign slave_if[11].awlock  = s11_awlock;
assign slave_if[11].awcache = s11_awcache;
assign slave_if[11].awprot  = s11_awprot;
assign slave_if[11].awqos   = s11_awqos;
assign slave_if[11].awvalid = s11_awvalid;
assign s11_awready  = slave_if[11].awready;

assign slave_if[11].wdata   = s11_wdata;
assign slave_if[11].wstrb   = s11_wstrb;
assign slave_if[11].wlast   = s11_wlast;
assign slave_if[11].wvalid  = s11_wvalid;
assign s11_wready   = slave_if[11].wready;

assign s11_bid      = slave_if[11].bid[RTL_ID_WIDTH-1:0];
assign s11_bresp    = slave_if[11].bresp;
assign s11_bvalid   = slave_if[11].bvalid;
assign slave_if[11].bready  = s11_bready;

assign slave_if[11].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s11_arid};
assign slave_if[11].araddr  = s11_araddr;
assign slave_if[11].arlen   = s11_arlen;
assign slave_if[11].arsize  = s11_arsize;
assign slave_if[11].arburst = s11_arburst;
assign slave_if[11].arlock  = s11_arlock;
assign slave_if[11].arcache = s11_arcache;
assign slave_if[11].arprot  = s11_arprot;
assign slave_if[11].arqos   = s11_arqos;
assign slave_if[11].arvalid = s11_arvalid;
assign s11_arready  = slave_if[11].arready;

assign s11_rid      = slave_if[11].rid[RTL_ID_WIDTH-1:0];
assign s11_rdata    = slave_if[11].rdata;
assign s11_rresp    = slave_if[11].rresp;
assign s11_rlast    = slave_if[11].rlast;
assign s11_rvalid   = slave_if[11].rvalid;
assign slave_if[11].rready  = s11_rready;

// Slave 12
assign slave_if[12].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s12_awid};
assign slave_if[12].awaddr  = s12_awaddr;
assign slave_if[12].awlen   = s12_awlen;
assign slave_if[12].awsize  = s12_awsize;
assign slave_if[12].awburst = s12_awburst;
assign slave_if[12].awlock  = s12_awlock;
assign slave_if[12].awcache = s12_awcache;
assign slave_if[12].awprot  = s12_awprot;
assign slave_if[12].awqos   = s12_awqos;
assign slave_if[12].awvalid = s12_awvalid;
assign s12_awready  = slave_if[12].awready;

assign slave_if[12].wdata   = s12_wdata;
assign slave_if[12].wstrb   = s12_wstrb;
assign slave_if[12].wlast   = s12_wlast;
assign slave_if[12].wvalid  = s12_wvalid;
assign s12_wready   = slave_if[12].wready;

assign s12_bid      = slave_if[12].bid[RTL_ID_WIDTH-1:0];
assign s12_bresp    = slave_if[12].bresp;
assign s12_bvalid   = slave_if[12].bvalid;
assign slave_if[12].bready  = s12_bready;

assign slave_if[12].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s12_arid};
assign slave_if[12].araddr  = s12_araddr;
assign slave_if[12].arlen   = s12_arlen;
assign slave_if[12].arsize  = s12_arsize;
assign slave_if[12].arburst = s12_arburst;
assign slave_if[12].arlock  = s12_arlock;
assign slave_if[12].arcache = s12_arcache;
assign slave_if[12].arprot  = s12_arprot;
assign slave_if[12].arqos   = s12_arqos;
assign slave_if[12].arvalid = s12_arvalid;
assign s12_arready  = slave_if[12].arready;

assign s12_rid      = slave_if[12].rid[RTL_ID_WIDTH-1:0];
assign s12_rdata    = slave_if[12].rdata;
assign s12_rresp    = slave_if[12].rresp;
assign s12_rlast    = slave_if[12].rlast;
assign s12_rvalid   = slave_if[12].rvalid;
assign slave_if[12].rready  = s12_rready;

// Slave 13
assign slave_if[13].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s13_awid};
assign slave_if[13].awaddr  = s13_awaddr;
assign slave_if[13].awlen   = s13_awlen;
assign slave_if[13].awsize  = s13_awsize;
assign slave_if[13].awburst = s13_awburst;
assign slave_if[13].awlock  = s13_awlock;
assign slave_if[13].awcache = s13_awcache;
assign slave_if[13].awprot  = s13_awprot;
assign slave_if[13].awqos   = s13_awqos;
assign slave_if[13].awvalid = s13_awvalid;
assign s13_awready  = slave_if[13].awready;

assign slave_if[13].wdata   = s13_wdata;
assign slave_if[13].wstrb   = s13_wstrb;
assign slave_if[13].wlast   = s13_wlast;
assign slave_if[13].wvalid  = s13_wvalid;
assign s13_wready   = slave_if[13].wready;

assign s13_bid      = slave_if[13].bid[RTL_ID_WIDTH-1:0];
assign s13_bresp    = slave_if[13].bresp;
assign s13_bvalid   = slave_if[13].bvalid;
assign slave_if[13].bready  = s13_bready;

assign slave_if[13].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s13_arid};
assign slave_if[13].araddr  = s13_araddr;
assign slave_if[13].arlen   = s13_arlen;
assign slave_if[13].arsize  = s13_arsize;
assign slave_if[13].arburst = s13_arburst;
assign slave_if[13].arlock  = s13_arlock;
assign slave_if[13].arcache = s13_arcache;
assign slave_if[13].arprot  = s13_arprot;
assign slave_if[13].arqos   = s13_arqos;
assign slave_if[13].arvalid = s13_arvalid;
assign s13_arready  = slave_if[13].arready;

assign s13_rid      = slave_if[13].rid[RTL_ID_WIDTH-1:0];
assign s13_rdata    = slave_if[13].rdata;
assign s13_rresp    = slave_if[13].rresp;
assign s13_rlast    = slave_if[13].rlast;
assign s13_rvalid   = slave_if[13].rvalid;
assign slave_if[13].rready  = s13_rready;

// Slave 14
assign slave_if[14].awid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s14_awid};
assign slave_if[14].awaddr  = s14_awaddr;
assign slave_if[14].awlen   = s14_awlen;
assign slave_if[14].awsize  = s14_awsize;
assign slave_if[14].awburst = s14_awburst;
assign slave_if[14].awlock  = s14_awlock;
assign slave_if[14].awcache = s14_awcache;
assign slave_if[14].awprot  = s14_awprot;
assign slave_if[14].awqos   = s14_awqos;
assign slave_if[14].awvalid = s14_awvalid;
assign s14_awready  = slave_if[14].awready;

assign slave_if[14].wdata   = s14_wdata;
assign slave_if[14].wstrb   = s14_wstrb;
assign slave_if[14].wlast   = s14_wlast;
assign slave_if[14].wvalid  = s14_wvalid;
assign s14_wready   = slave_if[14].wready;

assign s14_bid      = slave_if[14].bid[RTL_ID_WIDTH-1:0];
assign s14_bresp    = slave_if[14].bresp;
assign s14_bvalid   = slave_if[14].bvalid;
assign slave_if[14].bready  = s14_bready;

assign slave_if[14].arid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, s14_arid};
assign slave_if[14].araddr  = s14_araddr;
assign slave_if[14].arlen   = s14_arlen;
assign slave_if[14].arsize  = s14_arsize;
assign slave_if[14].arburst = s14_arburst;
assign slave_if[14].arlock  = s14_arlock;
assign slave_if[14].arcache = s14_arcache;
assign slave_if[14].arprot  = s14_arprot;
assign slave_if[14].arqos   = s14_arqos;
assign slave_if[14].arvalid = s14_arvalid;
assign s14_arready  = slave_if[14].arready;

assign s14_rid      = slave_if[14].rid[RTL_ID_WIDTH-1:0];
assign s14_rdata    = slave_if[14].rdata;
assign s14_rresp    = slave_if[14].rresp;
assign s14_rlast    = slave_if[14].rlast;
assign s14_rvalid   = slave_if[14].rvalid;
assign slave_if[14].rready  = s14_rready;

