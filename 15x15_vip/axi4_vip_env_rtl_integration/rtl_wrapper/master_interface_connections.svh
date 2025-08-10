// Master 1
assign m1_awid     = master_if[1].awid[RTL_ID_WIDTH-1:0];
assign m1_awaddr   = master_if[1].awaddr;
assign m1_awlen    = master_if[1].awlen;
assign m1_awsize   = master_if[1].awsize;
assign m1_awburst  = master_if[1].awburst;
assign m1_awlock   = master_if[1].awlock;
assign m1_awcache  = master_if[1].awcache;
assign m1_awprot   = master_if[1].awprot;
assign m1_awqos    = master_if[1].awqos;
assign m1_awvalid  = master_if[1].awvalid;
assign master_if[1].awready = m1_awready;

assign m1_wdata    = master_if[1].wdata;
assign m1_wstrb    = master_if[1].wstrb;
assign m1_wlast    = master_if[1].wlast;
assign m1_wvalid   = master_if[1].wvalid;
assign master_if[1].wready = m1_wready;

assign master_if[1].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m1_bid};
assign master_if[1].bresp  = m1_bresp;
assign master_if[1].bvalid = m1_bvalid;
assign m1_bready   = master_if[1].bready;

assign m1_arid     = master_if[1].arid[RTL_ID_WIDTH-1:0];
assign m1_araddr   = master_if[1].araddr;
assign m1_arlen    = master_if[1].arlen;
assign m1_arsize   = master_if[1].arsize;
assign m1_arburst  = master_if[1].arburst;
assign m1_arlock   = master_if[1].arlock;
assign m1_arcache  = master_if[1].arcache;
assign m1_arprot   = master_if[1].arprot;
assign m1_arqos    = master_if[1].arqos;
assign m1_arvalid  = master_if[1].arvalid;
assign master_if[1].arready = m1_arready;

assign master_if[1].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m1_rid};
assign master_if[1].rdata  = m1_rdata;
assign master_if[1].rresp  = m1_rresp;
assign master_if[1].rlast  = m1_rlast;
assign master_if[1].rvalid = m1_rvalid;
assign m1_rready   = master_if[1].rready;

// Master 2
assign m2_awid     = master_if[2].awid[RTL_ID_WIDTH-1:0];
assign m2_awaddr   = master_if[2].awaddr;
assign m2_awlen    = master_if[2].awlen;
assign m2_awsize   = master_if[2].awsize;
assign m2_awburst  = master_if[2].awburst;
assign m2_awlock   = master_if[2].awlock;
assign m2_awcache  = master_if[2].awcache;
assign m2_awprot   = master_if[2].awprot;
assign m2_awqos    = master_if[2].awqos;
assign m2_awvalid  = master_if[2].awvalid;
assign master_if[2].awready = m2_awready;

assign m2_wdata    = master_if[2].wdata;
assign m2_wstrb    = master_if[2].wstrb;
assign m2_wlast    = master_if[2].wlast;
assign m2_wvalid   = master_if[2].wvalid;
assign master_if[2].wready = m2_wready;

assign master_if[2].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m2_bid};
assign master_if[2].bresp  = m2_bresp;
assign master_if[2].bvalid = m2_bvalid;
assign m2_bready   = master_if[2].bready;

assign m2_arid     = master_if[2].arid[RTL_ID_WIDTH-1:0];
assign m2_araddr   = master_if[2].araddr;
assign m2_arlen    = master_if[2].arlen;
assign m2_arsize   = master_if[2].arsize;
assign m2_arburst  = master_if[2].arburst;
assign m2_arlock   = master_if[2].arlock;
assign m2_arcache  = master_if[2].arcache;
assign m2_arprot   = master_if[2].arprot;
assign m2_arqos    = master_if[2].arqos;
assign m2_arvalid  = master_if[2].arvalid;
assign master_if[2].arready = m2_arready;

assign master_if[2].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m2_rid};
assign master_if[2].rdata  = m2_rdata;
assign master_if[2].rresp  = m2_rresp;
assign master_if[2].rlast  = m2_rlast;
assign master_if[2].rvalid = m2_rvalid;
assign m2_rready   = master_if[2].rready;

// Master 3
assign m3_awid     = master_if[3].awid[RTL_ID_WIDTH-1:0];
assign m3_awaddr   = master_if[3].awaddr;
assign m3_awlen    = master_if[3].awlen;
assign m3_awsize   = master_if[3].awsize;
assign m3_awburst  = master_if[3].awburst;
assign m3_awlock   = master_if[3].awlock;
assign m3_awcache  = master_if[3].awcache;
assign m3_awprot   = master_if[3].awprot;
assign m3_awqos    = master_if[3].awqos;
assign m3_awvalid  = master_if[3].awvalid;
assign master_if[3].awready = m3_awready;

assign m3_wdata    = master_if[3].wdata;
assign m3_wstrb    = master_if[3].wstrb;
assign m3_wlast    = master_if[3].wlast;
assign m3_wvalid   = master_if[3].wvalid;
assign master_if[3].wready = m3_wready;

assign master_if[3].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m3_bid};
assign master_if[3].bresp  = m3_bresp;
assign master_if[3].bvalid = m3_bvalid;
assign m3_bready   = master_if[3].bready;

assign m3_arid     = master_if[3].arid[RTL_ID_WIDTH-1:0];
assign m3_araddr   = master_if[3].araddr;
assign m3_arlen    = master_if[3].arlen;
assign m3_arsize   = master_if[3].arsize;
assign m3_arburst  = master_if[3].arburst;
assign m3_arlock   = master_if[3].arlock;
assign m3_arcache  = master_if[3].arcache;
assign m3_arprot   = master_if[3].arprot;
assign m3_arqos    = master_if[3].arqos;
assign m3_arvalid  = master_if[3].arvalid;
assign master_if[3].arready = m3_arready;

assign master_if[3].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m3_rid};
assign master_if[3].rdata  = m3_rdata;
assign master_if[3].rresp  = m3_rresp;
assign master_if[3].rlast  = m3_rlast;
assign master_if[3].rvalid = m3_rvalid;
assign m3_rready   = master_if[3].rready;

// Master 4
assign m4_awid     = master_if[4].awid[RTL_ID_WIDTH-1:0];
assign m4_awaddr   = master_if[4].awaddr;
assign m4_awlen    = master_if[4].awlen;
assign m4_awsize   = master_if[4].awsize;
assign m4_awburst  = master_if[4].awburst;
assign m4_awlock   = master_if[4].awlock;
assign m4_awcache  = master_if[4].awcache;
assign m4_awprot   = master_if[4].awprot;
assign m4_awqos    = master_if[4].awqos;
assign m4_awvalid  = master_if[4].awvalid;
assign master_if[4].awready = m4_awready;

assign m4_wdata    = master_if[4].wdata;
assign m4_wstrb    = master_if[4].wstrb;
assign m4_wlast    = master_if[4].wlast;
assign m4_wvalid   = master_if[4].wvalid;
assign master_if[4].wready = m4_wready;

assign master_if[4].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m4_bid};
assign master_if[4].bresp  = m4_bresp;
assign master_if[4].bvalid = m4_bvalid;
assign m4_bready   = master_if[4].bready;

assign m4_arid     = master_if[4].arid[RTL_ID_WIDTH-1:0];
assign m4_araddr   = master_if[4].araddr;
assign m4_arlen    = master_if[4].arlen;
assign m4_arsize   = master_if[4].arsize;
assign m4_arburst  = master_if[4].arburst;
assign m4_arlock   = master_if[4].arlock;
assign m4_arcache  = master_if[4].arcache;
assign m4_arprot   = master_if[4].arprot;
assign m4_arqos    = master_if[4].arqos;
assign m4_arvalid  = master_if[4].arvalid;
assign master_if[4].arready = m4_arready;

assign master_if[4].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m4_rid};
assign master_if[4].rdata  = m4_rdata;
assign master_if[4].rresp  = m4_rresp;
assign master_if[4].rlast  = m4_rlast;
assign master_if[4].rvalid = m4_rvalid;
assign m4_rready   = master_if[4].rready;

// Master 5
assign m5_awid     = master_if[5].awid[RTL_ID_WIDTH-1:0];
assign m5_awaddr   = master_if[5].awaddr;
assign m5_awlen    = master_if[5].awlen;
assign m5_awsize   = master_if[5].awsize;
assign m5_awburst  = master_if[5].awburst;
assign m5_awlock   = master_if[5].awlock;
assign m5_awcache  = master_if[5].awcache;
assign m5_awprot   = master_if[5].awprot;
assign m5_awqos    = master_if[5].awqos;
assign m5_awvalid  = master_if[5].awvalid;
assign master_if[5].awready = m5_awready;

assign m5_wdata    = master_if[5].wdata;
assign m5_wstrb    = master_if[5].wstrb;
assign m5_wlast    = master_if[5].wlast;
assign m5_wvalid   = master_if[5].wvalid;
assign master_if[5].wready = m5_wready;

assign master_if[5].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m5_bid};
assign master_if[5].bresp  = m5_bresp;
assign master_if[5].bvalid = m5_bvalid;
assign m5_bready   = master_if[5].bready;

assign m5_arid     = master_if[5].arid[RTL_ID_WIDTH-1:0];
assign m5_araddr   = master_if[5].araddr;
assign m5_arlen    = master_if[5].arlen;
assign m5_arsize   = master_if[5].arsize;
assign m5_arburst  = master_if[5].arburst;
assign m5_arlock   = master_if[5].arlock;
assign m5_arcache  = master_if[5].arcache;
assign m5_arprot   = master_if[5].arprot;
assign m5_arqos    = master_if[5].arqos;
assign m5_arvalid  = master_if[5].arvalid;
assign master_if[5].arready = m5_arready;

assign master_if[5].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m5_rid};
assign master_if[5].rdata  = m5_rdata;
assign master_if[5].rresp  = m5_rresp;
assign master_if[5].rlast  = m5_rlast;
assign master_if[5].rvalid = m5_rvalid;
assign m5_rready   = master_if[5].rready;

// Master 6
assign m6_awid     = master_if[6].awid[RTL_ID_WIDTH-1:0];
assign m6_awaddr   = master_if[6].awaddr;
assign m6_awlen    = master_if[6].awlen;
assign m6_awsize   = master_if[6].awsize;
assign m6_awburst  = master_if[6].awburst;
assign m6_awlock   = master_if[6].awlock;
assign m6_awcache  = master_if[6].awcache;
assign m6_awprot   = master_if[6].awprot;
assign m6_awqos    = master_if[6].awqos;
assign m6_awvalid  = master_if[6].awvalid;
assign master_if[6].awready = m6_awready;

assign m6_wdata    = master_if[6].wdata;
assign m6_wstrb    = master_if[6].wstrb;
assign m6_wlast    = master_if[6].wlast;
assign m6_wvalid   = master_if[6].wvalid;
assign master_if[6].wready = m6_wready;

assign master_if[6].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m6_bid};
assign master_if[6].bresp  = m6_bresp;
assign master_if[6].bvalid = m6_bvalid;
assign m6_bready   = master_if[6].bready;

assign m6_arid     = master_if[6].arid[RTL_ID_WIDTH-1:0];
assign m6_araddr   = master_if[6].araddr;
assign m6_arlen    = master_if[6].arlen;
assign m6_arsize   = master_if[6].arsize;
assign m6_arburst  = master_if[6].arburst;
assign m6_arlock   = master_if[6].arlock;
assign m6_arcache  = master_if[6].arcache;
assign m6_arprot   = master_if[6].arprot;
assign m6_arqos    = master_if[6].arqos;
assign m6_arvalid  = master_if[6].arvalid;
assign master_if[6].arready = m6_arready;

assign master_if[6].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m6_rid};
assign master_if[6].rdata  = m6_rdata;
assign master_if[6].rresp  = m6_rresp;
assign master_if[6].rlast  = m6_rlast;
assign master_if[6].rvalid = m6_rvalid;
assign m6_rready   = master_if[6].rready;

// Master 7
assign m7_awid     = master_if[7].awid[RTL_ID_WIDTH-1:0];
assign m7_awaddr   = master_if[7].awaddr;
assign m7_awlen    = master_if[7].awlen;
assign m7_awsize   = master_if[7].awsize;
assign m7_awburst  = master_if[7].awburst;
assign m7_awlock   = master_if[7].awlock;
assign m7_awcache  = master_if[7].awcache;
assign m7_awprot   = master_if[7].awprot;
assign m7_awqos    = master_if[7].awqos;
assign m7_awvalid  = master_if[7].awvalid;
assign master_if[7].awready = m7_awready;

assign m7_wdata    = master_if[7].wdata;
assign m7_wstrb    = master_if[7].wstrb;
assign m7_wlast    = master_if[7].wlast;
assign m7_wvalid   = master_if[7].wvalid;
assign master_if[7].wready = m7_wready;

assign master_if[7].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m7_bid};
assign master_if[7].bresp  = m7_bresp;
assign master_if[7].bvalid = m7_bvalid;
assign m7_bready   = master_if[7].bready;

assign m7_arid     = master_if[7].arid[RTL_ID_WIDTH-1:0];
assign m7_araddr   = master_if[7].araddr;
assign m7_arlen    = master_if[7].arlen;
assign m7_arsize   = master_if[7].arsize;
assign m7_arburst  = master_if[7].arburst;
assign m7_arlock   = master_if[7].arlock;
assign m7_arcache  = master_if[7].arcache;
assign m7_arprot   = master_if[7].arprot;
assign m7_arqos    = master_if[7].arqos;
assign m7_arvalid  = master_if[7].arvalid;
assign master_if[7].arready = m7_arready;

assign master_if[7].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m7_rid};
assign master_if[7].rdata  = m7_rdata;
assign master_if[7].rresp  = m7_rresp;
assign master_if[7].rlast  = m7_rlast;
assign master_if[7].rvalid = m7_rvalid;
assign m7_rready   = master_if[7].rready;

// Master 8
assign m8_awid     = master_if[8].awid[RTL_ID_WIDTH-1:0];
assign m8_awaddr   = master_if[8].awaddr;
assign m8_awlen    = master_if[8].awlen;
assign m8_awsize   = master_if[8].awsize;
assign m8_awburst  = master_if[8].awburst;
assign m8_awlock   = master_if[8].awlock;
assign m8_awcache  = master_if[8].awcache;
assign m8_awprot   = master_if[8].awprot;
assign m8_awqos    = master_if[8].awqos;
assign m8_awvalid  = master_if[8].awvalid;
assign master_if[8].awready = m8_awready;

assign m8_wdata    = master_if[8].wdata;
assign m8_wstrb    = master_if[8].wstrb;
assign m8_wlast    = master_if[8].wlast;
assign m8_wvalid   = master_if[8].wvalid;
assign master_if[8].wready = m8_wready;

assign master_if[8].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m8_bid};
assign master_if[8].bresp  = m8_bresp;
assign master_if[8].bvalid = m8_bvalid;
assign m8_bready   = master_if[8].bready;

assign m8_arid     = master_if[8].arid[RTL_ID_WIDTH-1:0];
assign m8_araddr   = master_if[8].araddr;
assign m8_arlen    = master_if[8].arlen;
assign m8_arsize   = master_if[8].arsize;
assign m8_arburst  = master_if[8].arburst;
assign m8_arlock   = master_if[8].arlock;
assign m8_arcache  = master_if[8].arcache;
assign m8_arprot   = master_if[8].arprot;
assign m8_arqos    = master_if[8].arqos;
assign m8_arvalid  = master_if[8].arvalid;
assign master_if[8].arready = m8_arready;

assign master_if[8].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m8_rid};
assign master_if[8].rdata  = m8_rdata;
assign master_if[8].rresp  = m8_rresp;
assign master_if[8].rlast  = m8_rlast;
assign master_if[8].rvalid = m8_rvalid;
assign m8_rready   = master_if[8].rready;

// Master 9
assign m9_awid     = master_if[9].awid[RTL_ID_WIDTH-1:0];
assign m9_awaddr   = master_if[9].awaddr;
assign m9_awlen    = master_if[9].awlen;
assign m9_awsize   = master_if[9].awsize;
assign m9_awburst  = master_if[9].awburst;
assign m9_awlock   = master_if[9].awlock;
assign m9_awcache  = master_if[9].awcache;
assign m9_awprot   = master_if[9].awprot;
assign m9_awqos    = master_if[9].awqos;
assign m9_awvalid  = master_if[9].awvalid;
assign master_if[9].awready = m9_awready;

assign m9_wdata    = master_if[9].wdata;
assign m9_wstrb    = master_if[9].wstrb;
assign m9_wlast    = master_if[9].wlast;
assign m9_wvalid   = master_if[9].wvalid;
assign master_if[9].wready = m9_wready;

assign master_if[9].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m9_bid};
assign master_if[9].bresp  = m9_bresp;
assign master_if[9].bvalid = m9_bvalid;
assign m9_bready   = master_if[9].bready;

assign m9_arid     = master_if[9].arid[RTL_ID_WIDTH-1:0];
assign m9_araddr   = master_if[9].araddr;
assign m9_arlen    = master_if[9].arlen;
assign m9_arsize   = master_if[9].arsize;
assign m9_arburst  = master_if[9].arburst;
assign m9_arlock   = master_if[9].arlock;
assign m9_arcache  = master_if[9].arcache;
assign m9_arprot   = master_if[9].arprot;
assign m9_arqos    = master_if[9].arqos;
assign m9_arvalid  = master_if[9].arvalid;
assign master_if[9].arready = m9_arready;

assign master_if[9].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m9_rid};
assign master_if[9].rdata  = m9_rdata;
assign master_if[9].rresp  = m9_rresp;
assign master_if[9].rlast  = m9_rlast;
assign master_if[9].rvalid = m9_rvalid;
assign m9_rready   = master_if[9].rready;

// Master 10
assign m10_awid     = master_if[10].awid[RTL_ID_WIDTH-1:0];
assign m10_awaddr   = master_if[10].awaddr;
assign m10_awlen    = master_if[10].awlen;
assign m10_awsize   = master_if[10].awsize;
assign m10_awburst  = master_if[10].awburst;
assign m10_awlock   = master_if[10].awlock;
assign m10_awcache  = master_if[10].awcache;
assign m10_awprot   = master_if[10].awprot;
assign m10_awqos    = master_if[10].awqos;
assign m10_awvalid  = master_if[10].awvalid;
assign master_if[10].awready = m10_awready;

assign m10_wdata    = master_if[10].wdata;
assign m10_wstrb    = master_if[10].wstrb;
assign m10_wlast    = master_if[10].wlast;
assign m10_wvalid   = master_if[10].wvalid;
assign master_if[10].wready = m10_wready;

assign master_if[10].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m10_bid};
assign master_if[10].bresp  = m10_bresp;
assign master_if[10].bvalid = m10_bvalid;
assign m10_bready   = master_if[10].bready;

assign m10_arid     = master_if[10].arid[RTL_ID_WIDTH-1:0];
assign m10_araddr   = master_if[10].araddr;
assign m10_arlen    = master_if[10].arlen;
assign m10_arsize   = master_if[10].arsize;
assign m10_arburst  = master_if[10].arburst;
assign m10_arlock   = master_if[10].arlock;
assign m10_arcache  = master_if[10].arcache;
assign m10_arprot   = master_if[10].arprot;
assign m10_arqos    = master_if[10].arqos;
assign m10_arvalid  = master_if[10].arvalid;
assign master_if[10].arready = m10_arready;

assign master_if[10].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m10_rid};
assign master_if[10].rdata  = m10_rdata;
assign master_if[10].rresp  = m10_rresp;
assign master_if[10].rlast  = m10_rlast;
assign master_if[10].rvalid = m10_rvalid;
assign m10_rready   = master_if[10].rready;

// Master 11
assign m11_awid     = master_if[11].awid[RTL_ID_WIDTH-1:0];
assign m11_awaddr   = master_if[11].awaddr;
assign m11_awlen    = master_if[11].awlen;
assign m11_awsize   = master_if[11].awsize;
assign m11_awburst  = master_if[11].awburst;
assign m11_awlock   = master_if[11].awlock;
assign m11_awcache  = master_if[11].awcache;
assign m11_awprot   = master_if[11].awprot;
assign m11_awqos    = master_if[11].awqos;
assign m11_awvalid  = master_if[11].awvalid;
assign master_if[11].awready = m11_awready;

assign m11_wdata    = master_if[11].wdata;
assign m11_wstrb    = master_if[11].wstrb;
assign m11_wlast    = master_if[11].wlast;
assign m11_wvalid   = master_if[11].wvalid;
assign master_if[11].wready = m11_wready;

assign master_if[11].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m11_bid};
assign master_if[11].bresp  = m11_bresp;
assign master_if[11].bvalid = m11_bvalid;
assign m11_bready   = master_if[11].bready;

assign m11_arid     = master_if[11].arid[RTL_ID_WIDTH-1:0];
assign m11_araddr   = master_if[11].araddr;
assign m11_arlen    = master_if[11].arlen;
assign m11_arsize   = master_if[11].arsize;
assign m11_arburst  = master_if[11].arburst;
assign m11_arlock   = master_if[11].arlock;
assign m11_arcache  = master_if[11].arcache;
assign m11_arprot   = master_if[11].arprot;
assign m11_arqos    = master_if[11].arqos;
assign m11_arvalid  = master_if[11].arvalid;
assign master_if[11].arready = m11_arready;

assign master_if[11].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m11_rid};
assign master_if[11].rdata  = m11_rdata;
assign master_if[11].rresp  = m11_rresp;
assign master_if[11].rlast  = m11_rlast;
assign master_if[11].rvalid = m11_rvalid;
assign m11_rready   = master_if[11].rready;

// Master 12
assign m12_awid     = master_if[12].awid[RTL_ID_WIDTH-1:0];
assign m12_awaddr   = master_if[12].awaddr;
assign m12_awlen    = master_if[12].awlen;
assign m12_awsize   = master_if[12].awsize;
assign m12_awburst  = master_if[12].awburst;
assign m12_awlock   = master_if[12].awlock;
assign m12_awcache  = master_if[12].awcache;
assign m12_awprot   = master_if[12].awprot;
assign m12_awqos    = master_if[12].awqos;
assign m12_awvalid  = master_if[12].awvalid;
assign master_if[12].awready = m12_awready;

assign m12_wdata    = master_if[12].wdata;
assign m12_wstrb    = master_if[12].wstrb;
assign m12_wlast    = master_if[12].wlast;
assign m12_wvalid   = master_if[12].wvalid;
assign master_if[12].wready = m12_wready;

assign master_if[12].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m12_bid};
assign master_if[12].bresp  = m12_bresp;
assign master_if[12].bvalid = m12_bvalid;
assign m12_bready   = master_if[12].bready;

assign m12_arid     = master_if[12].arid[RTL_ID_WIDTH-1:0];
assign m12_araddr   = master_if[12].araddr;
assign m12_arlen    = master_if[12].arlen;
assign m12_arsize   = master_if[12].arsize;
assign m12_arburst  = master_if[12].arburst;
assign m12_arlock   = master_if[12].arlock;
assign m12_arcache  = master_if[12].arcache;
assign m12_arprot   = master_if[12].arprot;
assign m12_arqos    = master_if[12].arqos;
assign m12_arvalid  = master_if[12].arvalid;
assign master_if[12].arready = m12_arready;

assign master_if[12].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m12_rid};
assign master_if[12].rdata  = m12_rdata;
assign master_if[12].rresp  = m12_rresp;
assign master_if[12].rlast  = m12_rlast;
assign master_if[12].rvalid = m12_rvalid;
assign m12_rready   = master_if[12].rready;

// Master 13
assign m13_awid     = master_if[13].awid[RTL_ID_WIDTH-1:0];
assign m13_awaddr   = master_if[13].awaddr;
assign m13_awlen    = master_if[13].awlen;
assign m13_awsize   = master_if[13].awsize;
assign m13_awburst  = master_if[13].awburst;
assign m13_awlock   = master_if[13].awlock;
assign m13_awcache  = master_if[13].awcache;
assign m13_awprot   = master_if[13].awprot;
assign m13_awqos    = master_if[13].awqos;
assign m13_awvalid  = master_if[13].awvalid;
assign master_if[13].awready = m13_awready;

assign m13_wdata    = master_if[13].wdata;
assign m13_wstrb    = master_if[13].wstrb;
assign m13_wlast    = master_if[13].wlast;
assign m13_wvalid   = master_if[13].wvalid;
assign master_if[13].wready = m13_wready;

assign master_if[13].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m13_bid};
assign master_if[13].bresp  = m13_bresp;
assign master_if[13].bvalid = m13_bvalid;
assign m13_bready   = master_if[13].bready;

assign m13_arid     = master_if[13].arid[RTL_ID_WIDTH-1:0];
assign m13_araddr   = master_if[13].araddr;
assign m13_arlen    = master_if[13].arlen;
assign m13_arsize   = master_if[13].arsize;
assign m13_arburst  = master_if[13].arburst;
assign m13_arlock   = master_if[13].arlock;
assign m13_arcache  = master_if[13].arcache;
assign m13_arprot   = master_if[13].arprot;
assign m13_arqos    = master_if[13].arqos;
assign m13_arvalid  = master_if[13].arvalid;
assign master_if[13].arready = m13_arready;

assign master_if[13].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m13_rid};
assign master_if[13].rdata  = m13_rdata;
assign master_if[13].rresp  = m13_rresp;
assign master_if[13].rlast  = m13_rlast;
assign master_if[13].rvalid = m13_rvalid;
assign m13_rready   = master_if[13].rready;

// Master 14
assign m14_awid     = master_if[14].awid[RTL_ID_WIDTH-1:0];
assign m14_awaddr   = master_if[14].awaddr;
assign m14_awlen    = master_if[14].awlen;
assign m14_awsize   = master_if[14].awsize;
assign m14_awburst  = master_if[14].awburst;
assign m14_awlock   = master_if[14].awlock;
assign m14_awcache  = master_if[14].awcache;
assign m14_awprot   = master_if[14].awprot;
assign m14_awqos    = master_if[14].awqos;
assign m14_awvalid  = master_if[14].awvalid;
assign master_if[14].awready = m14_awready;

assign m14_wdata    = master_if[14].wdata;
assign m14_wstrb    = master_if[14].wstrb;
assign m14_wlast    = master_if[14].wlast;
assign m14_wvalid   = master_if[14].wvalid;
assign master_if[14].wready = m14_wready;

assign master_if[14].bid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m14_bid};
assign master_if[14].bresp  = m14_bresp;
assign master_if[14].bvalid = m14_bvalid;
assign m14_bready   = master_if[14].bready;

assign m14_arid     = master_if[14].arid[RTL_ID_WIDTH-1:0];
assign m14_araddr   = master_if[14].araddr;
assign m14_arlen    = master_if[14].arlen;
assign m14_arsize   = master_if[14].arsize;
assign m14_arburst  = master_if[14].arburst;
assign m14_arlock   = master_if[14].arlock;
assign m14_arcache  = master_if[14].arcache;
assign m14_arprot   = master_if[14].arprot;
assign m14_arqos    = master_if[14].arqos;
assign m14_arvalid  = master_if[14].arvalid;
assign master_if[14].arready = m14_arready;

assign master_if[14].rid    = {{(ID_WIDTH-RTL_ID_WIDTH){1'b0}}, m14_rid};
assign master_if[14].rdata  = m14_rdata;
assign master_if[14].rresp  = m14_rresp;
assign master_if[14].rlast  = m14_rlast;
assign master_if[14].rvalid = m14_rvalid;
assign m14_rready   = master_if[14].rready;

