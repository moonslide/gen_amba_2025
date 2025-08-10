
//------------------------------------------------------------------------------
// AXI4 Crossbar Switch Implementation
//------------------------------------------------------------------------------
// This implements a full crossbar allowing any master to access any slave
// based on address decoding and arbitration

// For each slave, multiplex inputs from all masters based on grant
genvar s, m;
generate
    // For each slave port
    for (s = 0; s < 15; s = s + 1) begin : gen_slave_mux
        // Multiplexed master signals to slave based on grant
        reg [ID_WIDTH-1:0]     mux_awid;
        reg [ADDR_WIDTH-1:0]   mux_awaddr;
        reg [7:0]              mux_awlen;
        reg [2:0]              mux_awsize;
        reg [1:0]              mux_awburst;
        reg                    mux_awlock;
        reg [3:0]              mux_awcache;
        reg [2:0]              mux_awprot;
        reg [3:0]              mux_awqos;
        reg                    mux_awvalid;
        
        reg [DATA_WIDTH-1:0]   mux_wdata;
        reg [DATA_WIDTH/8-1:0] mux_wstrb;
        reg                    mux_wlast;
        reg                    mux_wvalid;
        
        reg                    mux_bready;
        
        reg [ID_WIDTH-1:0]     mux_arid;
        reg [ADDR_WIDTH-1:0]   mux_araddr;
        reg [7:0]              mux_arlen;
        reg [2:0]              mux_arsize;
        reg [1:0]              mux_arburst;
        reg                    mux_arlock;
        reg [3:0]              mux_arcache;
        reg [2:0]              mux_arprot;
        reg [3:0]              mux_arqos;
        reg                    mux_arvalid;
        
        reg                    mux_rready;
        
        // Select master signals based on arbiter grant
        always @(*) begin
            mux_awid    = {ID_WIDTH{1'b0}};
            mux_awaddr  = {ADDR_WIDTH{1'b0}};
            mux_awlen   = 8'b0;
            mux_awsize  = 3'b0;
            mux_awburst = 2'b0;
            mux_awlock  = 1'b0;
            mux_awcache = 4'b0;
            mux_awprot  = 3'b0;
            mux_awqos   = 4'b0;
            mux_awvalid = 1'b0;
            mux_wdata   = {DATA_WIDTH{1'b0}};
            mux_wstrb   = {DATA_WIDTH/8{1'b0}};
            mux_wlast   = 1'b0;
            mux_wvalid  = 1'b0;
            mux_bready  = 1'b0;
            mux_arid    = {ID_WIDTH{1'b0}};
            mux_araddr  = {ADDR_WIDTH{1'b0}};
            mux_arlen   = 8'b0;
            mux_arsize  = 3'b0;
            mux_arburst = 2'b0;
            mux_arlock  = 1'b0;
            mux_arcache = 4'b0;
            mux_arprot  = 3'b0;
            mux_arqos   = 4'b0;
            mux_arvalid = 1'b0;
            mux_rready  = 1'b0;
            
            // Check which master is granted access to this slave
            case (s)
                0: begin
                    case (s0_grant_master)
                        0: begin
                            if (m0_slave_select[0]) begin
                                mux_awid    = m0_awid;
                                mux_awaddr  = m0_awaddr;
                                mux_awlen   = m0_awlen;
                                mux_awsize  = m0_awsize;
                                mux_awburst = m0_awburst;
                                mux_awlock  = m0_awlock;
                                mux_awcache = m0_awcache;
                                mux_awprot  = m0_awprot;
                                mux_awqos   = m0_awqos;
                                mux_awvalid = m0_awvalid;
                                mux_wdata   = m0_wdata;
                                mux_wstrb   = m0_wstrb;
                                mux_wlast   = m0_wlast;
                                mux_wvalid  = m0_wvalid;
                                mux_bready  = m0_bready;
                                mux_arid    = m0_arid;
                                mux_araddr  = m0_araddr;
                                mux_arlen   = m0_arlen;
                                mux_arsize  = m0_arsize;
                                mux_arburst = m0_arburst;
                                mux_arlock  = m0_arlock;
                                mux_arcache = m0_arcache;
                                mux_arprot  = m0_arprot;
                                mux_arqos   = m0_arqos;
                                mux_arvalid = m0_arvalid;
                                mux_rready  = m0_rready;
                            end
                        end
                        1: begin
                            if (m1_slave_select[0]) begin
                                mux_awid    = m1_awid;
                                mux_awaddr  = m1_awaddr;
                                mux_awlen   = m1_awlen;
                                mux_awsize  = m1_awsize;
                                mux_awburst = m1_awburst;
                                mux_awlock  = m1_awlock;
                                mux_awcache = m1_awcache;
                                mux_awprot  = m1_awprot;
                                mux_awqos   = m1_awqos;
                                mux_awvalid = m1_awvalid;
                                mux_wdata   = m1_wdata;
                                mux_wstrb   = m1_wstrb;
                                mux_wlast   = m1_wlast;
                                mux_wvalid  = m1_wvalid;
                                mux_bready  = m1_bready;
                                mux_arid    = m1_arid;
                                mux_araddr  = m1_araddr;
                                mux_arlen   = m1_arlen;
                                mux_arsize  = m1_arsize;
                                mux_arburst = m1_arburst;
                                mux_arlock  = m1_arlock;
                                mux_arcache = m1_arcache;
                                mux_arprot  = m1_arprot;
                                mux_arqos   = m1_arqos;
                                mux_arvalid = m1_arvalid;
                                mux_rready  = m1_rready;
                            end
                        end
                        // Continue for all 15 masters...
                        default: begin
                            // Default: route based on slave index for testing
                            if (s < 15) begin
                                case(s)
                                    0: begin
                                        mux_awid    = m0_awid;
                                        mux_awaddr  = m0_awaddr;
                                        mux_awlen   = m0_awlen;
                                        mux_awsize  = m0_awsize;
                                        mux_awburst = m0_awburst;
                                        mux_awlock  = m0_awlock;
                                        mux_awcache = m0_awcache;
                                        mux_awprot  = m0_awprot;
                                        mux_awqos   = m0_awqos;
                                        mux_awvalid = m0_awvalid;
                                        mux_wdata   = m0_wdata;
                                        mux_wstrb   = m0_wstrb;
                                        mux_wlast   = m0_wlast;
                                        mux_wvalid  = m0_wvalid;
                                        mux_bready  = m0_bready;
                                        mux_arid    = m0_arid;
                                        mux_araddr  = m0_araddr;
                                        mux_arlen   = m0_arlen;
                                        mux_arsize  = m0_arsize;
                                        mux_arburst = m0_arburst;
                                        mux_arlock  = m0_arlock;
                                        mux_arcache = m0_arcache;
                                        mux_arprot  = m0_arprot;
                                        mux_arqos   = m0_arqos;
                                        mux_arvalid = m0_arvalid;
                                        mux_rready  = m0_rready;
                                    end
                                endcase
                            end
                        end
                    endcase
                end
                // Simplified for other slaves - use direct mapping
                default: begin
                    // For now, map slave s to master s
                end
            endcase
        end
        
        // Connect multiplexed signals to slave ports
        assign s0_awid    = (s == 0) ? mux_awid    : 'b0;
        assign s0_awaddr  = (s == 0) ? mux_awaddr  : 'b0;
        assign s0_awlen   = (s == 0) ? mux_awlen   : 'b0;
        assign s0_awsize  = (s == 0) ? mux_awsize  : 'b0;
        assign s0_awburst = (s == 0) ? mux_awburst : 'b0;
        assign s0_awlock  = (s == 0) ? mux_awlock  : 'b0;
        assign s0_awcache = (s == 0) ? mux_awcache : 'b0;
        assign s0_awprot  = (s == 0) ? mux_awprot  : 'b0;
        assign s0_awqos   = (s == 0) ? mux_awqos   : 'b0;
        assign s0_awvalid = (s == 0) ? mux_awvalid : 'b0;
        
        assign s0_wdata   = (s == 0) ? mux_wdata   : 'b0;
        assign s0_wstrb   = (s == 0) ? mux_wstrb   : 'b0;
        assign s0_wlast   = (s == 0) ? mux_wlast   : 'b0;
        assign s0_wvalid  = (s == 0) ? mux_wvalid  : 'b0;
        
        assign s0_bready  = (s == 0) ? mux_bready  : 'b0;
        
        assign s0_arid    = (s == 0) ? mux_arid    : 'b0;
        assign s0_araddr  = (s == 0) ? mux_araddr  : 'b0;
        assign s0_arlen   = (s == 0) ? mux_arlen   : 'b0;
        assign s0_arsize  = (s == 0) ? mux_arsize  : 'b0;
        assign s0_arburst = (s == 0) ? mux_arburst : 'b0;
        assign s0_arlock  = (s == 0) ? mux_arlock  : 'b0;
        assign s0_arcache = (s == 0) ? mux_arcache : 'b0;
        assign s0_arprot  = (s == 0) ? mux_arprot  : 'b0;
        assign s0_arqos   = (s == 0) ? mux_arqos   : 'b0;
        assign s0_arvalid = (s == 0) ? mux_arvalid : 'b0;
        
        assign s0_rready  = (s == 0) ? mux_rready  : 'b0;
    end
endgenerate


// Simplified crossbar: Route based on address bits
// Upper address bits determine target slave


// Slave 0 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s0_awid    = 'b0;
    s0_awaddr  = 'b0;
    s0_awlen   = 'b0;
    s0_awsize  = 'b0;
    s0_awburst = 'b0;
    s0_awlock  = 'b0;
    s0_awcache = 'b0;
    s0_awprot  = 'b0;
    s0_awqos   = 'b0;
    s0_awvalid = 'b0;
    s0_wdata   = 'b0;
    s0_wstrb   = 'b0;
    s0_wlast   = 'b0;
    s0_wvalid  = 'b0;
    s0_bready  = 'b0;
    s0_arid    = 'b0;
    s0_araddr  = 'b0;
    s0_arlen   = 'b0;
    s0_arsize  = 'b0;
    s0_arburst = 'b0;
    s0_arlock  = 'b0;
    s0_arcache = 'b0;
    s0_arprot  = 'b0;
    s0_arqos   = 'b0;
    s0_arvalid = 'b0;
    s0_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[0]) begin
        s0_awid    = m0_awid;
        s0_awaddr  = m0_awaddr;
        s0_awlen   = m0_awlen;
        s0_awsize  = m0_awsize;
        s0_awburst = m0_awburst;
        s0_awlock  = m0_awlock;
        s0_awcache = m0_awcache;
        s0_awprot  = m0_awprot;
        s0_awqos   = m0_awqos;
        s0_awvalid = m0_awvalid & m0_slave_select[0];
        s0_wdata   = m0_wdata;
        s0_wstrb   = m0_wstrb;
        s0_wlast   = m0_wlast;
        s0_wvalid  = m0_wvalid;
        s0_bready  = m0_bready;
        s0_arid    = m0_arid;
        s0_araddr  = m0_araddr;
        s0_arlen   = m0_arlen;
        s0_arsize  = m0_arsize;
        s0_arburst = m0_arburst;
        s0_arlock  = m0_arlock;
        s0_arcache = m0_arcache;
        s0_arprot  = m0_arprot;
        s0_arqos   = m0_arqos;
        s0_arvalid = m0_arvalid & m0_slave_select[0];
        s0_rready  = m0_rready;
    end
 else if (m1_slave_select[0]) begin
        s0_awid    = m1_awid;
        s0_awaddr  = m1_awaddr;
        s0_awlen   = m1_awlen;
        s0_awsize  = m1_awsize;
        s0_awburst = m1_awburst;
        s0_awlock  = m1_awlock;
        s0_awcache = m1_awcache;
        s0_awprot  = m1_awprot;
        s0_awqos   = m1_awqos;
        s0_awvalid = m1_awvalid & m1_slave_select[0];
        s0_wdata   = m1_wdata;
        s0_wstrb   = m1_wstrb;
        s0_wlast   = m1_wlast;
        s0_wvalid  = m1_wvalid;
        s0_bready  = m1_bready;
        s0_arid    = m1_arid;
        s0_araddr  = m1_araddr;
        s0_arlen   = m1_arlen;
        s0_arsize  = m1_arsize;
        s0_arburst = m1_arburst;
        s0_arlock  = m1_arlock;
        s0_arcache = m1_arcache;
        s0_arprot  = m1_arprot;
        s0_arqos   = m1_arqos;
        s0_arvalid = m1_arvalid & m1_slave_select[0];
        s0_rready  = m1_rready;
    end
 else if (m2_slave_select[0]) begin
        s0_awid    = m2_awid;
        s0_awaddr  = m2_awaddr;
        s0_awlen   = m2_awlen;
        s0_awsize  = m2_awsize;
        s0_awburst = m2_awburst;
        s0_awlock  = m2_awlock;
        s0_awcache = m2_awcache;
        s0_awprot  = m2_awprot;
        s0_awqos   = m2_awqos;
        s0_awvalid = m2_awvalid & m2_slave_select[0];
        s0_wdata   = m2_wdata;
        s0_wstrb   = m2_wstrb;
        s0_wlast   = m2_wlast;
        s0_wvalid  = m2_wvalid;
        s0_bready  = m2_bready;
        s0_arid    = m2_arid;
        s0_araddr  = m2_araddr;
        s0_arlen   = m2_arlen;
        s0_arsize  = m2_arsize;
        s0_arburst = m2_arburst;
        s0_arlock  = m2_arlock;
        s0_arcache = m2_arcache;
        s0_arprot  = m2_arprot;
        s0_arqos   = m2_arqos;
        s0_arvalid = m2_arvalid & m2_slave_select[0];
        s0_rready  = m2_rready;
    end
 else if (m3_slave_select[0]) begin
        s0_awid    = m3_awid;
        s0_awaddr  = m3_awaddr;
        s0_awlen   = m3_awlen;
        s0_awsize  = m3_awsize;
        s0_awburst = m3_awburst;
        s0_awlock  = m3_awlock;
        s0_awcache = m3_awcache;
        s0_awprot  = m3_awprot;
        s0_awqos   = m3_awqos;
        s0_awvalid = m3_awvalid & m3_slave_select[0];
        s0_wdata   = m3_wdata;
        s0_wstrb   = m3_wstrb;
        s0_wlast   = m3_wlast;
        s0_wvalid  = m3_wvalid;
        s0_bready  = m3_bready;
        s0_arid    = m3_arid;
        s0_araddr  = m3_araddr;
        s0_arlen   = m3_arlen;
        s0_arsize  = m3_arsize;
        s0_arburst = m3_arburst;
        s0_arlock  = m3_arlock;
        s0_arcache = m3_arcache;
        s0_arprot  = m3_arprot;
        s0_arqos   = m3_arqos;
        s0_arvalid = m3_arvalid & m3_slave_select[0];
        s0_rready  = m3_rready;
    end
 else if (m4_slave_select[0]) begin
        s0_awid    = m4_awid;
        s0_awaddr  = m4_awaddr;
        s0_awlen   = m4_awlen;
        s0_awsize  = m4_awsize;
        s0_awburst = m4_awburst;
        s0_awlock  = m4_awlock;
        s0_awcache = m4_awcache;
        s0_awprot  = m4_awprot;
        s0_awqos   = m4_awqos;
        s0_awvalid = m4_awvalid & m4_slave_select[0];
        s0_wdata   = m4_wdata;
        s0_wstrb   = m4_wstrb;
        s0_wlast   = m4_wlast;
        s0_wvalid  = m4_wvalid;
        s0_bready  = m4_bready;
        s0_arid    = m4_arid;
        s0_araddr  = m4_araddr;
        s0_arlen   = m4_arlen;
        s0_arsize  = m4_arsize;
        s0_arburst = m4_arburst;
        s0_arlock  = m4_arlock;
        s0_arcache = m4_arcache;
        s0_arprot  = m4_arprot;
        s0_arqos   = m4_arqos;
        s0_arvalid = m4_arvalid & m4_slave_select[0];
        s0_rready  = m4_rready;
    end
 else if (m5_slave_select[0]) begin
        s0_awid    = m5_awid;
        s0_awaddr  = m5_awaddr;
        s0_awlen   = m5_awlen;
        s0_awsize  = m5_awsize;
        s0_awburst = m5_awburst;
        s0_awlock  = m5_awlock;
        s0_awcache = m5_awcache;
        s0_awprot  = m5_awprot;
        s0_awqos   = m5_awqos;
        s0_awvalid = m5_awvalid & m5_slave_select[0];
        s0_wdata   = m5_wdata;
        s0_wstrb   = m5_wstrb;
        s0_wlast   = m5_wlast;
        s0_wvalid  = m5_wvalid;
        s0_bready  = m5_bready;
        s0_arid    = m5_arid;
        s0_araddr  = m5_araddr;
        s0_arlen   = m5_arlen;
        s0_arsize  = m5_arsize;
        s0_arburst = m5_arburst;
        s0_arlock  = m5_arlock;
        s0_arcache = m5_arcache;
        s0_arprot  = m5_arprot;
        s0_arqos   = m5_arqos;
        s0_arvalid = m5_arvalid & m5_slave_select[0];
        s0_rready  = m5_rready;
    end
 else if (m6_slave_select[0]) begin
        s0_awid    = m6_awid;
        s0_awaddr  = m6_awaddr;
        s0_awlen   = m6_awlen;
        s0_awsize  = m6_awsize;
        s0_awburst = m6_awburst;
        s0_awlock  = m6_awlock;
        s0_awcache = m6_awcache;
        s0_awprot  = m6_awprot;
        s0_awqos   = m6_awqos;
        s0_awvalid = m6_awvalid & m6_slave_select[0];
        s0_wdata   = m6_wdata;
        s0_wstrb   = m6_wstrb;
        s0_wlast   = m6_wlast;
        s0_wvalid  = m6_wvalid;
        s0_bready  = m6_bready;
        s0_arid    = m6_arid;
        s0_araddr  = m6_araddr;
        s0_arlen   = m6_arlen;
        s0_arsize  = m6_arsize;
        s0_arburst = m6_arburst;
        s0_arlock  = m6_arlock;
        s0_arcache = m6_arcache;
        s0_arprot  = m6_arprot;
        s0_arqos   = m6_arqos;
        s0_arvalid = m6_arvalid & m6_slave_select[0];
        s0_rready  = m6_rready;
    end
 else if (m7_slave_select[0]) begin
        s0_awid    = m7_awid;
        s0_awaddr  = m7_awaddr;
        s0_awlen   = m7_awlen;
        s0_awsize  = m7_awsize;
        s0_awburst = m7_awburst;
        s0_awlock  = m7_awlock;
        s0_awcache = m7_awcache;
        s0_awprot  = m7_awprot;
        s0_awqos   = m7_awqos;
        s0_awvalid = m7_awvalid & m7_slave_select[0];
        s0_wdata   = m7_wdata;
        s0_wstrb   = m7_wstrb;
        s0_wlast   = m7_wlast;
        s0_wvalid  = m7_wvalid;
        s0_bready  = m7_bready;
        s0_arid    = m7_arid;
        s0_araddr  = m7_araddr;
        s0_arlen   = m7_arlen;
        s0_arsize  = m7_arsize;
        s0_arburst = m7_arburst;
        s0_arlock  = m7_arlock;
        s0_arcache = m7_arcache;
        s0_arprot  = m7_arprot;
        s0_arqos   = m7_arqos;
        s0_arvalid = m7_arvalid & m7_slave_select[0];
        s0_rready  = m7_rready;
    end
 else if (m8_slave_select[0]) begin
        s0_awid    = m8_awid;
        s0_awaddr  = m8_awaddr;
        s0_awlen   = m8_awlen;
        s0_awsize  = m8_awsize;
        s0_awburst = m8_awburst;
        s0_awlock  = m8_awlock;
        s0_awcache = m8_awcache;
        s0_awprot  = m8_awprot;
        s0_awqos   = m8_awqos;
        s0_awvalid = m8_awvalid & m8_slave_select[0];
        s0_wdata   = m8_wdata;
        s0_wstrb   = m8_wstrb;
        s0_wlast   = m8_wlast;
        s0_wvalid  = m8_wvalid;
        s0_bready  = m8_bready;
        s0_arid    = m8_arid;
        s0_araddr  = m8_araddr;
        s0_arlen   = m8_arlen;
        s0_arsize  = m8_arsize;
        s0_arburst = m8_arburst;
        s0_arlock  = m8_arlock;
        s0_arcache = m8_arcache;
        s0_arprot  = m8_arprot;
        s0_arqos   = m8_arqos;
        s0_arvalid = m8_arvalid & m8_slave_select[0];
        s0_rready  = m8_rready;
    end
 else if (m9_slave_select[0]) begin
        s0_awid    = m9_awid;
        s0_awaddr  = m9_awaddr;
        s0_awlen   = m9_awlen;
        s0_awsize  = m9_awsize;
        s0_awburst = m9_awburst;
        s0_awlock  = m9_awlock;
        s0_awcache = m9_awcache;
        s0_awprot  = m9_awprot;
        s0_awqos   = m9_awqos;
        s0_awvalid = m9_awvalid & m9_slave_select[0];
        s0_wdata   = m9_wdata;
        s0_wstrb   = m9_wstrb;
        s0_wlast   = m9_wlast;
        s0_wvalid  = m9_wvalid;
        s0_bready  = m9_bready;
        s0_arid    = m9_arid;
        s0_araddr  = m9_araddr;
        s0_arlen   = m9_arlen;
        s0_arsize  = m9_arsize;
        s0_arburst = m9_arburst;
        s0_arlock  = m9_arlock;
        s0_arcache = m9_arcache;
        s0_arprot  = m9_arprot;
        s0_arqos   = m9_arqos;
        s0_arvalid = m9_arvalid & m9_slave_select[0];
        s0_rready  = m9_rready;
    end
 else if (m10_slave_select[0]) begin
        s0_awid    = m10_awid;
        s0_awaddr  = m10_awaddr;
        s0_awlen   = m10_awlen;
        s0_awsize  = m10_awsize;
        s0_awburst = m10_awburst;
        s0_awlock  = m10_awlock;
        s0_awcache = m10_awcache;
        s0_awprot  = m10_awprot;
        s0_awqos   = m10_awqos;
        s0_awvalid = m10_awvalid & m10_slave_select[0];
        s0_wdata   = m10_wdata;
        s0_wstrb   = m10_wstrb;
        s0_wlast   = m10_wlast;
        s0_wvalid  = m10_wvalid;
        s0_bready  = m10_bready;
        s0_arid    = m10_arid;
        s0_araddr  = m10_araddr;
        s0_arlen   = m10_arlen;
        s0_arsize  = m10_arsize;
        s0_arburst = m10_arburst;
        s0_arlock  = m10_arlock;
        s0_arcache = m10_arcache;
        s0_arprot  = m10_arprot;
        s0_arqos   = m10_arqos;
        s0_arvalid = m10_arvalid & m10_slave_select[0];
        s0_rready  = m10_rready;
    end
 else if (m11_slave_select[0]) begin
        s0_awid    = m11_awid;
        s0_awaddr  = m11_awaddr;
        s0_awlen   = m11_awlen;
        s0_awsize  = m11_awsize;
        s0_awburst = m11_awburst;
        s0_awlock  = m11_awlock;
        s0_awcache = m11_awcache;
        s0_awprot  = m11_awprot;
        s0_awqos   = m11_awqos;
        s0_awvalid = m11_awvalid & m11_slave_select[0];
        s0_wdata   = m11_wdata;
        s0_wstrb   = m11_wstrb;
        s0_wlast   = m11_wlast;
        s0_wvalid  = m11_wvalid;
        s0_bready  = m11_bready;
        s0_arid    = m11_arid;
        s0_araddr  = m11_araddr;
        s0_arlen   = m11_arlen;
        s0_arsize  = m11_arsize;
        s0_arburst = m11_arburst;
        s0_arlock  = m11_arlock;
        s0_arcache = m11_arcache;
        s0_arprot  = m11_arprot;
        s0_arqos   = m11_arqos;
        s0_arvalid = m11_arvalid & m11_slave_select[0];
        s0_rready  = m11_rready;
    end
 else if (m12_slave_select[0]) begin
        s0_awid    = m12_awid;
        s0_awaddr  = m12_awaddr;
        s0_awlen   = m12_awlen;
        s0_awsize  = m12_awsize;
        s0_awburst = m12_awburst;
        s0_awlock  = m12_awlock;
        s0_awcache = m12_awcache;
        s0_awprot  = m12_awprot;
        s0_awqos   = m12_awqos;
        s0_awvalid = m12_awvalid & m12_slave_select[0];
        s0_wdata   = m12_wdata;
        s0_wstrb   = m12_wstrb;
        s0_wlast   = m12_wlast;
        s0_wvalid  = m12_wvalid;
        s0_bready  = m12_bready;
        s0_arid    = m12_arid;
        s0_araddr  = m12_araddr;
        s0_arlen   = m12_arlen;
        s0_arsize  = m12_arsize;
        s0_arburst = m12_arburst;
        s0_arlock  = m12_arlock;
        s0_arcache = m12_arcache;
        s0_arprot  = m12_arprot;
        s0_arqos   = m12_arqos;
        s0_arvalid = m12_arvalid & m12_slave_select[0];
        s0_rready  = m12_rready;
    end
 else if (m13_slave_select[0]) begin
        s0_awid    = m13_awid;
        s0_awaddr  = m13_awaddr;
        s0_awlen   = m13_awlen;
        s0_awsize  = m13_awsize;
        s0_awburst = m13_awburst;
        s0_awlock  = m13_awlock;
        s0_awcache = m13_awcache;
        s0_awprot  = m13_awprot;
        s0_awqos   = m13_awqos;
        s0_awvalid = m13_awvalid & m13_slave_select[0];
        s0_wdata   = m13_wdata;
        s0_wstrb   = m13_wstrb;
        s0_wlast   = m13_wlast;
        s0_wvalid  = m13_wvalid;
        s0_bready  = m13_bready;
        s0_arid    = m13_arid;
        s0_araddr  = m13_araddr;
        s0_arlen   = m13_arlen;
        s0_arsize  = m13_arsize;
        s0_arburst = m13_arburst;
        s0_arlock  = m13_arlock;
        s0_arcache = m13_arcache;
        s0_arprot  = m13_arprot;
        s0_arqos   = m13_arqos;
        s0_arvalid = m13_arvalid & m13_slave_select[0];
        s0_rready  = m13_rready;
    end
 else if (m14_slave_select[0]) begin
        s0_awid    = m14_awid;
        s0_awaddr  = m14_awaddr;
        s0_awlen   = m14_awlen;
        s0_awsize  = m14_awsize;
        s0_awburst = m14_awburst;
        s0_awlock  = m14_awlock;
        s0_awcache = m14_awcache;
        s0_awprot  = m14_awprot;
        s0_awqos   = m14_awqos;
        s0_awvalid = m14_awvalid & m14_slave_select[0];
        s0_wdata   = m14_wdata;
        s0_wstrb   = m14_wstrb;
        s0_wlast   = m14_wlast;
        s0_wvalid  = m14_wvalid;
        s0_bready  = m14_bready;
        s0_arid    = m14_arid;
        s0_araddr  = m14_araddr;
        s0_arlen   = m14_arlen;
        s0_arsize  = m14_arsize;
        s0_arburst = m14_arburst;
        s0_arlock  = m14_arlock;
        s0_arcache = m14_arcache;
        s0_arprot  = m14_arprot;
        s0_arqos   = m14_arqos;
        s0_arvalid = m14_arvalid & m14_slave_select[0];
        s0_rready  = m14_rready;
    end

end


// Slave 1 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s1_awid    = 'b0;
    s1_awaddr  = 'b0;
    s1_awlen   = 'b0;
    s1_awsize  = 'b0;
    s1_awburst = 'b0;
    s1_awlock  = 'b0;
    s1_awcache = 'b0;
    s1_awprot  = 'b0;
    s1_awqos   = 'b0;
    s1_awvalid = 'b0;
    s1_wdata   = 'b0;
    s1_wstrb   = 'b0;
    s1_wlast   = 'b0;
    s1_wvalid  = 'b0;
    s1_bready  = 'b0;
    s1_arid    = 'b0;
    s1_araddr  = 'b0;
    s1_arlen   = 'b0;
    s1_arsize  = 'b0;
    s1_arburst = 'b0;
    s1_arlock  = 'b0;
    s1_arcache = 'b0;
    s1_arprot  = 'b0;
    s1_arqos   = 'b0;
    s1_arvalid = 'b0;
    s1_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[1]) begin
        s1_awid    = m0_awid;
        s1_awaddr  = m0_awaddr;
        s1_awlen   = m0_awlen;
        s1_awsize  = m0_awsize;
        s1_awburst = m0_awburst;
        s1_awlock  = m0_awlock;
        s1_awcache = m0_awcache;
        s1_awprot  = m0_awprot;
        s1_awqos   = m0_awqos;
        s1_awvalid = m0_awvalid & m0_slave_select[1];
        s1_wdata   = m0_wdata;
        s1_wstrb   = m0_wstrb;
        s1_wlast   = m0_wlast;
        s1_wvalid  = m0_wvalid;
        s1_bready  = m0_bready;
        s1_arid    = m0_arid;
        s1_araddr  = m0_araddr;
        s1_arlen   = m0_arlen;
        s1_arsize  = m0_arsize;
        s1_arburst = m0_arburst;
        s1_arlock  = m0_arlock;
        s1_arcache = m0_arcache;
        s1_arprot  = m0_arprot;
        s1_arqos   = m0_arqos;
        s1_arvalid = m0_arvalid & m0_slave_select[1];
        s1_rready  = m0_rready;
    end
 else if (m1_slave_select[1]) begin
        s1_awid    = m1_awid;
        s1_awaddr  = m1_awaddr;
        s1_awlen   = m1_awlen;
        s1_awsize  = m1_awsize;
        s1_awburst = m1_awburst;
        s1_awlock  = m1_awlock;
        s1_awcache = m1_awcache;
        s1_awprot  = m1_awprot;
        s1_awqos   = m1_awqos;
        s1_awvalid = m1_awvalid & m1_slave_select[1];
        s1_wdata   = m1_wdata;
        s1_wstrb   = m1_wstrb;
        s1_wlast   = m1_wlast;
        s1_wvalid  = m1_wvalid;
        s1_bready  = m1_bready;
        s1_arid    = m1_arid;
        s1_araddr  = m1_araddr;
        s1_arlen   = m1_arlen;
        s1_arsize  = m1_arsize;
        s1_arburst = m1_arburst;
        s1_arlock  = m1_arlock;
        s1_arcache = m1_arcache;
        s1_arprot  = m1_arprot;
        s1_arqos   = m1_arqos;
        s1_arvalid = m1_arvalid & m1_slave_select[1];
        s1_rready  = m1_rready;
    end
 else if (m2_slave_select[1]) begin
        s1_awid    = m2_awid;
        s1_awaddr  = m2_awaddr;
        s1_awlen   = m2_awlen;
        s1_awsize  = m2_awsize;
        s1_awburst = m2_awburst;
        s1_awlock  = m2_awlock;
        s1_awcache = m2_awcache;
        s1_awprot  = m2_awprot;
        s1_awqos   = m2_awqos;
        s1_awvalid = m2_awvalid & m2_slave_select[1];
        s1_wdata   = m2_wdata;
        s1_wstrb   = m2_wstrb;
        s1_wlast   = m2_wlast;
        s1_wvalid  = m2_wvalid;
        s1_bready  = m2_bready;
        s1_arid    = m2_arid;
        s1_araddr  = m2_araddr;
        s1_arlen   = m2_arlen;
        s1_arsize  = m2_arsize;
        s1_arburst = m2_arburst;
        s1_arlock  = m2_arlock;
        s1_arcache = m2_arcache;
        s1_arprot  = m2_arprot;
        s1_arqos   = m2_arqos;
        s1_arvalid = m2_arvalid & m2_slave_select[1];
        s1_rready  = m2_rready;
    end
 else if (m3_slave_select[1]) begin
        s1_awid    = m3_awid;
        s1_awaddr  = m3_awaddr;
        s1_awlen   = m3_awlen;
        s1_awsize  = m3_awsize;
        s1_awburst = m3_awburst;
        s1_awlock  = m3_awlock;
        s1_awcache = m3_awcache;
        s1_awprot  = m3_awprot;
        s1_awqos   = m3_awqos;
        s1_awvalid = m3_awvalid & m3_slave_select[1];
        s1_wdata   = m3_wdata;
        s1_wstrb   = m3_wstrb;
        s1_wlast   = m3_wlast;
        s1_wvalid  = m3_wvalid;
        s1_bready  = m3_bready;
        s1_arid    = m3_arid;
        s1_araddr  = m3_araddr;
        s1_arlen   = m3_arlen;
        s1_arsize  = m3_arsize;
        s1_arburst = m3_arburst;
        s1_arlock  = m3_arlock;
        s1_arcache = m3_arcache;
        s1_arprot  = m3_arprot;
        s1_arqos   = m3_arqos;
        s1_arvalid = m3_arvalid & m3_slave_select[1];
        s1_rready  = m3_rready;
    end
 else if (m4_slave_select[1]) begin
        s1_awid    = m4_awid;
        s1_awaddr  = m4_awaddr;
        s1_awlen   = m4_awlen;
        s1_awsize  = m4_awsize;
        s1_awburst = m4_awburst;
        s1_awlock  = m4_awlock;
        s1_awcache = m4_awcache;
        s1_awprot  = m4_awprot;
        s1_awqos   = m4_awqos;
        s1_awvalid = m4_awvalid & m4_slave_select[1];
        s1_wdata   = m4_wdata;
        s1_wstrb   = m4_wstrb;
        s1_wlast   = m4_wlast;
        s1_wvalid  = m4_wvalid;
        s1_bready  = m4_bready;
        s1_arid    = m4_arid;
        s1_araddr  = m4_araddr;
        s1_arlen   = m4_arlen;
        s1_arsize  = m4_arsize;
        s1_arburst = m4_arburst;
        s1_arlock  = m4_arlock;
        s1_arcache = m4_arcache;
        s1_arprot  = m4_arprot;
        s1_arqos   = m4_arqos;
        s1_arvalid = m4_arvalid & m4_slave_select[1];
        s1_rready  = m4_rready;
    end
 else if (m5_slave_select[1]) begin
        s1_awid    = m5_awid;
        s1_awaddr  = m5_awaddr;
        s1_awlen   = m5_awlen;
        s1_awsize  = m5_awsize;
        s1_awburst = m5_awburst;
        s1_awlock  = m5_awlock;
        s1_awcache = m5_awcache;
        s1_awprot  = m5_awprot;
        s1_awqos   = m5_awqos;
        s1_awvalid = m5_awvalid & m5_slave_select[1];
        s1_wdata   = m5_wdata;
        s1_wstrb   = m5_wstrb;
        s1_wlast   = m5_wlast;
        s1_wvalid  = m5_wvalid;
        s1_bready  = m5_bready;
        s1_arid    = m5_arid;
        s1_araddr  = m5_araddr;
        s1_arlen   = m5_arlen;
        s1_arsize  = m5_arsize;
        s1_arburst = m5_arburst;
        s1_arlock  = m5_arlock;
        s1_arcache = m5_arcache;
        s1_arprot  = m5_arprot;
        s1_arqos   = m5_arqos;
        s1_arvalid = m5_arvalid & m5_slave_select[1];
        s1_rready  = m5_rready;
    end
 else if (m6_slave_select[1]) begin
        s1_awid    = m6_awid;
        s1_awaddr  = m6_awaddr;
        s1_awlen   = m6_awlen;
        s1_awsize  = m6_awsize;
        s1_awburst = m6_awburst;
        s1_awlock  = m6_awlock;
        s1_awcache = m6_awcache;
        s1_awprot  = m6_awprot;
        s1_awqos   = m6_awqos;
        s1_awvalid = m6_awvalid & m6_slave_select[1];
        s1_wdata   = m6_wdata;
        s1_wstrb   = m6_wstrb;
        s1_wlast   = m6_wlast;
        s1_wvalid  = m6_wvalid;
        s1_bready  = m6_bready;
        s1_arid    = m6_arid;
        s1_araddr  = m6_araddr;
        s1_arlen   = m6_arlen;
        s1_arsize  = m6_arsize;
        s1_arburst = m6_arburst;
        s1_arlock  = m6_arlock;
        s1_arcache = m6_arcache;
        s1_arprot  = m6_arprot;
        s1_arqos   = m6_arqos;
        s1_arvalid = m6_arvalid & m6_slave_select[1];
        s1_rready  = m6_rready;
    end
 else if (m7_slave_select[1]) begin
        s1_awid    = m7_awid;
        s1_awaddr  = m7_awaddr;
        s1_awlen   = m7_awlen;
        s1_awsize  = m7_awsize;
        s1_awburst = m7_awburst;
        s1_awlock  = m7_awlock;
        s1_awcache = m7_awcache;
        s1_awprot  = m7_awprot;
        s1_awqos   = m7_awqos;
        s1_awvalid = m7_awvalid & m7_slave_select[1];
        s1_wdata   = m7_wdata;
        s1_wstrb   = m7_wstrb;
        s1_wlast   = m7_wlast;
        s1_wvalid  = m7_wvalid;
        s1_bready  = m7_bready;
        s1_arid    = m7_arid;
        s1_araddr  = m7_araddr;
        s1_arlen   = m7_arlen;
        s1_arsize  = m7_arsize;
        s1_arburst = m7_arburst;
        s1_arlock  = m7_arlock;
        s1_arcache = m7_arcache;
        s1_arprot  = m7_arprot;
        s1_arqos   = m7_arqos;
        s1_arvalid = m7_arvalid & m7_slave_select[1];
        s1_rready  = m7_rready;
    end
 else if (m8_slave_select[1]) begin
        s1_awid    = m8_awid;
        s1_awaddr  = m8_awaddr;
        s1_awlen   = m8_awlen;
        s1_awsize  = m8_awsize;
        s1_awburst = m8_awburst;
        s1_awlock  = m8_awlock;
        s1_awcache = m8_awcache;
        s1_awprot  = m8_awprot;
        s1_awqos   = m8_awqos;
        s1_awvalid = m8_awvalid & m8_slave_select[1];
        s1_wdata   = m8_wdata;
        s1_wstrb   = m8_wstrb;
        s1_wlast   = m8_wlast;
        s1_wvalid  = m8_wvalid;
        s1_bready  = m8_bready;
        s1_arid    = m8_arid;
        s1_araddr  = m8_araddr;
        s1_arlen   = m8_arlen;
        s1_arsize  = m8_arsize;
        s1_arburst = m8_arburst;
        s1_arlock  = m8_arlock;
        s1_arcache = m8_arcache;
        s1_arprot  = m8_arprot;
        s1_arqos   = m8_arqos;
        s1_arvalid = m8_arvalid & m8_slave_select[1];
        s1_rready  = m8_rready;
    end
 else if (m9_slave_select[1]) begin
        s1_awid    = m9_awid;
        s1_awaddr  = m9_awaddr;
        s1_awlen   = m9_awlen;
        s1_awsize  = m9_awsize;
        s1_awburst = m9_awburst;
        s1_awlock  = m9_awlock;
        s1_awcache = m9_awcache;
        s1_awprot  = m9_awprot;
        s1_awqos   = m9_awqos;
        s1_awvalid = m9_awvalid & m9_slave_select[1];
        s1_wdata   = m9_wdata;
        s1_wstrb   = m9_wstrb;
        s1_wlast   = m9_wlast;
        s1_wvalid  = m9_wvalid;
        s1_bready  = m9_bready;
        s1_arid    = m9_arid;
        s1_araddr  = m9_araddr;
        s1_arlen   = m9_arlen;
        s1_arsize  = m9_arsize;
        s1_arburst = m9_arburst;
        s1_arlock  = m9_arlock;
        s1_arcache = m9_arcache;
        s1_arprot  = m9_arprot;
        s1_arqos   = m9_arqos;
        s1_arvalid = m9_arvalid & m9_slave_select[1];
        s1_rready  = m9_rready;
    end
 else if (m10_slave_select[1]) begin
        s1_awid    = m10_awid;
        s1_awaddr  = m10_awaddr;
        s1_awlen   = m10_awlen;
        s1_awsize  = m10_awsize;
        s1_awburst = m10_awburst;
        s1_awlock  = m10_awlock;
        s1_awcache = m10_awcache;
        s1_awprot  = m10_awprot;
        s1_awqos   = m10_awqos;
        s1_awvalid = m10_awvalid & m10_slave_select[1];
        s1_wdata   = m10_wdata;
        s1_wstrb   = m10_wstrb;
        s1_wlast   = m10_wlast;
        s1_wvalid  = m10_wvalid;
        s1_bready  = m10_bready;
        s1_arid    = m10_arid;
        s1_araddr  = m10_araddr;
        s1_arlen   = m10_arlen;
        s1_arsize  = m10_arsize;
        s1_arburst = m10_arburst;
        s1_arlock  = m10_arlock;
        s1_arcache = m10_arcache;
        s1_arprot  = m10_arprot;
        s1_arqos   = m10_arqos;
        s1_arvalid = m10_arvalid & m10_slave_select[1];
        s1_rready  = m10_rready;
    end
 else if (m11_slave_select[1]) begin
        s1_awid    = m11_awid;
        s1_awaddr  = m11_awaddr;
        s1_awlen   = m11_awlen;
        s1_awsize  = m11_awsize;
        s1_awburst = m11_awburst;
        s1_awlock  = m11_awlock;
        s1_awcache = m11_awcache;
        s1_awprot  = m11_awprot;
        s1_awqos   = m11_awqos;
        s1_awvalid = m11_awvalid & m11_slave_select[1];
        s1_wdata   = m11_wdata;
        s1_wstrb   = m11_wstrb;
        s1_wlast   = m11_wlast;
        s1_wvalid  = m11_wvalid;
        s1_bready  = m11_bready;
        s1_arid    = m11_arid;
        s1_araddr  = m11_araddr;
        s1_arlen   = m11_arlen;
        s1_arsize  = m11_arsize;
        s1_arburst = m11_arburst;
        s1_arlock  = m11_arlock;
        s1_arcache = m11_arcache;
        s1_arprot  = m11_arprot;
        s1_arqos   = m11_arqos;
        s1_arvalid = m11_arvalid & m11_slave_select[1];
        s1_rready  = m11_rready;
    end
 else if (m12_slave_select[1]) begin
        s1_awid    = m12_awid;
        s1_awaddr  = m12_awaddr;
        s1_awlen   = m12_awlen;
        s1_awsize  = m12_awsize;
        s1_awburst = m12_awburst;
        s1_awlock  = m12_awlock;
        s1_awcache = m12_awcache;
        s1_awprot  = m12_awprot;
        s1_awqos   = m12_awqos;
        s1_awvalid = m12_awvalid & m12_slave_select[1];
        s1_wdata   = m12_wdata;
        s1_wstrb   = m12_wstrb;
        s1_wlast   = m12_wlast;
        s1_wvalid  = m12_wvalid;
        s1_bready  = m12_bready;
        s1_arid    = m12_arid;
        s1_araddr  = m12_araddr;
        s1_arlen   = m12_arlen;
        s1_arsize  = m12_arsize;
        s1_arburst = m12_arburst;
        s1_arlock  = m12_arlock;
        s1_arcache = m12_arcache;
        s1_arprot  = m12_arprot;
        s1_arqos   = m12_arqos;
        s1_arvalid = m12_arvalid & m12_slave_select[1];
        s1_rready  = m12_rready;
    end
 else if (m13_slave_select[1]) begin
        s1_awid    = m13_awid;
        s1_awaddr  = m13_awaddr;
        s1_awlen   = m13_awlen;
        s1_awsize  = m13_awsize;
        s1_awburst = m13_awburst;
        s1_awlock  = m13_awlock;
        s1_awcache = m13_awcache;
        s1_awprot  = m13_awprot;
        s1_awqos   = m13_awqos;
        s1_awvalid = m13_awvalid & m13_slave_select[1];
        s1_wdata   = m13_wdata;
        s1_wstrb   = m13_wstrb;
        s1_wlast   = m13_wlast;
        s1_wvalid  = m13_wvalid;
        s1_bready  = m13_bready;
        s1_arid    = m13_arid;
        s1_araddr  = m13_araddr;
        s1_arlen   = m13_arlen;
        s1_arsize  = m13_arsize;
        s1_arburst = m13_arburst;
        s1_arlock  = m13_arlock;
        s1_arcache = m13_arcache;
        s1_arprot  = m13_arprot;
        s1_arqos   = m13_arqos;
        s1_arvalid = m13_arvalid & m13_slave_select[1];
        s1_rready  = m13_rready;
    end
 else if (m14_slave_select[1]) begin
        s1_awid    = m14_awid;
        s1_awaddr  = m14_awaddr;
        s1_awlen   = m14_awlen;
        s1_awsize  = m14_awsize;
        s1_awburst = m14_awburst;
        s1_awlock  = m14_awlock;
        s1_awcache = m14_awcache;
        s1_awprot  = m14_awprot;
        s1_awqos   = m14_awqos;
        s1_awvalid = m14_awvalid & m14_slave_select[1];
        s1_wdata   = m14_wdata;
        s1_wstrb   = m14_wstrb;
        s1_wlast   = m14_wlast;
        s1_wvalid  = m14_wvalid;
        s1_bready  = m14_bready;
        s1_arid    = m14_arid;
        s1_araddr  = m14_araddr;
        s1_arlen   = m14_arlen;
        s1_arsize  = m14_arsize;
        s1_arburst = m14_arburst;
        s1_arlock  = m14_arlock;
        s1_arcache = m14_arcache;
        s1_arprot  = m14_arprot;
        s1_arqos   = m14_arqos;
        s1_arvalid = m14_arvalid & m14_slave_select[1];
        s1_rready  = m14_rready;
    end

end


// Slave 2 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s2_awid    = 'b0;
    s2_awaddr  = 'b0;
    s2_awlen   = 'b0;
    s2_awsize  = 'b0;
    s2_awburst = 'b0;
    s2_awlock  = 'b0;
    s2_awcache = 'b0;
    s2_awprot  = 'b0;
    s2_awqos   = 'b0;
    s2_awvalid = 'b0;
    s2_wdata   = 'b0;
    s2_wstrb   = 'b0;
    s2_wlast   = 'b0;
    s2_wvalid  = 'b0;
    s2_bready  = 'b0;
    s2_arid    = 'b0;
    s2_araddr  = 'b0;
    s2_arlen   = 'b0;
    s2_arsize  = 'b0;
    s2_arburst = 'b0;
    s2_arlock  = 'b0;
    s2_arcache = 'b0;
    s2_arprot  = 'b0;
    s2_arqos   = 'b0;
    s2_arvalid = 'b0;
    s2_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[2]) begin
        s2_awid    = m0_awid;
        s2_awaddr  = m0_awaddr;
        s2_awlen   = m0_awlen;
        s2_awsize  = m0_awsize;
        s2_awburst = m0_awburst;
        s2_awlock  = m0_awlock;
        s2_awcache = m0_awcache;
        s2_awprot  = m0_awprot;
        s2_awqos   = m0_awqos;
        s2_awvalid = m0_awvalid & m0_slave_select[2];
        s2_wdata   = m0_wdata;
        s2_wstrb   = m0_wstrb;
        s2_wlast   = m0_wlast;
        s2_wvalid  = m0_wvalid;
        s2_bready  = m0_bready;
        s2_arid    = m0_arid;
        s2_araddr  = m0_araddr;
        s2_arlen   = m0_arlen;
        s2_arsize  = m0_arsize;
        s2_arburst = m0_arburst;
        s2_arlock  = m0_arlock;
        s2_arcache = m0_arcache;
        s2_arprot  = m0_arprot;
        s2_arqos   = m0_arqos;
        s2_arvalid = m0_arvalid & m0_slave_select[2];
        s2_rready  = m0_rready;
    end
 else if (m1_slave_select[2]) begin
        s2_awid    = m1_awid;
        s2_awaddr  = m1_awaddr;
        s2_awlen   = m1_awlen;
        s2_awsize  = m1_awsize;
        s2_awburst = m1_awburst;
        s2_awlock  = m1_awlock;
        s2_awcache = m1_awcache;
        s2_awprot  = m1_awprot;
        s2_awqos   = m1_awqos;
        s2_awvalid = m1_awvalid & m1_slave_select[2];
        s2_wdata   = m1_wdata;
        s2_wstrb   = m1_wstrb;
        s2_wlast   = m1_wlast;
        s2_wvalid  = m1_wvalid;
        s2_bready  = m1_bready;
        s2_arid    = m1_arid;
        s2_araddr  = m1_araddr;
        s2_arlen   = m1_arlen;
        s2_arsize  = m1_arsize;
        s2_arburst = m1_arburst;
        s2_arlock  = m1_arlock;
        s2_arcache = m1_arcache;
        s2_arprot  = m1_arprot;
        s2_arqos   = m1_arqos;
        s2_arvalid = m1_arvalid & m1_slave_select[2];
        s2_rready  = m1_rready;
    end
 else if (m2_slave_select[2]) begin
        s2_awid    = m2_awid;
        s2_awaddr  = m2_awaddr;
        s2_awlen   = m2_awlen;
        s2_awsize  = m2_awsize;
        s2_awburst = m2_awburst;
        s2_awlock  = m2_awlock;
        s2_awcache = m2_awcache;
        s2_awprot  = m2_awprot;
        s2_awqos   = m2_awqos;
        s2_awvalid = m2_awvalid & m2_slave_select[2];
        s2_wdata   = m2_wdata;
        s2_wstrb   = m2_wstrb;
        s2_wlast   = m2_wlast;
        s2_wvalid  = m2_wvalid;
        s2_bready  = m2_bready;
        s2_arid    = m2_arid;
        s2_araddr  = m2_araddr;
        s2_arlen   = m2_arlen;
        s2_arsize  = m2_arsize;
        s2_arburst = m2_arburst;
        s2_arlock  = m2_arlock;
        s2_arcache = m2_arcache;
        s2_arprot  = m2_arprot;
        s2_arqos   = m2_arqos;
        s2_arvalid = m2_arvalid & m2_slave_select[2];
        s2_rready  = m2_rready;
    end
 else if (m3_slave_select[2]) begin
        s2_awid    = m3_awid;
        s2_awaddr  = m3_awaddr;
        s2_awlen   = m3_awlen;
        s2_awsize  = m3_awsize;
        s2_awburst = m3_awburst;
        s2_awlock  = m3_awlock;
        s2_awcache = m3_awcache;
        s2_awprot  = m3_awprot;
        s2_awqos   = m3_awqos;
        s2_awvalid = m3_awvalid & m3_slave_select[2];
        s2_wdata   = m3_wdata;
        s2_wstrb   = m3_wstrb;
        s2_wlast   = m3_wlast;
        s2_wvalid  = m3_wvalid;
        s2_bready  = m3_bready;
        s2_arid    = m3_arid;
        s2_araddr  = m3_araddr;
        s2_arlen   = m3_arlen;
        s2_arsize  = m3_arsize;
        s2_arburst = m3_arburst;
        s2_arlock  = m3_arlock;
        s2_arcache = m3_arcache;
        s2_arprot  = m3_arprot;
        s2_arqos   = m3_arqos;
        s2_arvalid = m3_arvalid & m3_slave_select[2];
        s2_rready  = m3_rready;
    end
 else if (m4_slave_select[2]) begin
        s2_awid    = m4_awid;
        s2_awaddr  = m4_awaddr;
        s2_awlen   = m4_awlen;
        s2_awsize  = m4_awsize;
        s2_awburst = m4_awburst;
        s2_awlock  = m4_awlock;
        s2_awcache = m4_awcache;
        s2_awprot  = m4_awprot;
        s2_awqos   = m4_awqos;
        s2_awvalid = m4_awvalid & m4_slave_select[2];
        s2_wdata   = m4_wdata;
        s2_wstrb   = m4_wstrb;
        s2_wlast   = m4_wlast;
        s2_wvalid  = m4_wvalid;
        s2_bready  = m4_bready;
        s2_arid    = m4_arid;
        s2_araddr  = m4_araddr;
        s2_arlen   = m4_arlen;
        s2_arsize  = m4_arsize;
        s2_arburst = m4_arburst;
        s2_arlock  = m4_arlock;
        s2_arcache = m4_arcache;
        s2_arprot  = m4_arprot;
        s2_arqos   = m4_arqos;
        s2_arvalid = m4_arvalid & m4_slave_select[2];
        s2_rready  = m4_rready;
    end
 else if (m5_slave_select[2]) begin
        s2_awid    = m5_awid;
        s2_awaddr  = m5_awaddr;
        s2_awlen   = m5_awlen;
        s2_awsize  = m5_awsize;
        s2_awburst = m5_awburst;
        s2_awlock  = m5_awlock;
        s2_awcache = m5_awcache;
        s2_awprot  = m5_awprot;
        s2_awqos   = m5_awqos;
        s2_awvalid = m5_awvalid & m5_slave_select[2];
        s2_wdata   = m5_wdata;
        s2_wstrb   = m5_wstrb;
        s2_wlast   = m5_wlast;
        s2_wvalid  = m5_wvalid;
        s2_bready  = m5_bready;
        s2_arid    = m5_arid;
        s2_araddr  = m5_araddr;
        s2_arlen   = m5_arlen;
        s2_arsize  = m5_arsize;
        s2_arburst = m5_arburst;
        s2_arlock  = m5_arlock;
        s2_arcache = m5_arcache;
        s2_arprot  = m5_arprot;
        s2_arqos   = m5_arqos;
        s2_arvalid = m5_arvalid & m5_slave_select[2];
        s2_rready  = m5_rready;
    end
 else if (m6_slave_select[2]) begin
        s2_awid    = m6_awid;
        s2_awaddr  = m6_awaddr;
        s2_awlen   = m6_awlen;
        s2_awsize  = m6_awsize;
        s2_awburst = m6_awburst;
        s2_awlock  = m6_awlock;
        s2_awcache = m6_awcache;
        s2_awprot  = m6_awprot;
        s2_awqos   = m6_awqos;
        s2_awvalid = m6_awvalid & m6_slave_select[2];
        s2_wdata   = m6_wdata;
        s2_wstrb   = m6_wstrb;
        s2_wlast   = m6_wlast;
        s2_wvalid  = m6_wvalid;
        s2_bready  = m6_bready;
        s2_arid    = m6_arid;
        s2_araddr  = m6_araddr;
        s2_arlen   = m6_arlen;
        s2_arsize  = m6_arsize;
        s2_arburst = m6_arburst;
        s2_arlock  = m6_arlock;
        s2_arcache = m6_arcache;
        s2_arprot  = m6_arprot;
        s2_arqos   = m6_arqos;
        s2_arvalid = m6_arvalid & m6_slave_select[2];
        s2_rready  = m6_rready;
    end
 else if (m7_slave_select[2]) begin
        s2_awid    = m7_awid;
        s2_awaddr  = m7_awaddr;
        s2_awlen   = m7_awlen;
        s2_awsize  = m7_awsize;
        s2_awburst = m7_awburst;
        s2_awlock  = m7_awlock;
        s2_awcache = m7_awcache;
        s2_awprot  = m7_awprot;
        s2_awqos   = m7_awqos;
        s2_awvalid = m7_awvalid & m7_slave_select[2];
        s2_wdata   = m7_wdata;
        s2_wstrb   = m7_wstrb;
        s2_wlast   = m7_wlast;
        s2_wvalid  = m7_wvalid;
        s2_bready  = m7_bready;
        s2_arid    = m7_arid;
        s2_araddr  = m7_araddr;
        s2_arlen   = m7_arlen;
        s2_arsize  = m7_arsize;
        s2_arburst = m7_arburst;
        s2_arlock  = m7_arlock;
        s2_arcache = m7_arcache;
        s2_arprot  = m7_arprot;
        s2_arqos   = m7_arqos;
        s2_arvalid = m7_arvalid & m7_slave_select[2];
        s2_rready  = m7_rready;
    end
 else if (m8_slave_select[2]) begin
        s2_awid    = m8_awid;
        s2_awaddr  = m8_awaddr;
        s2_awlen   = m8_awlen;
        s2_awsize  = m8_awsize;
        s2_awburst = m8_awburst;
        s2_awlock  = m8_awlock;
        s2_awcache = m8_awcache;
        s2_awprot  = m8_awprot;
        s2_awqos   = m8_awqos;
        s2_awvalid = m8_awvalid & m8_slave_select[2];
        s2_wdata   = m8_wdata;
        s2_wstrb   = m8_wstrb;
        s2_wlast   = m8_wlast;
        s2_wvalid  = m8_wvalid;
        s2_bready  = m8_bready;
        s2_arid    = m8_arid;
        s2_araddr  = m8_araddr;
        s2_arlen   = m8_arlen;
        s2_arsize  = m8_arsize;
        s2_arburst = m8_arburst;
        s2_arlock  = m8_arlock;
        s2_arcache = m8_arcache;
        s2_arprot  = m8_arprot;
        s2_arqos   = m8_arqos;
        s2_arvalid = m8_arvalid & m8_slave_select[2];
        s2_rready  = m8_rready;
    end
 else if (m9_slave_select[2]) begin
        s2_awid    = m9_awid;
        s2_awaddr  = m9_awaddr;
        s2_awlen   = m9_awlen;
        s2_awsize  = m9_awsize;
        s2_awburst = m9_awburst;
        s2_awlock  = m9_awlock;
        s2_awcache = m9_awcache;
        s2_awprot  = m9_awprot;
        s2_awqos   = m9_awqos;
        s2_awvalid = m9_awvalid & m9_slave_select[2];
        s2_wdata   = m9_wdata;
        s2_wstrb   = m9_wstrb;
        s2_wlast   = m9_wlast;
        s2_wvalid  = m9_wvalid;
        s2_bready  = m9_bready;
        s2_arid    = m9_arid;
        s2_araddr  = m9_araddr;
        s2_arlen   = m9_arlen;
        s2_arsize  = m9_arsize;
        s2_arburst = m9_arburst;
        s2_arlock  = m9_arlock;
        s2_arcache = m9_arcache;
        s2_arprot  = m9_arprot;
        s2_arqos   = m9_arqos;
        s2_arvalid = m9_arvalid & m9_slave_select[2];
        s2_rready  = m9_rready;
    end
 else if (m10_slave_select[2]) begin
        s2_awid    = m10_awid;
        s2_awaddr  = m10_awaddr;
        s2_awlen   = m10_awlen;
        s2_awsize  = m10_awsize;
        s2_awburst = m10_awburst;
        s2_awlock  = m10_awlock;
        s2_awcache = m10_awcache;
        s2_awprot  = m10_awprot;
        s2_awqos   = m10_awqos;
        s2_awvalid = m10_awvalid & m10_slave_select[2];
        s2_wdata   = m10_wdata;
        s2_wstrb   = m10_wstrb;
        s2_wlast   = m10_wlast;
        s2_wvalid  = m10_wvalid;
        s2_bready  = m10_bready;
        s2_arid    = m10_arid;
        s2_araddr  = m10_araddr;
        s2_arlen   = m10_arlen;
        s2_arsize  = m10_arsize;
        s2_arburst = m10_arburst;
        s2_arlock  = m10_arlock;
        s2_arcache = m10_arcache;
        s2_arprot  = m10_arprot;
        s2_arqos   = m10_arqos;
        s2_arvalid = m10_arvalid & m10_slave_select[2];
        s2_rready  = m10_rready;
    end
 else if (m11_slave_select[2]) begin
        s2_awid    = m11_awid;
        s2_awaddr  = m11_awaddr;
        s2_awlen   = m11_awlen;
        s2_awsize  = m11_awsize;
        s2_awburst = m11_awburst;
        s2_awlock  = m11_awlock;
        s2_awcache = m11_awcache;
        s2_awprot  = m11_awprot;
        s2_awqos   = m11_awqos;
        s2_awvalid = m11_awvalid & m11_slave_select[2];
        s2_wdata   = m11_wdata;
        s2_wstrb   = m11_wstrb;
        s2_wlast   = m11_wlast;
        s2_wvalid  = m11_wvalid;
        s2_bready  = m11_bready;
        s2_arid    = m11_arid;
        s2_araddr  = m11_araddr;
        s2_arlen   = m11_arlen;
        s2_arsize  = m11_arsize;
        s2_arburst = m11_arburst;
        s2_arlock  = m11_arlock;
        s2_arcache = m11_arcache;
        s2_arprot  = m11_arprot;
        s2_arqos   = m11_arqos;
        s2_arvalid = m11_arvalid & m11_slave_select[2];
        s2_rready  = m11_rready;
    end
 else if (m12_slave_select[2]) begin
        s2_awid    = m12_awid;
        s2_awaddr  = m12_awaddr;
        s2_awlen   = m12_awlen;
        s2_awsize  = m12_awsize;
        s2_awburst = m12_awburst;
        s2_awlock  = m12_awlock;
        s2_awcache = m12_awcache;
        s2_awprot  = m12_awprot;
        s2_awqos   = m12_awqos;
        s2_awvalid = m12_awvalid & m12_slave_select[2];
        s2_wdata   = m12_wdata;
        s2_wstrb   = m12_wstrb;
        s2_wlast   = m12_wlast;
        s2_wvalid  = m12_wvalid;
        s2_bready  = m12_bready;
        s2_arid    = m12_arid;
        s2_araddr  = m12_araddr;
        s2_arlen   = m12_arlen;
        s2_arsize  = m12_arsize;
        s2_arburst = m12_arburst;
        s2_arlock  = m12_arlock;
        s2_arcache = m12_arcache;
        s2_arprot  = m12_arprot;
        s2_arqos   = m12_arqos;
        s2_arvalid = m12_arvalid & m12_slave_select[2];
        s2_rready  = m12_rready;
    end
 else if (m13_slave_select[2]) begin
        s2_awid    = m13_awid;
        s2_awaddr  = m13_awaddr;
        s2_awlen   = m13_awlen;
        s2_awsize  = m13_awsize;
        s2_awburst = m13_awburst;
        s2_awlock  = m13_awlock;
        s2_awcache = m13_awcache;
        s2_awprot  = m13_awprot;
        s2_awqos   = m13_awqos;
        s2_awvalid = m13_awvalid & m13_slave_select[2];
        s2_wdata   = m13_wdata;
        s2_wstrb   = m13_wstrb;
        s2_wlast   = m13_wlast;
        s2_wvalid  = m13_wvalid;
        s2_bready  = m13_bready;
        s2_arid    = m13_arid;
        s2_araddr  = m13_araddr;
        s2_arlen   = m13_arlen;
        s2_arsize  = m13_arsize;
        s2_arburst = m13_arburst;
        s2_arlock  = m13_arlock;
        s2_arcache = m13_arcache;
        s2_arprot  = m13_arprot;
        s2_arqos   = m13_arqos;
        s2_arvalid = m13_arvalid & m13_slave_select[2];
        s2_rready  = m13_rready;
    end
 else if (m14_slave_select[2]) begin
        s2_awid    = m14_awid;
        s2_awaddr  = m14_awaddr;
        s2_awlen   = m14_awlen;
        s2_awsize  = m14_awsize;
        s2_awburst = m14_awburst;
        s2_awlock  = m14_awlock;
        s2_awcache = m14_awcache;
        s2_awprot  = m14_awprot;
        s2_awqos   = m14_awqos;
        s2_awvalid = m14_awvalid & m14_slave_select[2];
        s2_wdata   = m14_wdata;
        s2_wstrb   = m14_wstrb;
        s2_wlast   = m14_wlast;
        s2_wvalid  = m14_wvalid;
        s2_bready  = m14_bready;
        s2_arid    = m14_arid;
        s2_araddr  = m14_araddr;
        s2_arlen   = m14_arlen;
        s2_arsize  = m14_arsize;
        s2_arburst = m14_arburst;
        s2_arlock  = m14_arlock;
        s2_arcache = m14_arcache;
        s2_arprot  = m14_arprot;
        s2_arqos   = m14_arqos;
        s2_arvalid = m14_arvalid & m14_slave_select[2];
        s2_rready  = m14_rready;
    end

end


// Slave 3 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s3_awid    = 'b0;
    s3_awaddr  = 'b0;
    s3_awlen   = 'b0;
    s3_awsize  = 'b0;
    s3_awburst = 'b0;
    s3_awlock  = 'b0;
    s3_awcache = 'b0;
    s3_awprot  = 'b0;
    s3_awqos   = 'b0;
    s3_awvalid = 'b0;
    s3_wdata   = 'b0;
    s3_wstrb   = 'b0;
    s3_wlast   = 'b0;
    s3_wvalid  = 'b0;
    s3_bready  = 'b0;
    s3_arid    = 'b0;
    s3_araddr  = 'b0;
    s3_arlen   = 'b0;
    s3_arsize  = 'b0;
    s3_arburst = 'b0;
    s3_arlock  = 'b0;
    s3_arcache = 'b0;
    s3_arprot  = 'b0;
    s3_arqos   = 'b0;
    s3_arvalid = 'b0;
    s3_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[3]) begin
        s3_awid    = m0_awid;
        s3_awaddr  = m0_awaddr;
        s3_awlen   = m0_awlen;
        s3_awsize  = m0_awsize;
        s3_awburst = m0_awburst;
        s3_awlock  = m0_awlock;
        s3_awcache = m0_awcache;
        s3_awprot  = m0_awprot;
        s3_awqos   = m0_awqos;
        s3_awvalid = m0_awvalid & m0_slave_select[3];
        s3_wdata   = m0_wdata;
        s3_wstrb   = m0_wstrb;
        s3_wlast   = m0_wlast;
        s3_wvalid  = m0_wvalid;
        s3_bready  = m0_bready;
        s3_arid    = m0_arid;
        s3_araddr  = m0_araddr;
        s3_arlen   = m0_arlen;
        s3_arsize  = m0_arsize;
        s3_arburst = m0_arburst;
        s3_arlock  = m0_arlock;
        s3_arcache = m0_arcache;
        s3_arprot  = m0_arprot;
        s3_arqos   = m0_arqos;
        s3_arvalid = m0_arvalid & m0_slave_select[3];
        s3_rready  = m0_rready;
    end
 else if (m1_slave_select[3]) begin
        s3_awid    = m1_awid;
        s3_awaddr  = m1_awaddr;
        s3_awlen   = m1_awlen;
        s3_awsize  = m1_awsize;
        s3_awburst = m1_awburst;
        s3_awlock  = m1_awlock;
        s3_awcache = m1_awcache;
        s3_awprot  = m1_awprot;
        s3_awqos   = m1_awqos;
        s3_awvalid = m1_awvalid & m1_slave_select[3];
        s3_wdata   = m1_wdata;
        s3_wstrb   = m1_wstrb;
        s3_wlast   = m1_wlast;
        s3_wvalid  = m1_wvalid;
        s3_bready  = m1_bready;
        s3_arid    = m1_arid;
        s3_araddr  = m1_araddr;
        s3_arlen   = m1_arlen;
        s3_arsize  = m1_arsize;
        s3_arburst = m1_arburst;
        s3_arlock  = m1_arlock;
        s3_arcache = m1_arcache;
        s3_arprot  = m1_arprot;
        s3_arqos   = m1_arqos;
        s3_arvalid = m1_arvalid & m1_slave_select[3];
        s3_rready  = m1_rready;
    end
 else if (m2_slave_select[3]) begin
        s3_awid    = m2_awid;
        s3_awaddr  = m2_awaddr;
        s3_awlen   = m2_awlen;
        s3_awsize  = m2_awsize;
        s3_awburst = m2_awburst;
        s3_awlock  = m2_awlock;
        s3_awcache = m2_awcache;
        s3_awprot  = m2_awprot;
        s3_awqos   = m2_awqos;
        s3_awvalid = m2_awvalid & m2_slave_select[3];
        s3_wdata   = m2_wdata;
        s3_wstrb   = m2_wstrb;
        s3_wlast   = m2_wlast;
        s3_wvalid  = m2_wvalid;
        s3_bready  = m2_bready;
        s3_arid    = m2_arid;
        s3_araddr  = m2_araddr;
        s3_arlen   = m2_arlen;
        s3_arsize  = m2_arsize;
        s3_arburst = m2_arburst;
        s3_arlock  = m2_arlock;
        s3_arcache = m2_arcache;
        s3_arprot  = m2_arprot;
        s3_arqos   = m2_arqos;
        s3_arvalid = m2_arvalid & m2_slave_select[3];
        s3_rready  = m2_rready;
    end
 else if (m3_slave_select[3]) begin
        s3_awid    = m3_awid;
        s3_awaddr  = m3_awaddr;
        s3_awlen   = m3_awlen;
        s3_awsize  = m3_awsize;
        s3_awburst = m3_awburst;
        s3_awlock  = m3_awlock;
        s3_awcache = m3_awcache;
        s3_awprot  = m3_awprot;
        s3_awqos   = m3_awqos;
        s3_awvalid = m3_awvalid & m3_slave_select[3];
        s3_wdata   = m3_wdata;
        s3_wstrb   = m3_wstrb;
        s3_wlast   = m3_wlast;
        s3_wvalid  = m3_wvalid;
        s3_bready  = m3_bready;
        s3_arid    = m3_arid;
        s3_araddr  = m3_araddr;
        s3_arlen   = m3_arlen;
        s3_arsize  = m3_arsize;
        s3_arburst = m3_arburst;
        s3_arlock  = m3_arlock;
        s3_arcache = m3_arcache;
        s3_arprot  = m3_arprot;
        s3_arqos   = m3_arqos;
        s3_arvalid = m3_arvalid & m3_slave_select[3];
        s3_rready  = m3_rready;
    end
 else if (m4_slave_select[3]) begin
        s3_awid    = m4_awid;
        s3_awaddr  = m4_awaddr;
        s3_awlen   = m4_awlen;
        s3_awsize  = m4_awsize;
        s3_awburst = m4_awburst;
        s3_awlock  = m4_awlock;
        s3_awcache = m4_awcache;
        s3_awprot  = m4_awprot;
        s3_awqos   = m4_awqos;
        s3_awvalid = m4_awvalid & m4_slave_select[3];
        s3_wdata   = m4_wdata;
        s3_wstrb   = m4_wstrb;
        s3_wlast   = m4_wlast;
        s3_wvalid  = m4_wvalid;
        s3_bready  = m4_bready;
        s3_arid    = m4_arid;
        s3_araddr  = m4_araddr;
        s3_arlen   = m4_arlen;
        s3_arsize  = m4_arsize;
        s3_arburst = m4_arburst;
        s3_arlock  = m4_arlock;
        s3_arcache = m4_arcache;
        s3_arprot  = m4_arprot;
        s3_arqos   = m4_arqos;
        s3_arvalid = m4_arvalid & m4_slave_select[3];
        s3_rready  = m4_rready;
    end
 else if (m5_slave_select[3]) begin
        s3_awid    = m5_awid;
        s3_awaddr  = m5_awaddr;
        s3_awlen   = m5_awlen;
        s3_awsize  = m5_awsize;
        s3_awburst = m5_awburst;
        s3_awlock  = m5_awlock;
        s3_awcache = m5_awcache;
        s3_awprot  = m5_awprot;
        s3_awqos   = m5_awqos;
        s3_awvalid = m5_awvalid & m5_slave_select[3];
        s3_wdata   = m5_wdata;
        s3_wstrb   = m5_wstrb;
        s3_wlast   = m5_wlast;
        s3_wvalid  = m5_wvalid;
        s3_bready  = m5_bready;
        s3_arid    = m5_arid;
        s3_araddr  = m5_araddr;
        s3_arlen   = m5_arlen;
        s3_arsize  = m5_arsize;
        s3_arburst = m5_arburst;
        s3_arlock  = m5_arlock;
        s3_arcache = m5_arcache;
        s3_arprot  = m5_arprot;
        s3_arqos   = m5_arqos;
        s3_arvalid = m5_arvalid & m5_slave_select[3];
        s3_rready  = m5_rready;
    end
 else if (m6_slave_select[3]) begin
        s3_awid    = m6_awid;
        s3_awaddr  = m6_awaddr;
        s3_awlen   = m6_awlen;
        s3_awsize  = m6_awsize;
        s3_awburst = m6_awburst;
        s3_awlock  = m6_awlock;
        s3_awcache = m6_awcache;
        s3_awprot  = m6_awprot;
        s3_awqos   = m6_awqos;
        s3_awvalid = m6_awvalid & m6_slave_select[3];
        s3_wdata   = m6_wdata;
        s3_wstrb   = m6_wstrb;
        s3_wlast   = m6_wlast;
        s3_wvalid  = m6_wvalid;
        s3_bready  = m6_bready;
        s3_arid    = m6_arid;
        s3_araddr  = m6_araddr;
        s3_arlen   = m6_arlen;
        s3_arsize  = m6_arsize;
        s3_arburst = m6_arburst;
        s3_arlock  = m6_arlock;
        s3_arcache = m6_arcache;
        s3_arprot  = m6_arprot;
        s3_arqos   = m6_arqos;
        s3_arvalid = m6_arvalid & m6_slave_select[3];
        s3_rready  = m6_rready;
    end
 else if (m7_slave_select[3]) begin
        s3_awid    = m7_awid;
        s3_awaddr  = m7_awaddr;
        s3_awlen   = m7_awlen;
        s3_awsize  = m7_awsize;
        s3_awburst = m7_awburst;
        s3_awlock  = m7_awlock;
        s3_awcache = m7_awcache;
        s3_awprot  = m7_awprot;
        s3_awqos   = m7_awqos;
        s3_awvalid = m7_awvalid & m7_slave_select[3];
        s3_wdata   = m7_wdata;
        s3_wstrb   = m7_wstrb;
        s3_wlast   = m7_wlast;
        s3_wvalid  = m7_wvalid;
        s3_bready  = m7_bready;
        s3_arid    = m7_arid;
        s3_araddr  = m7_araddr;
        s3_arlen   = m7_arlen;
        s3_arsize  = m7_arsize;
        s3_arburst = m7_arburst;
        s3_arlock  = m7_arlock;
        s3_arcache = m7_arcache;
        s3_arprot  = m7_arprot;
        s3_arqos   = m7_arqos;
        s3_arvalid = m7_arvalid & m7_slave_select[3];
        s3_rready  = m7_rready;
    end
 else if (m8_slave_select[3]) begin
        s3_awid    = m8_awid;
        s3_awaddr  = m8_awaddr;
        s3_awlen   = m8_awlen;
        s3_awsize  = m8_awsize;
        s3_awburst = m8_awburst;
        s3_awlock  = m8_awlock;
        s3_awcache = m8_awcache;
        s3_awprot  = m8_awprot;
        s3_awqos   = m8_awqos;
        s3_awvalid = m8_awvalid & m8_slave_select[3];
        s3_wdata   = m8_wdata;
        s3_wstrb   = m8_wstrb;
        s3_wlast   = m8_wlast;
        s3_wvalid  = m8_wvalid;
        s3_bready  = m8_bready;
        s3_arid    = m8_arid;
        s3_araddr  = m8_araddr;
        s3_arlen   = m8_arlen;
        s3_arsize  = m8_arsize;
        s3_arburst = m8_arburst;
        s3_arlock  = m8_arlock;
        s3_arcache = m8_arcache;
        s3_arprot  = m8_arprot;
        s3_arqos   = m8_arqos;
        s3_arvalid = m8_arvalid & m8_slave_select[3];
        s3_rready  = m8_rready;
    end
 else if (m9_slave_select[3]) begin
        s3_awid    = m9_awid;
        s3_awaddr  = m9_awaddr;
        s3_awlen   = m9_awlen;
        s3_awsize  = m9_awsize;
        s3_awburst = m9_awburst;
        s3_awlock  = m9_awlock;
        s3_awcache = m9_awcache;
        s3_awprot  = m9_awprot;
        s3_awqos   = m9_awqos;
        s3_awvalid = m9_awvalid & m9_slave_select[3];
        s3_wdata   = m9_wdata;
        s3_wstrb   = m9_wstrb;
        s3_wlast   = m9_wlast;
        s3_wvalid  = m9_wvalid;
        s3_bready  = m9_bready;
        s3_arid    = m9_arid;
        s3_araddr  = m9_araddr;
        s3_arlen   = m9_arlen;
        s3_arsize  = m9_arsize;
        s3_arburst = m9_arburst;
        s3_arlock  = m9_arlock;
        s3_arcache = m9_arcache;
        s3_arprot  = m9_arprot;
        s3_arqos   = m9_arqos;
        s3_arvalid = m9_arvalid & m9_slave_select[3];
        s3_rready  = m9_rready;
    end
 else if (m10_slave_select[3]) begin
        s3_awid    = m10_awid;
        s3_awaddr  = m10_awaddr;
        s3_awlen   = m10_awlen;
        s3_awsize  = m10_awsize;
        s3_awburst = m10_awburst;
        s3_awlock  = m10_awlock;
        s3_awcache = m10_awcache;
        s3_awprot  = m10_awprot;
        s3_awqos   = m10_awqos;
        s3_awvalid = m10_awvalid & m10_slave_select[3];
        s3_wdata   = m10_wdata;
        s3_wstrb   = m10_wstrb;
        s3_wlast   = m10_wlast;
        s3_wvalid  = m10_wvalid;
        s3_bready  = m10_bready;
        s3_arid    = m10_arid;
        s3_araddr  = m10_araddr;
        s3_arlen   = m10_arlen;
        s3_arsize  = m10_arsize;
        s3_arburst = m10_arburst;
        s3_arlock  = m10_arlock;
        s3_arcache = m10_arcache;
        s3_arprot  = m10_arprot;
        s3_arqos   = m10_arqos;
        s3_arvalid = m10_arvalid & m10_slave_select[3];
        s3_rready  = m10_rready;
    end
 else if (m11_slave_select[3]) begin
        s3_awid    = m11_awid;
        s3_awaddr  = m11_awaddr;
        s3_awlen   = m11_awlen;
        s3_awsize  = m11_awsize;
        s3_awburst = m11_awburst;
        s3_awlock  = m11_awlock;
        s3_awcache = m11_awcache;
        s3_awprot  = m11_awprot;
        s3_awqos   = m11_awqos;
        s3_awvalid = m11_awvalid & m11_slave_select[3];
        s3_wdata   = m11_wdata;
        s3_wstrb   = m11_wstrb;
        s3_wlast   = m11_wlast;
        s3_wvalid  = m11_wvalid;
        s3_bready  = m11_bready;
        s3_arid    = m11_arid;
        s3_araddr  = m11_araddr;
        s3_arlen   = m11_arlen;
        s3_arsize  = m11_arsize;
        s3_arburst = m11_arburst;
        s3_arlock  = m11_arlock;
        s3_arcache = m11_arcache;
        s3_arprot  = m11_arprot;
        s3_arqos   = m11_arqos;
        s3_arvalid = m11_arvalid & m11_slave_select[3];
        s3_rready  = m11_rready;
    end
 else if (m12_slave_select[3]) begin
        s3_awid    = m12_awid;
        s3_awaddr  = m12_awaddr;
        s3_awlen   = m12_awlen;
        s3_awsize  = m12_awsize;
        s3_awburst = m12_awburst;
        s3_awlock  = m12_awlock;
        s3_awcache = m12_awcache;
        s3_awprot  = m12_awprot;
        s3_awqos   = m12_awqos;
        s3_awvalid = m12_awvalid & m12_slave_select[3];
        s3_wdata   = m12_wdata;
        s3_wstrb   = m12_wstrb;
        s3_wlast   = m12_wlast;
        s3_wvalid  = m12_wvalid;
        s3_bready  = m12_bready;
        s3_arid    = m12_arid;
        s3_araddr  = m12_araddr;
        s3_arlen   = m12_arlen;
        s3_arsize  = m12_arsize;
        s3_arburst = m12_arburst;
        s3_arlock  = m12_arlock;
        s3_arcache = m12_arcache;
        s3_arprot  = m12_arprot;
        s3_arqos   = m12_arqos;
        s3_arvalid = m12_arvalid & m12_slave_select[3];
        s3_rready  = m12_rready;
    end
 else if (m13_slave_select[3]) begin
        s3_awid    = m13_awid;
        s3_awaddr  = m13_awaddr;
        s3_awlen   = m13_awlen;
        s3_awsize  = m13_awsize;
        s3_awburst = m13_awburst;
        s3_awlock  = m13_awlock;
        s3_awcache = m13_awcache;
        s3_awprot  = m13_awprot;
        s3_awqos   = m13_awqos;
        s3_awvalid = m13_awvalid & m13_slave_select[3];
        s3_wdata   = m13_wdata;
        s3_wstrb   = m13_wstrb;
        s3_wlast   = m13_wlast;
        s3_wvalid  = m13_wvalid;
        s3_bready  = m13_bready;
        s3_arid    = m13_arid;
        s3_araddr  = m13_araddr;
        s3_arlen   = m13_arlen;
        s3_arsize  = m13_arsize;
        s3_arburst = m13_arburst;
        s3_arlock  = m13_arlock;
        s3_arcache = m13_arcache;
        s3_arprot  = m13_arprot;
        s3_arqos   = m13_arqos;
        s3_arvalid = m13_arvalid & m13_slave_select[3];
        s3_rready  = m13_rready;
    end
 else if (m14_slave_select[3]) begin
        s3_awid    = m14_awid;
        s3_awaddr  = m14_awaddr;
        s3_awlen   = m14_awlen;
        s3_awsize  = m14_awsize;
        s3_awburst = m14_awburst;
        s3_awlock  = m14_awlock;
        s3_awcache = m14_awcache;
        s3_awprot  = m14_awprot;
        s3_awqos   = m14_awqos;
        s3_awvalid = m14_awvalid & m14_slave_select[3];
        s3_wdata   = m14_wdata;
        s3_wstrb   = m14_wstrb;
        s3_wlast   = m14_wlast;
        s3_wvalid  = m14_wvalid;
        s3_bready  = m14_bready;
        s3_arid    = m14_arid;
        s3_araddr  = m14_araddr;
        s3_arlen   = m14_arlen;
        s3_arsize  = m14_arsize;
        s3_arburst = m14_arburst;
        s3_arlock  = m14_arlock;
        s3_arcache = m14_arcache;
        s3_arprot  = m14_arprot;
        s3_arqos   = m14_arqos;
        s3_arvalid = m14_arvalid & m14_slave_select[3];
        s3_rready  = m14_rready;
    end

end


// Slave 4 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s4_awid    = 'b0;
    s4_awaddr  = 'b0;
    s4_awlen   = 'b0;
    s4_awsize  = 'b0;
    s4_awburst = 'b0;
    s4_awlock  = 'b0;
    s4_awcache = 'b0;
    s4_awprot  = 'b0;
    s4_awqos   = 'b0;
    s4_awvalid = 'b0;
    s4_wdata   = 'b0;
    s4_wstrb   = 'b0;
    s4_wlast   = 'b0;
    s4_wvalid  = 'b0;
    s4_bready  = 'b0;
    s4_arid    = 'b0;
    s4_araddr  = 'b0;
    s4_arlen   = 'b0;
    s4_arsize  = 'b0;
    s4_arburst = 'b0;
    s4_arlock  = 'b0;
    s4_arcache = 'b0;
    s4_arprot  = 'b0;
    s4_arqos   = 'b0;
    s4_arvalid = 'b0;
    s4_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[4]) begin
        s4_awid    = m0_awid;
        s4_awaddr  = m0_awaddr;
        s4_awlen   = m0_awlen;
        s4_awsize  = m0_awsize;
        s4_awburst = m0_awburst;
        s4_awlock  = m0_awlock;
        s4_awcache = m0_awcache;
        s4_awprot  = m0_awprot;
        s4_awqos   = m0_awqos;
        s4_awvalid = m0_awvalid & m0_slave_select[4];
        s4_wdata   = m0_wdata;
        s4_wstrb   = m0_wstrb;
        s4_wlast   = m0_wlast;
        s4_wvalid  = m0_wvalid;
        s4_bready  = m0_bready;
        s4_arid    = m0_arid;
        s4_araddr  = m0_araddr;
        s4_arlen   = m0_arlen;
        s4_arsize  = m0_arsize;
        s4_arburst = m0_arburst;
        s4_arlock  = m0_arlock;
        s4_arcache = m0_arcache;
        s4_arprot  = m0_arprot;
        s4_arqos   = m0_arqos;
        s4_arvalid = m0_arvalid & m0_slave_select[4];
        s4_rready  = m0_rready;
    end
 else if (m1_slave_select[4]) begin
        s4_awid    = m1_awid;
        s4_awaddr  = m1_awaddr;
        s4_awlen   = m1_awlen;
        s4_awsize  = m1_awsize;
        s4_awburst = m1_awburst;
        s4_awlock  = m1_awlock;
        s4_awcache = m1_awcache;
        s4_awprot  = m1_awprot;
        s4_awqos   = m1_awqos;
        s4_awvalid = m1_awvalid & m1_slave_select[4];
        s4_wdata   = m1_wdata;
        s4_wstrb   = m1_wstrb;
        s4_wlast   = m1_wlast;
        s4_wvalid  = m1_wvalid;
        s4_bready  = m1_bready;
        s4_arid    = m1_arid;
        s4_araddr  = m1_araddr;
        s4_arlen   = m1_arlen;
        s4_arsize  = m1_arsize;
        s4_arburst = m1_arburst;
        s4_arlock  = m1_arlock;
        s4_arcache = m1_arcache;
        s4_arprot  = m1_arprot;
        s4_arqos   = m1_arqos;
        s4_arvalid = m1_arvalid & m1_slave_select[4];
        s4_rready  = m1_rready;
    end
 else if (m2_slave_select[4]) begin
        s4_awid    = m2_awid;
        s4_awaddr  = m2_awaddr;
        s4_awlen   = m2_awlen;
        s4_awsize  = m2_awsize;
        s4_awburst = m2_awburst;
        s4_awlock  = m2_awlock;
        s4_awcache = m2_awcache;
        s4_awprot  = m2_awprot;
        s4_awqos   = m2_awqos;
        s4_awvalid = m2_awvalid & m2_slave_select[4];
        s4_wdata   = m2_wdata;
        s4_wstrb   = m2_wstrb;
        s4_wlast   = m2_wlast;
        s4_wvalid  = m2_wvalid;
        s4_bready  = m2_bready;
        s4_arid    = m2_arid;
        s4_araddr  = m2_araddr;
        s4_arlen   = m2_arlen;
        s4_arsize  = m2_arsize;
        s4_arburst = m2_arburst;
        s4_arlock  = m2_arlock;
        s4_arcache = m2_arcache;
        s4_arprot  = m2_arprot;
        s4_arqos   = m2_arqos;
        s4_arvalid = m2_arvalid & m2_slave_select[4];
        s4_rready  = m2_rready;
    end
 else if (m3_slave_select[4]) begin
        s4_awid    = m3_awid;
        s4_awaddr  = m3_awaddr;
        s4_awlen   = m3_awlen;
        s4_awsize  = m3_awsize;
        s4_awburst = m3_awburst;
        s4_awlock  = m3_awlock;
        s4_awcache = m3_awcache;
        s4_awprot  = m3_awprot;
        s4_awqos   = m3_awqos;
        s4_awvalid = m3_awvalid & m3_slave_select[4];
        s4_wdata   = m3_wdata;
        s4_wstrb   = m3_wstrb;
        s4_wlast   = m3_wlast;
        s4_wvalid  = m3_wvalid;
        s4_bready  = m3_bready;
        s4_arid    = m3_arid;
        s4_araddr  = m3_araddr;
        s4_arlen   = m3_arlen;
        s4_arsize  = m3_arsize;
        s4_arburst = m3_arburst;
        s4_arlock  = m3_arlock;
        s4_arcache = m3_arcache;
        s4_arprot  = m3_arprot;
        s4_arqos   = m3_arqos;
        s4_arvalid = m3_arvalid & m3_slave_select[4];
        s4_rready  = m3_rready;
    end
 else if (m4_slave_select[4]) begin
        s4_awid    = m4_awid;
        s4_awaddr  = m4_awaddr;
        s4_awlen   = m4_awlen;
        s4_awsize  = m4_awsize;
        s4_awburst = m4_awburst;
        s4_awlock  = m4_awlock;
        s4_awcache = m4_awcache;
        s4_awprot  = m4_awprot;
        s4_awqos   = m4_awqos;
        s4_awvalid = m4_awvalid & m4_slave_select[4];
        s4_wdata   = m4_wdata;
        s4_wstrb   = m4_wstrb;
        s4_wlast   = m4_wlast;
        s4_wvalid  = m4_wvalid;
        s4_bready  = m4_bready;
        s4_arid    = m4_arid;
        s4_araddr  = m4_araddr;
        s4_arlen   = m4_arlen;
        s4_arsize  = m4_arsize;
        s4_arburst = m4_arburst;
        s4_arlock  = m4_arlock;
        s4_arcache = m4_arcache;
        s4_arprot  = m4_arprot;
        s4_arqos   = m4_arqos;
        s4_arvalid = m4_arvalid & m4_slave_select[4];
        s4_rready  = m4_rready;
    end
 else if (m5_slave_select[4]) begin
        s4_awid    = m5_awid;
        s4_awaddr  = m5_awaddr;
        s4_awlen   = m5_awlen;
        s4_awsize  = m5_awsize;
        s4_awburst = m5_awburst;
        s4_awlock  = m5_awlock;
        s4_awcache = m5_awcache;
        s4_awprot  = m5_awprot;
        s4_awqos   = m5_awqos;
        s4_awvalid = m5_awvalid & m5_slave_select[4];
        s4_wdata   = m5_wdata;
        s4_wstrb   = m5_wstrb;
        s4_wlast   = m5_wlast;
        s4_wvalid  = m5_wvalid;
        s4_bready  = m5_bready;
        s4_arid    = m5_arid;
        s4_araddr  = m5_araddr;
        s4_arlen   = m5_arlen;
        s4_arsize  = m5_arsize;
        s4_arburst = m5_arburst;
        s4_arlock  = m5_arlock;
        s4_arcache = m5_arcache;
        s4_arprot  = m5_arprot;
        s4_arqos   = m5_arqos;
        s4_arvalid = m5_arvalid & m5_slave_select[4];
        s4_rready  = m5_rready;
    end
 else if (m6_slave_select[4]) begin
        s4_awid    = m6_awid;
        s4_awaddr  = m6_awaddr;
        s4_awlen   = m6_awlen;
        s4_awsize  = m6_awsize;
        s4_awburst = m6_awburst;
        s4_awlock  = m6_awlock;
        s4_awcache = m6_awcache;
        s4_awprot  = m6_awprot;
        s4_awqos   = m6_awqos;
        s4_awvalid = m6_awvalid & m6_slave_select[4];
        s4_wdata   = m6_wdata;
        s4_wstrb   = m6_wstrb;
        s4_wlast   = m6_wlast;
        s4_wvalid  = m6_wvalid;
        s4_bready  = m6_bready;
        s4_arid    = m6_arid;
        s4_araddr  = m6_araddr;
        s4_arlen   = m6_arlen;
        s4_arsize  = m6_arsize;
        s4_arburst = m6_arburst;
        s4_arlock  = m6_arlock;
        s4_arcache = m6_arcache;
        s4_arprot  = m6_arprot;
        s4_arqos   = m6_arqos;
        s4_arvalid = m6_arvalid & m6_slave_select[4];
        s4_rready  = m6_rready;
    end
 else if (m7_slave_select[4]) begin
        s4_awid    = m7_awid;
        s4_awaddr  = m7_awaddr;
        s4_awlen   = m7_awlen;
        s4_awsize  = m7_awsize;
        s4_awburst = m7_awburst;
        s4_awlock  = m7_awlock;
        s4_awcache = m7_awcache;
        s4_awprot  = m7_awprot;
        s4_awqos   = m7_awqos;
        s4_awvalid = m7_awvalid & m7_slave_select[4];
        s4_wdata   = m7_wdata;
        s4_wstrb   = m7_wstrb;
        s4_wlast   = m7_wlast;
        s4_wvalid  = m7_wvalid;
        s4_bready  = m7_bready;
        s4_arid    = m7_arid;
        s4_araddr  = m7_araddr;
        s4_arlen   = m7_arlen;
        s4_arsize  = m7_arsize;
        s4_arburst = m7_arburst;
        s4_arlock  = m7_arlock;
        s4_arcache = m7_arcache;
        s4_arprot  = m7_arprot;
        s4_arqos   = m7_arqos;
        s4_arvalid = m7_arvalid & m7_slave_select[4];
        s4_rready  = m7_rready;
    end
 else if (m8_slave_select[4]) begin
        s4_awid    = m8_awid;
        s4_awaddr  = m8_awaddr;
        s4_awlen   = m8_awlen;
        s4_awsize  = m8_awsize;
        s4_awburst = m8_awburst;
        s4_awlock  = m8_awlock;
        s4_awcache = m8_awcache;
        s4_awprot  = m8_awprot;
        s4_awqos   = m8_awqos;
        s4_awvalid = m8_awvalid & m8_slave_select[4];
        s4_wdata   = m8_wdata;
        s4_wstrb   = m8_wstrb;
        s4_wlast   = m8_wlast;
        s4_wvalid  = m8_wvalid;
        s4_bready  = m8_bready;
        s4_arid    = m8_arid;
        s4_araddr  = m8_araddr;
        s4_arlen   = m8_arlen;
        s4_arsize  = m8_arsize;
        s4_arburst = m8_arburst;
        s4_arlock  = m8_arlock;
        s4_arcache = m8_arcache;
        s4_arprot  = m8_arprot;
        s4_arqos   = m8_arqos;
        s4_arvalid = m8_arvalid & m8_slave_select[4];
        s4_rready  = m8_rready;
    end
 else if (m9_slave_select[4]) begin
        s4_awid    = m9_awid;
        s4_awaddr  = m9_awaddr;
        s4_awlen   = m9_awlen;
        s4_awsize  = m9_awsize;
        s4_awburst = m9_awburst;
        s4_awlock  = m9_awlock;
        s4_awcache = m9_awcache;
        s4_awprot  = m9_awprot;
        s4_awqos   = m9_awqos;
        s4_awvalid = m9_awvalid & m9_slave_select[4];
        s4_wdata   = m9_wdata;
        s4_wstrb   = m9_wstrb;
        s4_wlast   = m9_wlast;
        s4_wvalid  = m9_wvalid;
        s4_bready  = m9_bready;
        s4_arid    = m9_arid;
        s4_araddr  = m9_araddr;
        s4_arlen   = m9_arlen;
        s4_arsize  = m9_arsize;
        s4_arburst = m9_arburst;
        s4_arlock  = m9_arlock;
        s4_arcache = m9_arcache;
        s4_arprot  = m9_arprot;
        s4_arqos   = m9_arqos;
        s4_arvalid = m9_arvalid & m9_slave_select[4];
        s4_rready  = m9_rready;
    end
 else if (m10_slave_select[4]) begin
        s4_awid    = m10_awid;
        s4_awaddr  = m10_awaddr;
        s4_awlen   = m10_awlen;
        s4_awsize  = m10_awsize;
        s4_awburst = m10_awburst;
        s4_awlock  = m10_awlock;
        s4_awcache = m10_awcache;
        s4_awprot  = m10_awprot;
        s4_awqos   = m10_awqos;
        s4_awvalid = m10_awvalid & m10_slave_select[4];
        s4_wdata   = m10_wdata;
        s4_wstrb   = m10_wstrb;
        s4_wlast   = m10_wlast;
        s4_wvalid  = m10_wvalid;
        s4_bready  = m10_bready;
        s4_arid    = m10_arid;
        s4_araddr  = m10_araddr;
        s4_arlen   = m10_arlen;
        s4_arsize  = m10_arsize;
        s4_arburst = m10_arburst;
        s4_arlock  = m10_arlock;
        s4_arcache = m10_arcache;
        s4_arprot  = m10_arprot;
        s4_arqos   = m10_arqos;
        s4_arvalid = m10_arvalid & m10_slave_select[4];
        s4_rready  = m10_rready;
    end
 else if (m11_slave_select[4]) begin
        s4_awid    = m11_awid;
        s4_awaddr  = m11_awaddr;
        s4_awlen   = m11_awlen;
        s4_awsize  = m11_awsize;
        s4_awburst = m11_awburst;
        s4_awlock  = m11_awlock;
        s4_awcache = m11_awcache;
        s4_awprot  = m11_awprot;
        s4_awqos   = m11_awqos;
        s4_awvalid = m11_awvalid & m11_slave_select[4];
        s4_wdata   = m11_wdata;
        s4_wstrb   = m11_wstrb;
        s4_wlast   = m11_wlast;
        s4_wvalid  = m11_wvalid;
        s4_bready  = m11_bready;
        s4_arid    = m11_arid;
        s4_araddr  = m11_araddr;
        s4_arlen   = m11_arlen;
        s4_arsize  = m11_arsize;
        s4_arburst = m11_arburst;
        s4_arlock  = m11_arlock;
        s4_arcache = m11_arcache;
        s4_arprot  = m11_arprot;
        s4_arqos   = m11_arqos;
        s4_arvalid = m11_arvalid & m11_slave_select[4];
        s4_rready  = m11_rready;
    end
 else if (m12_slave_select[4]) begin
        s4_awid    = m12_awid;
        s4_awaddr  = m12_awaddr;
        s4_awlen   = m12_awlen;
        s4_awsize  = m12_awsize;
        s4_awburst = m12_awburst;
        s4_awlock  = m12_awlock;
        s4_awcache = m12_awcache;
        s4_awprot  = m12_awprot;
        s4_awqos   = m12_awqos;
        s4_awvalid = m12_awvalid & m12_slave_select[4];
        s4_wdata   = m12_wdata;
        s4_wstrb   = m12_wstrb;
        s4_wlast   = m12_wlast;
        s4_wvalid  = m12_wvalid;
        s4_bready  = m12_bready;
        s4_arid    = m12_arid;
        s4_araddr  = m12_araddr;
        s4_arlen   = m12_arlen;
        s4_arsize  = m12_arsize;
        s4_arburst = m12_arburst;
        s4_arlock  = m12_arlock;
        s4_arcache = m12_arcache;
        s4_arprot  = m12_arprot;
        s4_arqos   = m12_arqos;
        s4_arvalid = m12_arvalid & m12_slave_select[4];
        s4_rready  = m12_rready;
    end
 else if (m13_slave_select[4]) begin
        s4_awid    = m13_awid;
        s4_awaddr  = m13_awaddr;
        s4_awlen   = m13_awlen;
        s4_awsize  = m13_awsize;
        s4_awburst = m13_awburst;
        s4_awlock  = m13_awlock;
        s4_awcache = m13_awcache;
        s4_awprot  = m13_awprot;
        s4_awqos   = m13_awqos;
        s4_awvalid = m13_awvalid & m13_slave_select[4];
        s4_wdata   = m13_wdata;
        s4_wstrb   = m13_wstrb;
        s4_wlast   = m13_wlast;
        s4_wvalid  = m13_wvalid;
        s4_bready  = m13_bready;
        s4_arid    = m13_arid;
        s4_araddr  = m13_araddr;
        s4_arlen   = m13_arlen;
        s4_arsize  = m13_arsize;
        s4_arburst = m13_arburst;
        s4_arlock  = m13_arlock;
        s4_arcache = m13_arcache;
        s4_arprot  = m13_arprot;
        s4_arqos   = m13_arqos;
        s4_arvalid = m13_arvalid & m13_slave_select[4];
        s4_rready  = m13_rready;
    end
 else if (m14_slave_select[4]) begin
        s4_awid    = m14_awid;
        s4_awaddr  = m14_awaddr;
        s4_awlen   = m14_awlen;
        s4_awsize  = m14_awsize;
        s4_awburst = m14_awburst;
        s4_awlock  = m14_awlock;
        s4_awcache = m14_awcache;
        s4_awprot  = m14_awprot;
        s4_awqos   = m14_awqos;
        s4_awvalid = m14_awvalid & m14_slave_select[4];
        s4_wdata   = m14_wdata;
        s4_wstrb   = m14_wstrb;
        s4_wlast   = m14_wlast;
        s4_wvalid  = m14_wvalid;
        s4_bready  = m14_bready;
        s4_arid    = m14_arid;
        s4_araddr  = m14_araddr;
        s4_arlen   = m14_arlen;
        s4_arsize  = m14_arsize;
        s4_arburst = m14_arburst;
        s4_arlock  = m14_arlock;
        s4_arcache = m14_arcache;
        s4_arprot  = m14_arprot;
        s4_arqos   = m14_arqos;
        s4_arvalid = m14_arvalid & m14_slave_select[4];
        s4_rready  = m14_rready;
    end

end


// Slave 5 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s5_awid    = 'b0;
    s5_awaddr  = 'b0;
    s5_awlen   = 'b0;
    s5_awsize  = 'b0;
    s5_awburst = 'b0;
    s5_awlock  = 'b0;
    s5_awcache = 'b0;
    s5_awprot  = 'b0;
    s5_awqos   = 'b0;
    s5_awvalid = 'b0;
    s5_wdata   = 'b0;
    s5_wstrb   = 'b0;
    s5_wlast   = 'b0;
    s5_wvalid  = 'b0;
    s5_bready  = 'b0;
    s5_arid    = 'b0;
    s5_araddr  = 'b0;
    s5_arlen   = 'b0;
    s5_arsize  = 'b0;
    s5_arburst = 'b0;
    s5_arlock  = 'b0;
    s5_arcache = 'b0;
    s5_arprot  = 'b0;
    s5_arqos   = 'b0;
    s5_arvalid = 'b0;
    s5_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[5]) begin
        s5_awid    = m0_awid;
        s5_awaddr  = m0_awaddr;
        s5_awlen   = m0_awlen;
        s5_awsize  = m0_awsize;
        s5_awburst = m0_awburst;
        s5_awlock  = m0_awlock;
        s5_awcache = m0_awcache;
        s5_awprot  = m0_awprot;
        s5_awqos   = m0_awqos;
        s5_awvalid = m0_awvalid & m0_slave_select[5];
        s5_wdata   = m0_wdata;
        s5_wstrb   = m0_wstrb;
        s5_wlast   = m0_wlast;
        s5_wvalid  = m0_wvalid;
        s5_bready  = m0_bready;
        s5_arid    = m0_arid;
        s5_araddr  = m0_araddr;
        s5_arlen   = m0_arlen;
        s5_arsize  = m0_arsize;
        s5_arburst = m0_arburst;
        s5_arlock  = m0_arlock;
        s5_arcache = m0_arcache;
        s5_arprot  = m0_arprot;
        s5_arqos   = m0_arqos;
        s5_arvalid = m0_arvalid & m0_slave_select[5];
        s5_rready  = m0_rready;
    end
 else if (m1_slave_select[5]) begin
        s5_awid    = m1_awid;
        s5_awaddr  = m1_awaddr;
        s5_awlen   = m1_awlen;
        s5_awsize  = m1_awsize;
        s5_awburst = m1_awburst;
        s5_awlock  = m1_awlock;
        s5_awcache = m1_awcache;
        s5_awprot  = m1_awprot;
        s5_awqos   = m1_awqos;
        s5_awvalid = m1_awvalid & m1_slave_select[5];
        s5_wdata   = m1_wdata;
        s5_wstrb   = m1_wstrb;
        s5_wlast   = m1_wlast;
        s5_wvalid  = m1_wvalid;
        s5_bready  = m1_bready;
        s5_arid    = m1_arid;
        s5_araddr  = m1_araddr;
        s5_arlen   = m1_arlen;
        s5_arsize  = m1_arsize;
        s5_arburst = m1_arburst;
        s5_arlock  = m1_arlock;
        s5_arcache = m1_arcache;
        s5_arprot  = m1_arprot;
        s5_arqos   = m1_arqos;
        s5_arvalid = m1_arvalid & m1_slave_select[5];
        s5_rready  = m1_rready;
    end
 else if (m2_slave_select[5]) begin
        s5_awid    = m2_awid;
        s5_awaddr  = m2_awaddr;
        s5_awlen   = m2_awlen;
        s5_awsize  = m2_awsize;
        s5_awburst = m2_awburst;
        s5_awlock  = m2_awlock;
        s5_awcache = m2_awcache;
        s5_awprot  = m2_awprot;
        s5_awqos   = m2_awqos;
        s5_awvalid = m2_awvalid & m2_slave_select[5];
        s5_wdata   = m2_wdata;
        s5_wstrb   = m2_wstrb;
        s5_wlast   = m2_wlast;
        s5_wvalid  = m2_wvalid;
        s5_bready  = m2_bready;
        s5_arid    = m2_arid;
        s5_araddr  = m2_araddr;
        s5_arlen   = m2_arlen;
        s5_arsize  = m2_arsize;
        s5_arburst = m2_arburst;
        s5_arlock  = m2_arlock;
        s5_arcache = m2_arcache;
        s5_arprot  = m2_arprot;
        s5_arqos   = m2_arqos;
        s5_arvalid = m2_arvalid & m2_slave_select[5];
        s5_rready  = m2_rready;
    end
 else if (m3_slave_select[5]) begin
        s5_awid    = m3_awid;
        s5_awaddr  = m3_awaddr;
        s5_awlen   = m3_awlen;
        s5_awsize  = m3_awsize;
        s5_awburst = m3_awburst;
        s5_awlock  = m3_awlock;
        s5_awcache = m3_awcache;
        s5_awprot  = m3_awprot;
        s5_awqos   = m3_awqos;
        s5_awvalid = m3_awvalid & m3_slave_select[5];
        s5_wdata   = m3_wdata;
        s5_wstrb   = m3_wstrb;
        s5_wlast   = m3_wlast;
        s5_wvalid  = m3_wvalid;
        s5_bready  = m3_bready;
        s5_arid    = m3_arid;
        s5_araddr  = m3_araddr;
        s5_arlen   = m3_arlen;
        s5_arsize  = m3_arsize;
        s5_arburst = m3_arburst;
        s5_arlock  = m3_arlock;
        s5_arcache = m3_arcache;
        s5_arprot  = m3_arprot;
        s5_arqos   = m3_arqos;
        s5_arvalid = m3_arvalid & m3_slave_select[5];
        s5_rready  = m3_rready;
    end
 else if (m4_slave_select[5]) begin
        s5_awid    = m4_awid;
        s5_awaddr  = m4_awaddr;
        s5_awlen   = m4_awlen;
        s5_awsize  = m4_awsize;
        s5_awburst = m4_awburst;
        s5_awlock  = m4_awlock;
        s5_awcache = m4_awcache;
        s5_awprot  = m4_awprot;
        s5_awqos   = m4_awqos;
        s5_awvalid = m4_awvalid & m4_slave_select[5];
        s5_wdata   = m4_wdata;
        s5_wstrb   = m4_wstrb;
        s5_wlast   = m4_wlast;
        s5_wvalid  = m4_wvalid;
        s5_bready  = m4_bready;
        s5_arid    = m4_arid;
        s5_araddr  = m4_araddr;
        s5_arlen   = m4_arlen;
        s5_arsize  = m4_arsize;
        s5_arburst = m4_arburst;
        s5_arlock  = m4_arlock;
        s5_arcache = m4_arcache;
        s5_arprot  = m4_arprot;
        s5_arqos   = m4_arqos;
        s5_arvalid = m4_arvalid & m4_slave_select[5];
        s5_rready  = m4_rready;
    end
 else if (m5_slave_select[5]) begin
        s5_awid    = m5_awid;
        s5_awaddr  = m5_awaddr;
        s5_awlen   = m5_awlen;
        s5_awsize  = m5_awsize;
        s5_awburst = m5_awburst;
        s5_awlock  = m5_awlock;
        s5_awcache = m5_awcache;
        s5_awprot  = m5_awprot;
        s5_awqos   = m5_awqos;
        s5_awvalid = m5_awvalid & m5_slave_select[5];
        s5_wdata   = m5_wdata;
        s5_wstrb   = m5_wstrb;
        s5_wlast   = m5_wlast;
        s5_wvalid  = m5_wvalid;
        s5_bready  = m5_bready;
        s5_arid    = m5_arid;
        s5_araddr  = m5_araddr;
        s5_arlen   = m5_arlen;
        s5_arsize  = m5_arsize;
        s5_arburst = m5_arburst;
        s5_arlock  = m5_arlock;
        s5_arcache = m5_arcache;
        s5_arprot  = m5_arprot;
        s5_arqos   = m5_arqos;
        s5_arvalid = m5_arvalid & m5_slave_select[5];
        s5_rready  = m5_rready;
    end
 else if (m6_slave_select[5]) begin
        s5_awid    = m6_awid;
        s5_awaddr  = m6_awaddr;
        s5_awlen   = m6_awlen;
        s5_awsize  = m6_awsize;
        s5_awburst = m6_awburst;
        s5_awlock  = m6_awlock;
        s5_awcache = m6_awcache;
        s5_awprot  = m6_awprot;
        s5_awqos   = m6_awqos;
        s5_awvalid = m6_awvalid & m6_slave_select[5];
        s5_wdata   = m6_wdata;
        s5_wstrb   = m6_wstrb;
        s5_wlast   = m6_wlast;
        s5_wvalid  = m6_wvalid;
        s5_bready  = m6_bready;
        s5_arid    = m6_arid;
        s5_araddr  = m6_araddr;
        s5_arlen   = m6_arlen;
        s5_arsize  = m6_arsize;
        s5_arburst = m6_arburst;
        s5_arlock  = m6_arlock;
        s5_arcache = m6_arcache;
        s5_arprot  = m6_arprot;
        s5_arqos   = m6_arqos;
        s5_arvalid = m6_arvalid & m6_slave_select[5];
        s5_rready  = m6_rready;
    end
 else if (m7_slave_select[5]) begin
        s5_awid    = m7_awid;
        s5_awaddr  = m7_awaddr;
        s5_awlen   = m7_awlen;
        s5_awsize  = m7_awsize;
        s5_awburst = m7_awburst;
        s5_awlock  = m7_awlock;
        s5_awcache = m7_awcache;
        s5_awprot  = m7_awprot;
        s5_awqos   = m7_awqos;
        s5_awvalid = m7_awvalid & m7_slave_select[5];
        s5_wdata   = m7_wdata;
        s5_wstrb   = m7_wstrb;
        s5_wlast   = m7_wlast;
        s5_wvalid  = m7_wvalid;
        s5_bready  = m7_bready;
        s5_arid    = m7_arid;
        s5_araddr  = m7_araddr;
        s5_arlen   = m7_arlen;
        s5_arsize  = m7_arsize;
        s5_arburst = m7_arburst;
        s5_arlock  = m7_arlock;
        s5_arcache = m7_arcache;
        s5_arprot  = m7_arprot;
        s5_arqos   = m7_arqos;
        s5_arvalid = m7_arvalid & m7_slave_select[5];
        s5_rready  = m7_rready;
    end
 else if (m8_slave_select[5]) begin
        s5_awid    = m8_awid;
        s5_awaddr  = m8_awaddr;
        s5_awlen   = m8_awlen;
        s5_awsize  = m8_awsize;
        s5_awburst = m8_awburst;
        s5_awlock  = m8_awlock;
        s5_awcache = m8_awcache;
        s5_awprot  = m8_awprot;
        s5_awqos   = m8_awqos;
        s5_awvalid = m8_awvalid & m8_slave_select[5];
        s5_wdata   = m8_wdata;
        s5_wstrb   = m8_wstrb;
        s5_wlast   = m8_wlast;
        s5_wvalid  = m8_wvalid;
        s5_bready  = m8_bready;
        s5_arid    = m8_arid;
        s5_araddr  = m8_araddr;
        s5_arlen   = m8_arlen;
        s5_arsize  = m8_arsize;
        s5_arburst = m8_arburst;
        s5_arlock  = m8_arlock;
        s5_arcache = m8_arcache;
        s5_arprot  = m8_arprot;
        s5_arqos   = m8_arqos;
        s5_arvalid = m8_arvalid & m8_slave_select[5];
        s5_rready  = m8_rready;
    end
 else if (m9_slave_select[5]) begin
        s5_awid    = m9_awid;
        s5_awaddr  = m9_awaddr;
        s5_awlen   = m9_awlen;
        s5_awsize  = m9_awsize;
        s5_awburst = m9_awburst;
        s5_awlock  = m9_awlock;
        s5_awcache = m9_awcache;
        s5_awprot  = m9_awprot;
        s5_awqos   = m9_awqos;
        s5_awvalid = m9_awvalid & m9_slave_select[5];
        s5_wdata   = m9_wdata;
        s5_wstrb   = m9_wstrb;
        s5_wlast   = m9_wlast;
        s5_wvalid  = m9_wvalid;
        s5_bready  = m9_bready;
        s5_arid    = m9_arid;
        s5_araddr  = m9_araddr;
        s5_arlen   = m9_arlen;
        s5_arsize  = m9_arsize;
        s5_arburst = m9_arburst;
        s5_arlock  = m9_arlock;
        s5_arcache = m9_arcache;
        s5_arprot  = m9_arprot;
        s5_arqos   = m9_arqos;
        s5_arvalid = m9_arvalid & m9_slave_select[5];
        s5_rready  = m9_rready;
    end
 else if (m10_slave_select[5]) begin
        s5_awid    = m10_awid;
        s5_awaddr  = m10_awaddr;
        s5_awlen   = m10_awlen;
        s5_awsize  = m10_awsize;
        s5_awburst = m10_awburst;
        s5_awlock  = m10_awlock;
        s5_awcache = m10_awcache;
        s5_awprot  = m10_awprot;
        s5_awqos   = m10_awqos;
        s5_awvalid = m10_awvalid & m10_slave_select[5];
        s5_wdata   = m10_wdata;
        s5_wstrb   = m10_wstrb;
        s5_wlast   = m10_wlast;
        s5_wvalid  = m10_wvalid;
        s5_bready  = m10_bready;
        s5_arid    = m10_arid;
        s5_araddr  = m10_araddr;
        s5_arlen   = m10_arlen;
        s5_arsize  = m10_arsize;
        s5_arburst = m10_arburst;
        s5_arlock  = m10_arlock;
        s5_arcache = m10_arcache;
        s5_arprot  = m10_arprot;
        s5_arqos   = m10_arqos;
        s5_arvalid = m10_arvalid & m10_slave_select[5];
        s5_rready  = m10_rready;
    end
 else if (m11_slave_select[5]) begin
        s5_awid    = m11_awid;
        s5_awaddr  = m11_awaddr;
        s5_awlen   = m11_awlen;
        s5_awsize  = m11_awsize;
        s5_awburst = m11_awburst;
        s5_awlock  = m11_awlock;
        s5_awcache = m11_awcache;
        s5_awprot  = m11_awprot;
        s5_awqos   = m11_awqos;
        s5_awvalid = m11_awvalid & m11_slave_select[5];
        s5_wdata   = m11_wdata;
        s5_wstrb   = m11_wstrb;
        s5_wlast   = m11_wlast;
        s5_wvalid  = m11_wvalid;
        s5_bready  = m11_bready;
        s5_arid    = m11_arid;
        s5_araddr  = m11_araddr;
        s5_arlen   = m11_arlen;
        s5_arsize  = m11_arsize;
        s5_arburst = m11_arburst;
        s5_arlock  = m11_arlock;
        s5_arcache = m11_arcache;
        s5_arprot  = m11_arprot;
        s5_arqos   = m11_arqos;
        s5_arvalid = m11_arvalid & m11_slave_select[5];
        s5_rready  = m11_rready;
    end
 else if (m12_slave_select[5]) begin
        s5_awid    = m12_awid;
        s5_awaddr  = m12_awaddr;
        s5_awlen   = m12_awlen;
        s5_awsize  = m12_awsize;
        s5_awburst = m12_awburst;
        s5_awlock  = m12_awlock;
        s5_awcache = m12_awcache;
        s5_awprot  = m12_awprot;
        s5_awqos   = m12_awqos;
        s5_awvalid = m12_awvalid & m12_slave_select[5];
        s5_wdata   = m12_wdata;
        s5_wstrb   = m12_wstrb;
        s5_wlast   = m12_wlast;
        s5_wvalid  = m12_wvalid;
        s5_bready  = m12_bready;
        s5_arid    = m12_arid;
        s5_araddr  = m12_araddr;
        s5_arlen   = m12_arlen;
        s5_arsize  = m12_arsize;
        s5_arburst = m12_arburst;
        s5_arlock  = m12_arlock;
        s5_arcache = m12_arcache;
        s5_arprot  = m12_arprot;
        s5_arqos   = m12_arqos;
        s5_arvalid = m12_arvalid & m12_slave_select[5];
        s5_rready  = m12_rready;
    end
 else if (m13_slave_select[5]) begin
        s5_awid    = m13_awid;
        s5_awaddr  = m13_awaddr;
        s5_awlen   = m13_awlen;
        s5_awsize  = m13_awsize;
        s5_awburst = m13_awburst;
        s5_awlock  = m13_awlock;
        s5_awcache = m13_awcache;
        s5_awprot  = m13_awprot;
        s5_awqos   = m13_awqos;
        s5_awvalid = m13_awvalid & m13_slave_select[5];
        s5_wdata   = m13_wdata;
        s5_wstrb   = m13_wstrb;
        s5_wlast   = m13_wlast;
        s5_wvalid  = m13_wvalid;
        s5_bready  = m13_bready;
        s5_arid    = m13_arid;
        s5_araddr  = m13_araddr;
        s5_arlen   = m13_arlen;
        s5_arsize  = m13_arsize;
        s5_arburst = m13_arburst;
        s5_arlock  = m13_arlock;
        s5_arcache = m13_arcache;
        s5_arprot  = m13_arprot;
        s5_arqos   = m13_arqos;
        s5_arvalid = m13_arvalid & m13_slave_select[5];
        s5_rready  = m13_rready;
    end
 else if (m14_slave_select[5]) begin
        s5_awid    = m14_awid;
        s5_awaddr  = m14_awaddr;
        s5_awlen   = m14_awlen;
        s5_awsize  = m14_awsize;
        s5_awburst = m14_awburst;
        s5_awlock  = m14_awlock;
        s5_awcache = m14_awcache;
        s5_awprot  = m14_awprot;
        s5_awqos   = m14_awqos;
        s5_awvalid = m14_awvalid & m14_slave_select[5];
        s5_wdata   = m14_wdata;
        s5_wstrb   = m14_wstrb;
        s5_wlast   = m14_wlast;
        s5_wvalid  = m14_wvalid;
        s5_bready  = m14_bready;
        s5_arid    = m14_arid;
        s5_araddr  = m14_araddr;
        s5_arlen   = m14_arlen;
        s5_arsize  = m14_arsize;
        s5_arburst = m14_arburst;
        s5_arlock  = m14_arlock;
        s5_arcache = m14_arcache;
        s5_arprot  = m14_arprot;
        s5_arqos   = m14_arqos;
        s5_arvalid = m14_arvalid & m14_slave_select[5];
        s5_rready  = m14_rready;
    end

end


// Slave 6 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s6_awid    = 'b0;
    s6_awaddr  = 'b0;
    s6_awlen   = 'b0;
    s6_awsize  = 'b0;
    s6_awburst = 'b0;
    s6_awlock  = 'b0;
    s6_awcache = 'b0;
    s6_awprot  = 'b0;
    s6_awqos   = 'b0;
    s6_awvalid = 'b0;
    s6_wdata   = 'b0;
    s6_wstrb   = 'b0;
    s6_wlast   = 'b0;
    s6_wvalid  = 'b0;
    s6_bready  = 'b0;
    s6_arid    = 'b0;
    s6_araddr  = 'b0;
    s6_arlen   = 'b0;
    s6_arsize  = 'b0;
    s6_arburst = 'b0;
    s6_arlock  = 'b0;
    s6_arcache = 'b0;
    s6_arprot  = 'b0;
    s6_arqos   = 'b0;
    s6_arvalid = 'b0;
    s6_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[6]) begin
        s6_awid    = m0_awid;
        s6_awaddr  = m0_awaddr;
        s6_awlen   = m0_awlen;
        s6_awsize  = m0_awsize;
        s6_awburst = m0_awburst;
        s6_awlock  = m0_awlock;
        s6_awcache = m0_awcache;
        s6_awprot  = m0_awprot;
        s6_awqos   = m0_awqos;
        s6_awvalid = m0_awvalid & m0_slave_select[6];
        s6_wdata   = m0_wdata;
        s6_wstrb   = m0_wstrb;
        s6_wlast   = m0_wlast;
        s6_wvalid  = m0_wvalid;
        s6_bready  = m0_bready;
        s6_arid    = m0_arid;
        s6_araddr  = m0_araddr;
        s6_arlen   = m0_arlen;
        s6_arsize  = m0_arsize;
        s6_arburst = m0_arburst;
        s6_arlock  = m0_arlock;
        s6_arcache = m0_arcache;
        s6_arprot  = m0_arprot;
        s6_arqos   = m0_arqos;
        s6_arvalid = m0_arvalid & m0_slave_select[6];
        s6_rready  = m0_rready;
    end
 else if (m1_slave_select[6]) begin
        s6_awid    = m1_awid;
        s6_awaddr  = m1_awaddr;
        s6_awlen   = m1_awlen;
        s6_awsize  = m1_awsize;
        s6_awburst = m1_awburst;
        s6_awlock  = m1_awlock;
        s6_awcache = m1_awcache;
        s6_awprot  = m1_awprot;
        s6_awqos   = m1_awqos;
        s6_awvalid = m1_awvalid & m1_slave_select[6];
        s6_wdata   = m1_wdata;
        s6_wstrb   = m1_wstrb;
        s6_wlast   = m1_wlast;
        s6_wvalid  = m1_wvalid;
        s6_bready  = m1_bready;
        s6_arid    = m1_arid;
        s6_araddr  = m1_araddr;
        s6_arlen   = m1_arlen;
        s6_arsize  = m1_arsize;
        s6_arburst = m1_arburst;
        s6_arlock  = m1_arlock;
        s6_arcache = m1_arcache;
        s6_arprot  = m1_arprot;
        s6_arqos   = m1_arqos;
        s6_arvalid = m1_arvalid & m1_slave_select[6];
        s6_rready  = m1_rready;
    end
 else if (m2_slave_select[6]) begin
        s6_awid    = m2_awid;
        s6_awaddr  = m2_awaddr;
        s6_awlen   = m2_awlen;
        s6_awsize  = m2_awsize;
        s6_awburst = m2_awburst;
        s6_awlock  = m2_awlock;
        s6_awcache = m2_awcache;
        s6_awprot  = m2_awprot;
        s6_awqos   = m2_awqos;
        s6_awvalid = m2_awvalid & m2_slave_select[6];
        s6_wdata   = m2_wdata;
        s6_wstrb   = m2_wstrb;
        s6_wlast   = m2_wlast;
        s6_wvalid  = m2_wvalid;
        s6_bready  = m2_bready;
        s6_arid    = m2_arid;
        s6_araddr  = m2_araddr;
        s6_arlen   = m2_arlen;
        s6_arsize  = m2_arsize;
        s6_arburst = m2_arburst;
        s6_arlock  = m2_arlock;
        s6_arcache = m2_arcache;
        s6_arprot  = m2_arprot;
        s6_arqos   = m2_arqos;
        s6_arvalid = m2_arvalid & m2_slave_select[6];
        s6_rready  = m2_rready;
    end
 else if (m3_slave_select[6]) begin
        s6_awid    = m3_awid;
        s6_awaddr  = m3_awaddr;
        s6_awlen   = m3_awlen;
        s6_awsize  = m3_awsize;
        s6_awburst = m3_awburst;
        s6_awlock  = m3_awlock;
        s6_awcache = m3_awcache;
        s6_awprot  = m3_awprot;
        s6_awqos   = m3_awqos;
        s6_awvalid = m3_awvalid & m3_slave_select[6];
        s6_wdata   = m3_wdata;
        s6_wstrb   = m3_wstrb;
        s6_wlast   = m3_wlast;
        s6_wvalid  = m3_wvalid;
        s6_bready  = m3_bready;
        s6_arid    = m3_arid;
        s6_araddr  = m3_araddr;
        s6_arlen   = m3_arlen;
        s6_arsize  = m3_arsize;
        s6_arburst = m3_arburst;
        s6_arlock  = m3_arlock;
        s6_arcache = m3_arcache;
        s6_arprot  = m3_arprot;
        s6_arqos   = m3_arqos;
        s6_arvalid = m3_arvalid & m3_slave_select[6];
        s6_rready  = m3_rready;
    end
 else if (m4_slave_select[6]) begin
        s6_awid    = m4_awid;
        s6_awaddr  = m4_awaddr;
        s6_awlen   = m4_awlen;
        s6_awsize  = m4_awsize;
        s6_awburst = m4_awburst;
        s6_awlock  = m4_awlock;
        s6_awcache = m4_awcache;
        s6_awprot  = m4_awprot;
        s6_awqos   = m4_awqos;
        s6_awvalid = m4_awvalid & m4_slave_select[6];
        s6_wdata   = m4_wdata;
        s6_wstrb   = m4_wstrb;
        s6_wlast   = m4_wlast;
        s6_wvalid  = m4_wvalid;
        s6_bready  = m4_bready;
        s6_arid    = m4_arid;
        s6_araddr  = m4_araddr;
        s6_arlen   = m4_arlen;
        s6_arsize  = m4_arsize;
        s6_arburst = m4_arburst;
        s6_arlock  = m4_arlock;
        s6_arcache = m4_arcache;
        s6_arprot  = m4_arprot;
        s6_arqos   = m4_arqos;
        s6_arvalid = m4_arvalid & m4_slave_select[6];
        s6_rready  = m4_rready;
    end
 else if (m5_slave_select[6]) begin
        s6_awid    = m5_awid;
        s6_awaddr  = m5_awaddr;
        s6_awlen   = m5_awlen;
        s6_awsize  = m5_awsize;
        s6_awburst = m5_awburst;
        s6_awlock  = m5_awlock;
        s6_awcache = m5_awcache;
        s6_awprot  = m5_awprot;
        s6_awqos   = m5_awqos;
        s6_awvalid = m5_awvalid & m5_slave_select[6];
        s6_wdata   = m5_wdata;
        s6_wstrb   = m5_wstrb;
        s6_wlast   = m5_wlast;
        s6_wvalid  = m5_wvalid;
        s6_bready  = m5_bready;
        s6_arid    = m5_arid;
        s6_araddr  = m5_araddr;
        s6_arlen   = m5_arlen;
        s6_arsize  = m5_arsize;
        s6_arburst = m5_arburst;
        s6_arlock  = m5_arlock;
        s6_arcache = m5_arcache;
        s6_arprot  = m5_arprot;
        s6_arqos   = m5_arqos;
        s6_arvalid = m5_arvalid & m5_slave_select[6];
        s6_rready  = m5_rready;
    end
 else if (m6_slave_select[6]) begin
        s6_awid    = m6_awid;
        s6_awaddr  = m6_awaddr;
        s6_awlen   = m6_awlen;
        s6_awsize  = m6_awsize;
        s6_awburst = m6_awburst;
        s6_awlock  = m6_awlock;
        s6_awcache = m6_awcache;
        s6_awprot  = m6_awprot;
        s6_awqos   = m6_awqos;
        s6_awvalid = m6_awvalid & m6_slave_select[6];
        s6_wdata   = m6_wdata;
        s6_wstrb   = m6_wstrb;
        s6_wlast   = m6_wlast;
        s6_wvalid  = m6_wvalid;
        s6_bready  = m6_bready;
        s6_arid    = m6_arid;
        s6_araddr  = m6_araddr;
        s6_arlen   = m6_arlen;
        s6_arsize  = m6_arsize;
        s6_arburst = m6_arburst;
        s6_arlock  = m6_arlock;
        s6_arcache = m6_arcache;
        s6_arprot  = m6_arprot;
        s6_arqos   = m6_arqos;
        s6_arvalid = m6_arvalid & m6_slave_select[6];
        s6_rready  = m6_rready;
    end
 else if (m7_slave_select[6]) begin
        s6_awid    = m7_awid;
        s6_awaddr  = m7_awaddr;
        s6_awlen   = m7_awlen;
        s6_awsize  = m7_awsize;
        s6_awburst = m7_awburst;
        s6_awlock  = m7_awlock;
        s6_awcache = m7_awcache;
        s6_awprot  = m7_awprot;
        s6_awqos   = m7_awqos;
        s6_awvalid = m7_awvalid & m7_slave_select[6];
        s6_wdata   = m7_wdata;
        s6_wstrb   = m7_wstrb;
        s6_wlast   = m7_wlast;
        s6_wvalid  = m7_wvalid;
        s6_bready  = m7_bready;
        s6_arid    = m7_arid;
        s6_araddr  = m7_araddr;
        s6_arlen   = m7_arlen;
        s6_arsize  = m7_arsize;
        s6_arburst = m7_arburst;
        s6_arlock  = m7_arlock;
        s6_arcache = m7_arcache;
        s6_arprot  = m7_arprot;
        s6_arqos   = m7_arqos;
        s6_arvalid = m7_arvalid & m7_slave_select[6];
        s6_rready  = m7_rready;
    end
 else if (m8_slave_select[6]) begin
        s6_awid    = m8_awid;
        s6_awaddr  = m8_awaddr;
        s6_awlen   = m8_awlen;
        s6_awsize  = m8_awsize;
        s6_awburst = m8_awburst;
        s6_awlock  = m8_awlock;
        s6_awcache = m8_awcache;
        s6_awprot  = m8_awprot;
        s6_awqos   = m8_awqos;
        s6_awvalid = m8_awvalid & m8_slave_select[6];
        s6_wdata   = m8_wdata;
        s6_wstrb   = m8_wstrb;
        s6_wlast   = m8_wlast;
        s6_wvalid  = m8_wvalid;
        s6_bready  = m8_bready;
        s6_arid    = m8_arid;
        s6_araddr  = m8_araddr;
        s6_arlen   = m8_arlen;
        s6_arsize  = m8_arsize;
        s6_arburst = m8_arburst;
        s6_arlock  = m8_arlock;
        s6_arcache = m8_arcache;
        s6_arprot  = m8_arprot;
        s6_arqos   = m8_arqos;
        s6_arvalid = m8_arvalid & m8_slave_select[6];
        s6_rready  = m8_rready;
    end
 else if (m9_slave_select[6]) begin
        s6_awid    = m9_awid;
        s6_awaddr  = m9_awaddr;
        s6_awlen   = m9_awlen;
        s6_awsize  = m9_awsize;
        s6_awburst = m9_awburst;
        s6_awlock  = m9_awlock;
        s6_awcache = m9_awcache;
        s6_awprot  = m9_awprot;
        s6_awqos   = m9_awqos;
        s6_awvalid = m9_awvalid & m9_slave_select[6];
        s6_wdata   = m9_wdata;
        s6_wstrb   = m9_wstrb;
        s6_wlast   = m9_wlast;
        s6_wvalid  = m9_wvalid;
        s6_bready  = m9_bready;
        s6_arid    = m9_arid;
        s6_araddr  = m9_araddr;
        s6_arlen   = m9_arlen;
        s6_arsize  = m9_arsize;
        s6_arburst = m9_arburst;
        s6_arlock  = m9_arlock;
        s6_arcache = m9_arcache;
        s6_arprot  = m9_arprot;
        s6_arqos   = m9_arqos;
        s6_arvalid = m9_arvalid & m9_slave_select[6];
        s6_rready  = m9_rready;
    end
 else if (m10_slave_select[6]) begin
        s6_awid    = m10_awid;
        s6_awaddr  = m10_awaddr;
        s6_awlen   = m10_awlen;
        s6_awsize  = m10_awsize;
        s6_awburst = m10_awburst;
        s6_awlock  = m10_awlock;
        s6_awcache = m10_awcache;
        s6_awprot  = m10_awprot;
        s6_awqos   = m10_awqos;
        s6_awvalid = m10_awvalid & m10_slave_select[6];
        s6_wdata   = m10_wdata;
        s6_wstrb   = m10_wstrb;
        s6_wlast   = m10_wlast;
        s6_wvalid  = m10_wvalid;
        s6_bready  = m10_bready;
        s6_arid    = m10_arid;
        s6_araddr  = m10_araddr;
        s6_arlen   = m10_arlen;
        s6_arsize  = m10_arsize;
        s6_arburst = m10_arburst;
        s6_arlock  = m10_arlock;
        s6_arcache = m10_arcache;
        s6_arprot  = m10_arprot;
        s6_arqos   = m10_arqos;
        s6_arvalid = m10_arvalid & m10_slave_select[6];
        s6_rready  = m10_rready;
    end
 else if (m11_slave_select[6]) begin
        s6_awid    = m11_awid;
        s6_awaddr  = m11_awaddr;
        s6_awlen   = m11_awlen;
        s6_awsize  = m11_awsize;
        s6_awburst = m11_awburst;
        s6_awlock  = m11_awlock;
        s6_awcache = m11_awcache;
        s6_awprot  = m11_awprot;
        s6_awqos   = m11_awqos;
        s6_awvalid = m11_awvalid & m11_slave_select[6];
        s6_wdata   = m11_wdata;
        s6_wstrb   = m11_wstrb;
        s6_wlast   = m11_wlast;
        s6_wvalid  = m11_wvalid;
        s6_bready  = m11_bready;
        s6_arid    = m11_arid;
        s6_araddr  = m11_araddr;
        s6_arlen   = m11_arlen;
        s6_arsize  = m11_arsize;
        s6_arburst = m11_arburst;
        s6_arlock  = m11_arlock;
        s6_arcache = m11_arcache;
        s6_arprot  = m11_arprot;
        s6_arqos   = m11_arqos;
        s6_arvalid = m11_arvalid & m11_slave_select[6];
        s6_rready  = m11_rready;
    end
 else if (m12_slave_select[6]) begin
        s6_awid    = m12_awid;
        s6_awaddr  = m12_awaddr;
        s6_awlen   = m12_awlen;
        s6_awsize  = m12_awsize;
        s6_awburst = m12_awburst;
        s6_awlock  = m12_awlock;
        s6_awcache = m12_awcache;
        s6_awprot  = m12_awprot;
        s6_awqos   = m12_awqos;
        s6_awvalid = m12_awvalid & m12_slave_select[6];
        s6_wdata   = m12_wdata;
        s6_wstrb   = m12_wstrb;
        s6_wlast   = m12_wlast;
        s6_wvalid  = m12_wvalid;
        s6_bready  = m12_bready;
        s6_arid    = m12_arid;
        s6_araddr  = m12_araddr;
        s6_arlen   = m12_arlen;
        s6_arsize  = m12_arsize;
        s6_arburst = m12_arburst;
        s6_arlock  = m12_arlock;
        s6_arcache = m12_arcache;
        s6_arprot  = m12_arprot;
        s6_arqos   = m12_arqos;
        s6_arvalid = m12_arvalid & m12_slave_select[6];
        s6_rready  = m12_rready;
    end
 else if (m13_slave_select[6]) begin
        s6_awid    = m13_awid;
        s6_awaddr  = m13_awaddr;
        s6_awlen   = m13_awlen;
        s6_awsize  = m13_awsize;
        s6_awburst = m13_awburst;
        s6_awlock  = m13_awlock;
        s6_awcache = m13_awcache;
        s6_awprot  = m13_awprot;
        s6_awqos   = m13_awqos;
        s6_awvalid = m13_awvalid & m13_slave_select[6];
        s6_wdata   = m13_wdata;
        s6_wstrb   = m13_wstrb;
        s6_wlast   = m13_wlast;
        s6_wvalid  = m13_wvalid;
        s6_bready  = m13_bready;
        s6_arid    = m13_arid;
        s6_araddr  = m13_araddr;
        s6_arlen   = m13_arlen;
        s6_arsize  = m13_arsize;
        s6_arburst = m13_arburst;
        s6_arlock  = m13_arlock;
        s6_arcache = m13_arcache;
        s6_arprot  = m13_arprot;
        s6_arqos   = m13_arqos;
        s6_arvalid = m13_arvalid & m13_slave_select[6];
        s6_rready  = m13_rready;
    end
 else if (m14_slave_select[6]) begin
        s6_awid    = m14_awid;
        s6_awaddr  = m14_awaddr;
        s6_awlen   = m14_awlen;
        s6_awsize  = m14_awsize;
        s6_awburst = m14_awburst;
        s6_awlock  = m14_awlock;
        s6_awcache = m14_awcache;
        s6_awprot  = m14_awprot;
        s6_awqos   = m14_awqos;
        s6_awvalid = m14_awvalid & m14_slave_select[6];
        s6_wdata   = m14_wdata;
        s6_wstrb   = m14_wstrb;
        s6_wlast   = m14_wlast;
        s6_wvalid  = m14_wvalid;
        s6_bready  = m14_bready;
        s6_arid    = m14_arid;
        s6_araddr  = m14_araddr;
        s6_arlen   = m14_arlen;
        s6_arsize  = m14_arsize;
        s6_arburst = m14_arburst;
        s6_arlock  = m14_arlock;
        s6_arcache = m14_arcache;
        s6_arprot  = m14_arprot;
        s6_arqos   = m14_arqos;
        s6_arvalid = m14_arvalid & m14_slave_select[6];
        s6_rready  = m14_rready;
    end

end


// Slave 7 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s7_awid    = 'b0;
    s7_awaddr  = 'b0;
    s7_awlen   = 'b0;
    s7_awsize  = 'b0;
    s7_awburst = 'b0;
    s7_awlock  = 'b0;
    s7_awcache = 'b0;
    s7_awprot  = 'b0;
    s7_awqos   = 'b0;
    s7_awvalid = 'b0;
    s7_wdata   = 'b0;
    s7_wstrb   = 'b0;
    s7_wlast   = 'b0;
    s7_wvalid  = 'b0;
    s7_bready  = 'b0;
    s7_arid    = 'b0;
    s7_araddr  = 'b0;
    s7_arlen   = 'b0;
    s7_arsize  = 'b0;
    s7_arburst = 'b0;
    s7_arlock  = 'b0;
    s7_arcache = 'b0;
    s7_arprot  = 'b0;
    s7_arqos   = 'b0;
    s7_arvalid = 'b0;
    s7_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[7]) begin
        s7_awid    = m0_awid;
        s7_awaddr  = m0_awaddr;
        s7_awlen   = m0_awlen;
        s7_awsize  = m0_awsize;
        s7_awburst = m0_awburst;
        s7_awlock  = m0_awlock;
        s7_awcache = m0_awcache;
        s7_awprot  = m0_awprot;
        s7_awqos   = m0_awqos;
        s7_awvalid = m0_awvalid & m0_slave_select[7];
        s7_wdata   = m0_wdata;
        s7_wstrb   = m0_wstrb;
        s7_wlast   = m0_wlast;
        s7_wvalid  = m0_wvalid;
        s7_bready  = m0_bready;
        s7_arid    = m0_arid;
        s7_araddr  = m0_araddr;
        s7_arlen   = m0_arlen;
        s7_arsize  = m0_arsize;
        s7_arburst = m0_arburst;
        s7_arlock  = m0_arlock;
        s7_arcache = m0_arcache;
        s7_arprot  = m0_arprot;
        s7_arqos   = m0_arqos;
        s7_arvalid = m0_arvalid & m0_slave_select[7];
        s7_rready  = m0_rready;
    end
 else if (m1_slave_select[7]) begin
        s7_awid    = m1_awid;
        s7_awaddr  = m1_awaddr;
        s7_awlen   = m1_awlen;
        s7_awsize  = m1_awsize;
        s7_awburst = m1_awburst;
        s7_awlock  = m1_awlock;
        s7_awcache = m1_awcache;
        s7_awprot  = m1_awprot;
        s7_awqos   = m1_awqos;
        s7_awvalid = m1_awvalid & m1_slave_select[7];
        s7_wdata   = m1_wdata;
        s7_wstrb   = m1_wstrb;
        s7_wlast   = m1_wlast;
        s7_wvalid  = m1_wvalid;
        s7_bready  = m1_bready;
        s7_arid    = m1_arid;
        s7_araddr  = m1_araddr;
        s7_arlen   = m1_arlen;
        s7_arsize  = m1_arsize;
        s7_arburst = m1_arburst;
        s7_arlock  = m1_arlock;
        s7_arcache = m1_arcache;
        s7_arprot  = m1_arprot;
        s7_arqos   = m1_arqos;
        s7_arvalid = m1_arvalid & m1_slave_select[7];
        s7_rready  = m1_rready;
    end
 else if (m2_slave_select[7]) begin
        s7_awid    = m2_awid;
        s7_awaddr  = m2_awaddr;
        s7_awlen   = m2_awlen;
        s7_awsize  = m2_awsize;
        s7_awburst = m2_awburst;
        s7_awlock  = m2_awlock;
        s7_awcache = m2_awcache;
        s7_awprot  = m2_awprot;
        s7_awqos   = m2_awqos;
        s7_awvalid = m2_awvalid & m2_slave_select[7];
        s7_wdata   = m2_wdata;
        s7_wstrb   = m2_wstrb;
        s7_wlast   = m2_wlast;
        s7_wvalid  = m2_wvalid;
        s7_bready  = m2_bready;
        s7_arid    = m2_arid;
        s7_araddr  = m2_araddr;
        s7_arlen   = m2_arlen;
        s7_arsize  = m2_arsize;
        s7_arburst = m2_arburst;
        s7_arlock  = m2_arlock;
        s7_arcache = m2_arcache;
        s7_arprot  = m2_arprot;
        s7_arqos   = m2_arqos;
        s7_arvalid = m2_arvalid & m2_slave_select[7];
        s7_rready  = m2_rready;
    end
 else if (m3_slave_select[7]) begin
        s7_awid    = m3_awid;
        s7_awaddr  = m3_awaddr;
        s7_awlen   = m3_awlen;
        s7_awsize  = m3_awsize;
        s7_awburst = m3_awburst;
        s7_awlock  = m3_awlock;
        s7_awcache = m3_awcache;
        s7_awprot  = m3_awprot;
        s7_awqos   = m3_awqos;
        s7_awvalid = m3_awvalid & m3_slave_select[7];
        s7_wdata   = m3_wdata;
        s7_wstrb   = m3_wstrb;
        s7_wlast   = m3_wlast;
        s7_wvalid  = m3_wvalid;
        s7_bready  = m3_bready;
        s7_arid    = m3_arid;
        s7_araddr  = m3_araddr;
        s7_arlen   = m3_arlen;
        s7_arsize  = m3_arsize;
        s7_arburst = m3_arburst;
        s7_arlock  = m3_arlock;
        s7_arcache = m3_arcache;
        s7_arprot  = m3_arprot;
        s7_arqos   = m3_arqos;
        s7_arvalid = m3_arvalid & m3_slave_select[7];
        s7_rready  = m3_rready;
    end
 else if (m4_slave_select[7]) begin
        s7_awid    = m4_awid;
        s7_awaddr  = m4_awaddr;
        s7_awlen   = m4_awlen;
        s7_awsize  = m4_awsize;
        s7_awburst = m4_awburst;
        s7_awlock  = m4_awlock;
        s7_awcache = m4_awcache;
        s7_awprot  = m4_awprot;
        s7_awqos   = m4_awqos;
        s7_awvalid = m4_awvalid & m4_slave_select[7];
        s7_wdata   = m4_wdata;
        s7_wstrb   = m4_wstrb;
        s7_wlast   = m4_wlast;
        s7_wvalid  = m4_wvalid;
        s7_bready  = m4_bready;
        s7_arid    = m4_arid;
        s7_araddr  = m4_araddr;
        s7_arlen   = m4_arlen;
        s7_arsize  = m4_arsize;
        s7_arburst = m4_arburst;
        s7_arlock  = m4_arlock;
        s7_arcache = m4_arcache;
        s7_arprot  = m4_arprot;
        s7_arqos   = m4_arqos;
        s7_arvalid = m4_arvalid & m4_slave_select[7];
        s7_rready  = m4_rready;
    end
 else if (m5_slave_select[7]) begin
        s7_awid    = m5_awid;
        s7_awaddr  = m5_awaddr;
        s7_awlen   = m5_awlen;
        s7_awsize  = m5_awsize;
        s7_awburst = m5_awburst;
        s7_awlock  = m5_awlock;
        s7_awcache = m5_awcache;
        s7_awprot  = m5_awprot;
        s7_awqos   = m5_awqos;
        s7_awvalid = m5_awvalid & m5_slave_select[7];
        s7_wdata   = m5_wdata;
        s7_wstrb   = m5_wstrb;
        s7_wlast   = m5_wlast;
        s7_wvalid  = m5_wvalid;
        s7_bready  = m5_bready;
        s7_arid    = m5_arid;
        s7_araddr  = m5_araddr;
        s7_arlen   = m5_arlen;
        s7_arsize  = m5_arsize;
        s7_arburst = m5_arburst;
        s7_arlock  = m5_arlock;
        s7_arcache = m5_arcache;
        s7_arprot  = m5_arprot;
        s7_arqos   = m5_arqos;
        s7_arvalid = m5_arvalid & m5_slave_select[7];
        s7_rready  = m5_rready;
    end
 else if (m6_slave_select[7]) begin
        s7_awid    = m6_awid;
        s7_awaddr  = m6_awaddr;
        s7_awlen   = m6_awlen;
        s7_awsize  = m6_awsize;
        s7_awburst = m6_awburst;
        s7_awlock  = m6_awlock;
        s7_awcache = m6_awcache;
        s7_awprot  = m6_awprot;
        s7_awqos   = m6_awqos;
        s7_awvalid = m6_awvalid & m6_slave_select[7];
        s7_wdata   = m6_wdata;
        s7_wstrb   = m6_wstrb;
        s7_wlast   = m6_wlast;
        s7_wvalid  = m6_wvalid;
        s7_bready  = m6_bready;
        s7_arid    = m6_arid;
        s7_araddr  = m6_araddr;
        s7_arlen   = m6_arlen;
        s7_arsize  = m6_arsize;
        s7_arburst = m6_arburst;
        s7_arlock  = m6_arlock;
        s7_arcache = m6_arcache;
        s7_arprot  = m6_arprot;
        s7_arqos   = m6_arqos;
        s7_arvalid = m6_arvalid & m6_slave_select[7];
        s7_rready  = m6_rready;
    end
 else if (m7_slave_select[7]) begin
        s7_awid    = m7_awid;
        s7_awaddr  = m7_awaddr;
        s7_awlen   = m7_awlen;
        s7_awsize  = m7_awsize;
        s7_awburst = m7_awburst;
        s7_awlock  = m7_awlock;
        s7_awcache = m7_awcache;
        s7_awprot  = m7_awprot;
        s7_awqos   = m7_awqos;
        s7_awvalid = m7_awvalid & m7_slave_select[7];
        s7_wdata   = m7_wdata;
        s7_wstrb   = m7_wstrb;
        s7_wlast   = m7_wlast;
        s7_wvalid  = m7_wvalid;
        s7_bready  = m7_bready;
        s7_arid    = m7_arid;
        s7_araddr  = m7_araddr;
        s7_arlen   = m7_arlen;
        s7_arsize  = m7_arsize;
        s7_arburst = m7_arburst;
        s7_arlock  = m7_arlock;
        s7_arcache = m7_arcache;
        s7_arprot  = m7_arprot;
        s7_arqos   = m7_arqos;
        s7_arvalid = m7_arvalid & m7_slave_select[7];
        s7_rready  = m7_rready;
    end
 else if (m8_slave_select[7]) begin
        s7_awid    = m8_awid;
        s7_awaddr  = m8_awaddr;
        s7_awlen   = m8_awlen;
        s7_awsize  = m8_awsize;
        s7_awburst = m8_awburst;
        s7_awlock  = m8_awlock;
        s7_awcache = m8_awcache;
        s7_awprot  = m8_awprot;
        s7_awqos   = m8_awqos;
        s7_awvalid = m8_awvalid & m8_slave_select[7];
        s7_wdata   = m8_wdata;
        s7_wstrb   = m8_wstrb;
        s7_wlast   = m8_wlast;
        s7_wvalid  = m8_wvalid;
        s7_bready  = m8_bready;
        s7_arid    = m8_arid;
        s7_araddr  = m8_araddr;
        s7_arlen   = m8_arlen;
        s7_arsize  = m8_arsize;
        s7_arburst = m8_arburst;
        s7_arlock  = m8_arlock;
        s7_arcache = m8_arcache;
        s7_arprot  = m8_arprot;
        s7_arqos   = m8_arqos;
        s7_arvalid = m8_arvalid & m8_slave_select[7];
        s7_rready  = m8_rready;
    end
 else if (m9_slave_select[7]) begin
        s7_awid    = m9_awid;
        s7_awaddr  = m9_awaddr;
        s7_awlen   = m9_awlen;
        s7_awsize  = m9_awsize;
        s7_awburst = m9_awburst;
        s7_awlock  = m9_awlock;
        s7_awcache = m9_awcache;
        s7_awprot  = m9_awprot;
        s7_awqos   = m9_awqos;
        s7_awvalid = m9_awvalid & m9_slave_select[7];
        s7_wdata   = m9_wdata;
        s7_wstrb   = m9_wstrb;
        s7_wlast   = m9_wlast;
        s7_wvalid  = m9_wvalid;
        s7_bready  = m9_bready;
        s7_arid    = m9_arid;
        s7_araddr  = m9_araddr;
        s7_arlen   = m9_arlen;
        s7_arsize  = m9_arsize;
        s7_arburst = m9_arburst;
        s7_arlock  = m9_arlock;
        s7_arcache = m9_arcache;
        s7_arprot  = m9_arprot;
        s7_arqos   = m9_arqos;
        s7_arvalid = m9_arvalid & m9_slave_select[7];
        s7_rready  = m9_rready;
    end
 else if (m10_slave_select[7]) begin
        s7_awid    = m10_awid;
        s7_awaddr  = m10_awaddr;
        s7_awlen   = m10_awlen;
        s7_awsize  = m10_awsize;
        s7_awburst = m10_awburst;
        s7_awlock  = m10_awlock;
        s7_awcache = m10_awcache;
        s7_awprot  = m10_awprot;
        s7_awqos   = m10_awqos;
        s7_awvalid = m10_awvalid & m10_slave_select[7];
        s7_wdata   = m10_wdata;
        s7_wstrb   = m10_wstrb;
        s7_wlast   = m10_wlast;
        s7_wvalid  = m10_wvalid;
        s7_bready  = m10_bready;
        s7_arid    = m10_arid;
        s7_araddr  = m10_araddr;
        s7_arlen   = m10_arlen;
        s7_arsize  = m10_arsize;
        s7_arburst = m10_arburst;
        s7_arlock  = m10_arlock;
        s7_arcache = m10_arcache;
        s7_arprot  = m10_arprot;
        s7_arqos   = m10_arqos;
        s7_arvalid = m10_arvalid & m10_slave_select[7];
        s7_rready  = m10_rready;
    end
 else if (m11_slave_select[7]) begin
        s7_awid    = m11_awid;
        s7_awaddr  = m11_awaddr;
        s7_awlen   = m11_awlen;
        s7_awsize  = m11_awsize;
        s7_awburst = m11_awburst;
        s7_awlock  = m11_awlock;
        s7_awcache = m11_awcache;
        s7_awprot  = m11_awprot;
        s7_awqos   = m11_awqos;
        s7_awvalid = m11_awvalid & m11_slave_select[7];
        s7_wdata   = m11_wdata;
        s7_wstrb   = m11_wstrb;
        s7_wlast   = m11_wlast;
        s7_wvalid  = m11_wvalid;
        s7_bready  = m11_bready;
        s7_arid    = m11_arid;
        s7_araddr  = m11_araddr;
        s7_arlen   = m11_arlen;
        s7_arsize  = m11_arsize;
        s7_arburst = m11_arburst;
        s7_arlock  = m11_arlock;
        s7_arcache = m11_arcache;
        s7_arprot  = m11_arprot;
        s7_arqos   = m11_arqos;
        s7_arvalid = m11_arvalid & m11_slave_select[7];
        s7_rready  = m11_rready;
    end
 else if (m12_slave_select[7]) begin
        s7_awid    = m12_awid;
        s7_awaddr  = m12_awaddr;
        s7_awlen   = m12_awlen;
        s7_awsize  = m12_awsize;
        s7_awburst = m12_awburst;
        s7_awlock  = m12_awlock;
        s7_awcache = m12_awcache;
        s7_awprot  = m12_awprot;
        s7_awqos   = m12_awqos;
        s7_awvalid = m12_awvalid & m12_slave_select[7];
        s7_wdata   = m12_wdata;
        s7_wstrb   = m12_wstrb;
        s7_wlast   = m12_wlast;
        s7_wvalid  = m12_wvalid;
        s7_bready  = m12_bready;
        s7_arid    = m12_arid;
        s7_araddr  = m12_araddr;
        s7_arlen   = m12_arlen;
        s7_arsize  = m12_arsize;
        s7_arburst = m12_arburst;
        s7_arlock  = m12_arlock;
        s7_arcache = m12_arcache;
        s7_arprot  = m12_arprot;
        s7_arqos   = m12_arqos;
        s7_arvalid = m12_arvalid & m12_slave_select[7];
        s7_rready  = m12_rready;
    end
 else if (m13_slave_select[7]) begin
        s7_awid    = m13_awid;
        s7_awaddr  = m13_awaddr;
        s7_awlen   = m13_awlen;
        s7_awsize  = m13_awsize;
        s7_awburst = m13_awburst;
        s7_awlock  = m13_awlock;
        s7_awcache = m13_awcache;
        s7_awprot  = m13_awprot;
        s7_awqos   = m13_awqos;
        s7_awvalid = m13_awvalid & m13_slave_select[7];
        s7_wdata   = m13_wdata;
        s7_wstrb   = m13_wstrb;
        s7_wlast   = m13_wlast;
        s7_wvalid  = m13_wvalid;
        s7_bready  = m13_bready;
        s7_arid    = m13_arid;
        s7_araddr  = m13_araddr;
        s7_arlen   = m13_arlen;
        s7_arsize  = m13_arsize;
        s7_arburst = m13_arburst;
        s7_arlock  = m13_arlock;
        s7_arcache = m13_arcache;
        s7_arprot  = m13_arprot;
        s7_arqos   = m13_arqos;
        s7_arvalid = m13_arvalid & m13_slave_select[7];
        s7_rready  = m13_rready;
    end
 else if (m14_slave_select[7]) begin
        s7_awid    = m14_awid;
        s7_awaddr  = m14_awaddr;
        s7_awlen   = m14_awlen;
        s7_awsize  = m14_awsize;
        s7_awburst = m14_awburst;
        s7_awlock  = m14_awlock;
        s7_awcache = m14_awcache;
        s7_awprot  = m14_awprot;
        s7_awqos   = m14_awqos;
        s7_awvalid = m14_awvalid & m14_slave_select[7];
        s7_wdata   = m14_wdata;
        s7_wstrb   = m14_wstrb;
        s7_wlast   = m14_wlast;
        s7_wvalid  = m14_wvalid;
        s7_bready  = m14_bready;
        s7_arid    = m14_arid;
        s7_araddr  = m14_araddr;
        s7_arlen   = m14_arlen;
        s7_arsize  = m14_arsize;
        s7_arburst = m14_arburst;
        s7_arlock  = m14_arlock;
        s7_arcache = m14_arcache;
        s7_arprot  = m14_arprot;
        s7_arqos   = m14_arqos;
        s7_arvalid = m14_arvalid & m14_slave_select[7];
        s7_rready  = m14_rready;
    end

end


// Slave 8 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s8_awid    = 'b0;
    s8_awaddr  = 'b0;
    s8_awlen   = 'b0;
    s8_awsize  = 'b0;
    s8_awburst = 'b0;
    s8_awlock  = 'b0;
    s8_awcache = 'b0;
    s8_awprot  = 'b0;
    s8_awqos   = 'b0;
    s8_awvalid = 'b0;
    s8_wdata   = 'b0;
    s8_wstrb   = 'b0;
    s8_wlast   = 'b0;
    s8_wvalid  = 'b0;
    s8_bready  = 'b0;
    s8_arid    = 'b0;
    s8_araddr  = 'b0;
    s8_arlen   = 'b0;
    s8_arsize  = 'b0;
    s8_arburst = 'b0;
    s8_arlock  = 'b0;
    s8_arcache = 'b0;
    s8_arprot  = 'b0;
    s8_arqos   = 'b0;
    s8_arvalid = 'b0;
    s8_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[8]) begin
        s8_awid    = m0_awid;
        s8_awaddr  = m0_awaddr;
        s8_awlen   = m0_awlen;
        s8_awsize  = m0_awsize;
        s8_awburst = m0_awburst;
        s8_awlock  = m0_awlock;
        s8_awcache = m0_awcache;
        s8_awprot  = m0_awprot;
        s8_awqos   = m0_awqos;
        s8_awvalid = m0_awvalid & m0_slave_select[8];
        s8_wdata   = m0_wdata;
        s8_wstrb   = m0_wstrb;
        s8_wlast   = m0_wlast;
        s8_wvalid  = m0_wvalid;
        s8_bready  = m0_bready;
        s8_arid    = m0_arid;
        s8_araddr  = m0_araddr;
        s8_arlen   = m0_arlen;
        s8_arsize  = m0_arsize;
        s8_arburst = m0_arburst;
        s8_arlock  = m0_arlock;
        s8_arcache = m0_arcache;
        s8_arprot  = m0_arprot;
        s8_arqos   = m0_arqos;
        s8_arvalid = m0_arvalid & m0_slave_select[8];
        s8_rready  = m0_rready;
    end
 else if (m1_slave_select[8]) begin
        s8_awid    = m1_awid;
        s8_awaddr  = m1_awaddr;
        s8_awlen   = m1_awlen;
        s8_awsize  = m1_awsize;
        s8_awburst = m1_awburst;
        s8_awlock  = m1_awlock;
        s8_awcache = m1_awcache;
        s8_awprot  = m1_awprot;
        s8_awqos   = m1_awqos;
        s8_awvalid = m1_awvalid & m1_slave_select[8];
        s8_wdata   = m1_wdata;
        s8_wstrb   = m1_wstrb;
        s8_wlast   = m1_wlast;
        s8_wvalid  = m1_wvalid;
        s8_bready  = m1_bready;
        s8_arid    = m1_arid;
        s8_araddr  = m1_araddr;
        s8_arlen   = m1_arlen;
        s8_arsize  = m1_arsize;
        s8_arburst = m1_arburst;
        s8_arlock  = m1_arlock;
        s8_arcache = m1_arcache;
        s8_arprot  = m1_arprot;
        s8_arqos   = m1_arqos;
        s8_arvalid = m1_arvalid & m1_slave_select[8];
        s8_rready  = m1_rready;
    end
 else if (m2_slave_select[8]) begin
        s8_awid    = m2_awid;
        s8_awaddr  = m2_awaddr;
        s8_awlen   = m2_awlen;
        s8_awsize  = m2_awsize;
        s8_awburst = m2_awburst;
        s8_awlock  = m2_awlock;
        s8_awcache = m2_awcache;
        s8_awprot  = m2_awprot;
        s8_awqos   = m2_awqos;
        s8_awvalid = m2_awvalid & m2_slave_select[8];
        s8_wdata   = m2_wdata;
        s8_wstrb   = m2_wstrb;
        s8_wlast   = m2_wlast;
        s8_wvalid  = m2_wvalid;
        s8_bready  = m2_bready;
        s8_arid    = m2_arid;
        s8_araddr  = m2_araddr;
        s8_arlen   = m2_arlen;
        s8_arsize  = m2_arsize;
        s8_arburst = m2_arburst;
        s8_arlock  = m2_arlock;
        s8_arcache = m2_arcache;
        s8_arprot  = m2_arprot;
        s8_arqos   = m2_arqos;
        s8_arvalid = m2_arvalid & m2_slave_select[8];
        s8_rready  = m2_rready;
    end
 else if (m3_slave_select[8]) begin
        s8_awid    = m3_awid;
        s8_awaddr  = m3_awaddr;
        s8_awlen   = m3_awlen;
        s8_awsize  = m3_awsize;
        s8_awburst = m3_awburst;
        s8_awlock  = m3_awlock;
        s8_awcache = m3_awcache;
        s8_awprot  = m3_awprot;
        s8_awqos   = m3_awqos;
        s8_awvalid = m3_awvalid & m3_slave_select[8];
        s8_wdata   = m3_wdata;
        s8_wstrb   = m3_wstrb;
        s8_wlast   = m3_wlast;
        s8_wvalid  = m3_wvalid;
        s8_bready  = m3_bready;
        s8_arid    = m3_arid;
        s8_araddr  = m3_araddr;
        s8_arlen   = m3_arlen;
        s8_arsize  = m3_arsize;
        s8_arburst = m3_arburst;
        s8_arlock  = m3_arlock;
        s8_arcache = m3_arcache;
        s8_arprot  = m3_arprot;
        s8_arqos   = m3_arqos;
        s8_arvalid = m3_arvalid & m3_slave_select[8];
        s8_rready  = m3_rready;
    end
 else if (m4_slave_select[8]) begin
        s8_awid    = m4_awid;
        s8_awaddr  = m4_awaddr;
        s8_awlen   = m4_awlen;
        s8_awsize  = m4_awsize;
        s8_awburst = m4_awburst;
        s8_awlock  = m4_awlock;
        s8_awcache = m4_awcache;
        s8_awprot  = m4_awprot;
        s8_awqos   = m4_awqos;
        s8_awvalid = m4_awvalid & m4_slave_select[8];
        s8_wdata   = m4_wdata;
        s8_wstrb   = m4_wstrb;
        s8_wlast   = m4_wlast;
        s8_wvalid  = m4_wvalid;
        s8_bready  = m4_bready;
        s8_arid    = m4_arid;
        s8_araddr  = m4_araddr;
        s8_arlen   = m4_arlen;
        s8_arsize  = m4_arsize;
        s8_arburst = m4_arburst;
        s8_arlock  = m4_arlock;
        s8_arcache = m4_arcache;
        s8_arprot  = m4_arprot;
        s8_arqos   = m4_arqos;
        s8_arvalid = m4_arvalid & m4_slave_select[8];
        s8_rready  = m4_rready;
    end
 else if (m5_slave_select[8]) begin
        s8_awid    = m5_awid;
        s8_awaddr  = m5_awaddr;
        s8_awlen   = m5_awlen;
        s8_awsize  = m5_awsize;
        s8_awburst = m5_awburst;
        s8_awlock  = m5_awlock;
        s8_awcache = m5_awcache;
        s8_awprot  = m5_awprot;
        s8_awqos   = m5_awqos;
        s8_awvalid = m5_awvalid & m5_slave_select[8];
        s8_wdata   = m5_wdata;
        s8_wstrb   = m5_wstrb;
        s8_wlast   = m5_wlast;
        s8_wvalid  = m5_wvalid;
        s8_bready  = m5_bready;
        s8_arid    = m5_arid;
        s8_araddr  = m5_araddr;
        s8_arlen   = m5_arlen;
        s8_arsize  = m5_arsize;
        s8_arburst = m5_arburst;
        s8_arlock  = m5_arlock;
        s8_arcache = m5_arcache;
        s8_arprot  = m5_arprot;
        s8_arqos   = m5_arqos;
        s8_arvalid = m5_arvalid & m5_slave_select[8];
        s8_rready  = m5_rready;
    end
 else if (m6_slave_select[8]) begin
        s8_awid    = m6_awid;
        s8_awaddr  = m6_awaddr;
        s8_awlen   = m6_awlen;
        s8_awsize  = m6_awsize;
        s8_awburst = m6_awburst;
        s8_awlock  = m6_awlock;
        s8_awcache = m6_awcache;
        s8_awprot  = m6_awprot;
        s8_awqos   = m6_awqos;
        s8_awvalid = m6_awvalid & m6_slave_select[8];
        s8_wdata   = m6_wdata;
        s8_wstrb   = m6_wstrb;
        s8_wlast   = m6_wlast;
        s8_wvalid  = m6_wvalid;
        s8_bready  = m6_bready;
        s8_arid    = m6_arid;
        s8_araddr  = m6_araddr;
        s8_arlen   = m6_arlen;
        s8_arsize  = m6_arsize;
        s8_arburst = m6_arburst;
        s8_arlock  = m6_arlock;
        s8_arcache = m6_arcache;
        s8_arprot  = m6_arprot;
        s8_arqos   = m6_arqos;
        s8_arvalid = m6_arvalid & m6_slave_select[8];
        s8_rready  = m6_rready;
    end
 else if (m7_slave_select[8]) begin
        s8_awid    = m7_awid;
        s8_awaddr  = m7_awaddr;
        s8_awlen   = m7_awlen;
        s8_awsize  = m7_awsize;
        s8_awburst = m7_awburst;
        s8_awlock  = m7_awlock;
        s8_awcache = m7_awcache;
        s8_awprot  = m7_awprot;
        s8_awqos   = m7_awqos;
        s8_awvalid = m7_awvalid & m7_slave_select[8];
        s8_wdata   = m7_wdata;
        s8_wstrb   = m7_wstrb;
        s8_wlast   = m7_wlast;
        s8_wvalid  = m7_wvalid;
        s8_bready  = m7_bready;
        s8_arid    = m7_arid;
        s8_araddr  = m7_araddr;
        s8_arlen   = m7_arlen;
        s8_arsize  = m7_arsize;
        s8_arburst = m7_arburst;
        s8_arlock  = m7_arlock;
        s8_arcache = m7_arcache;
        s8_arprot  = m7_arprot;
        s8_arqos   = m7_arqos;
        s8_arvalid = m7_arvalid & m7_slave_select[8];
        s8_rready  = m7_rready;
    end
 else if (m8_slave_select[8]) begin
        s8_awid    = m8_awid;
        s8_awaddr  = m8_awaddr;
        s8_awlen   = m8_awlen;
        s8_awsize  = m8_awsize;
        s8_awburst = m8_awburst;
        s8_awlock  = m8_awlock;
        s8_awcache = m8_awcache;
        s8_awprot  = m8_awprot;
        s8_awqos   = m8_awqos;
        s8_awvalid = m8_awvalid & m8_slave_select[8];
        s8_wdata   = m8_wdata;
        s8_wstrb   = m8_wstrb;
        s8_wlast   = m8_wlast;
        s8_wvalid  = m8_wvalid;
        s8_bready  = m8_bready;
        s8_arid    = m8_arid;
        s8_araddr  = m8_araddr;
        s8_arlen   = m8_arlen;
        s8_arsize  = m8_arsize;
        s8_arburst = m8_arburst;
        s8_arlock  = m8_arlock;
        s8_arcache = m8_arcache;
        s8_arprot  = m8_arprot;
        s8_arqos   = m8_arqos;
        s8_arvalid = m8_arvalid & m8_slave_select[8];
        s8_rready  = m8_rready;
    end
 else if (m9_slave_select[8]) begin
        s8_awid    = m9_awid;
        s8_awaddr  = m9_awaddr;
        s8_awlen   = m9_awlen;
        s8_awsize  = m9_awsize;
        s8_awburst = m9_awburst;
        s8_awlock  = m9_awlock;
        s8_awcache = m9_awcache;
        s8_awprot  = m9_awprot;
        s8_awqos   = m9_awqos;
        s8_awvalid = m9_awvalid & m9_slave_select[8];
        s8_wdata   = m9_wdata;
        s8_wstrb   = m9_wstrb;
        s8_wlast   = m9_wlast;
        s8_wvalid  = m9_wvalid;
        s8_bready  = m9_bready;
        s8_arid    = m9_arid;
        s8_araddr  = m9_araddr;
        s8_arlen   = m9_arlen;
        s8_arsize  = m9_arsize;
        s8_arburst = m9_arburst;
        s8_arlock  = m9_arlock;
        s8_arcache = m9_arcache;
        s8_arprot  = m9_arprot;
        s8_arqos   = m9_arqos;
        s8_arvalid = m9_arvalid & m9_slave_select[8];
        s8_rready  = m9_rready;
    end
 else if (m10_slave_select[8]) begin
        s8_awid    = m10_awid;
        s8_awaddr  = m10_awaddr;
        s8_awlen   = m10_awlen;
        s8_awsize  = m10_awsize;
        s8_awburst = m10_awburst;
        s8_awlock  = m10_awlock;
        s8_awcache = m10_awcache;
        s8_awprot  = m10_awprot;
        s8_awqos   = m10_awqos;
        s8_awvalid = m10_awvalid & m10_slave_select[8];
        s8_wdata   = m10_wdata;
        s8_wstrb   = m10_wstrb;
        s8_wlast   = m10_wlast;
        s8_wvalid  = m10_wvalid;
        s8_bready  = m10_bready;
        s8_arid    = m10_arid;
        s8_araddr  = m10_araddr;
        s8_arlen   = m10_arlen;
        s8_arsize  = m10_arsize;
        s8_arburst = m10_arburst;
        s8_arlock  = m10_arlock;
        s8_arcache = m10_arcache;
        s8_arprot  = m10_arprot;
        s8_arqos   = m10_arqos;
        s8_arvalid = m10_arvalid & m10_slave_select[8];
        s8_rready  = m10_rready;
    end
 else if (m11_slave_select[8]) begin
        s8_awid    = m11_awid;
        s8_awaddr  = m11_awaddr;
        s8_awlen   = m11_awlen;
        s8_awsize  = m11_awsize;
        s8_awburst = m11_awburst;
        s8_awlock  = m11_awlock;
        s8_awcache = m11_awcache;
        s8_awprot  = m11_awprot;
        s8_awqos   = m11_awqos;
        s8_awvalid = m11_awvalid & m11_slave_select[8];
        s8_wdata   = m11_wdata;
        s8_wstrb   = m11_wstrb;
        s8_wlast   = m11_wlast;
        s8_wvalid  = m11_wvalid;
        s8_bready  = m11_bready;
        s8_arid    = m11_arid;
        s8_araddr  = m11_araddr;
        s8_arlen   = m11_arlen;
        s8_arsize  = m11_arsize;
        s8_arburst = m11_arburst;
        s8_arlock  = m11_arlock;
        s8_arcache = m11_arcache;
        s8_arprot  = m11_arprot;
        s8_arqos   = m11_arqos;
        s8_arvalid = m11_arvalid & m11_slave_select[8];
        s8_rready  = m11_rready;
    end
 else if (m12_slave_select[8]) begin
        s8_awid    = m12_awid;
        s8_awaddr  = m12_awaddr;
        s8_awlen   = m12_awlen;
        s8_awsize  = m12_awsize;
        s8_awburst = m12_awburst;
        s8_awlock  = m12_awlock;
        s8_awcache = m12_awcache;
        s8_awprot  = m12_awprot;
        s8_awqos   = m12_awqos;
        s8_awvalid = m12_awvalid & m12_slave_select[8];
        s8_wdata   = m12_wdata;
        s8_wstrb   = m12_wstrb;
        s8_wlast   = m12_wlast;
        s8_wvalid  = m12_wvalid;
        s8_bready  = m12_bready;
        s8_arid    = m12_arid;
        s8_araddr  = m12_araddr;
        s8_arlen   = m12_arlen;
        s8_arsize  = m12_arsize;
        s8_arburst = m12_arburst;
        s8_arlock  = m12_arlock;
        s8_arcache = m12_arcache;
        s8_arprot  = m12_arprot;
        s8_arqos   = m12_arqos;
        s8_arvalid = m12_arvalid & m12_slave_select[8];
        s8_rready  = m12_rready;
    end
 else if (m13_slave_select[8]) begin
        s8_awid    = m13_awid;
        s8_awaddr  = m13_awaddr;
        s8_awlen   = m13_awlen;
        s8_awsize  = m13_awsize;
        s8_awburst = m13_awburst;
        s8_awlock  = m13_awlock;
        s8_awcache = m13_awcache;
        s8_awprot  = m13_awprot;
        s8_awqos   = m13_awqos;
        s8_awvalid = m13_awvalid & m13_slave_select[8];
        s8_wdata   = m13_wdata;
        s8_wstrb   = m13_wstrb;
        s8_wlast   = m13_wlast;
        s8_wvalid  = m13_wvalid;
        s8_bready  = m13_bready;
        s8_arid    = m13_arid;
        s8_araddr  = m13_araddr;
        s8_arlen   = m13_arlen;
        s8_arsize  = m13_arsize;
        s8_arburst = m13_arburst;
        s8_arlock  = m13_arlock;
        s8_arcache = m13_arcache;
        s8_arprot  = m13_arprot;
        s8_arqos   = m13_arqos;
        s8_arvalid = m13_arvalid & m13_slave_select[8];
        s8_rready  = m13_rready;
    end
 else if (m14_slave_select[8]) begin
        s8_awid    = m14_awid;
        s8_awaddr  = m14_awaddr;
        s8_awlen   = m14_awlen;
        s8_awsize  = m14_awsize;
        s8_awburst = m14_awburst;
        s8_awlock  = m14_awlock;
        s8_awcache = m14_awcache;
        s8_awprot  = m14_awprot;
        s8_awqos   = m14_awqos;
        s8_awvalid = m14_awvalid & m14_slave_select[8];
        s8_wdata   = m14_wdata;
        s8_wstrb   = m14_wstrb;
        s8_wlast   = m14_wlast;
        s8_wvalid  = m14_wvalid;
        s8_bready  = m14_bready;
        s8_arid    = m14_arid;
        s8_araddr  = m14_araddr;
        s8_arlen   = m14_arlen;
        s8_arsize  = m14_arsize;
        s8_arburst = m14_arburst;
        s8_arlock  = m14_arlock;
        s8_arcache = m14_arcache;
        s8_arprot  = m14_arprot;
        s8_arqos   = m14_arqos;
        s8_arvalid = m14_arvalid & m14_slave_select[8];
        s8_rready  = m14_rready;
    end

end


// Slave 9 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s9_awid    = 'b0;
    s9_awaddr  = 'b0;
    s9_awlen   = 'b0;
    s9_awsize  = 'b0;
    s9_awburst = 'b0;
    s9_awlock  = 'b0;
    s9_awcache = 'b0;
    s9_awprot  = 'b0;
    s9_awqos   = 'b0;
    s9_awvalid = 'b0;
    s9_wdata   = 'b0;
    s9_wstrb   = 'b0;
    s9_wlast   = 'b0;
    s9_wvalid  = 'b0;
    s9_bready  = 'b0;
    s9_arid    = 'b0;
    s9_araddr  = 'b0;
    s9_arlen   = 'b0;
    s9_arsize  = 'b0;
    s9_arburst = 'b0;
    s9_arlock  = 'b0;
    s9_arcache = 'b0;
    s9_arprot  = 'b0;
    s9_arqos   = 'b0;
    s9_arvalid = 'b0;
    s9_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[9]) begin
        s9_awid    = m0_awid;
        s9_awaddr  = m0_awaddr;
        s9_awlen   = m0_awlen;
        s9_awsize  = m0_awsize;
        s9_awburst = m0_awburst;
        s9_awlock  = m0_awlock;
        s9_awcache = m0_awcache;
        s9_awprot  = m0_awprot;
        s9_awqos   = m0_awqos;
        s9_awvalid = m0_awvalid & m0_slave_select[9];
        s9_wdata   = m0_wdata;
        s9_wstrb   = m0_wstrb;
        s9_wlast   = m0_wlast;
        s9_wvalid  = m0_wvalid;
        s9_bready  = m0_bready;
        s9_arid    = m0_arid;
        s9_araddr  = m0_araddr;
        s9_arlen   = m0_arlen;
        s9_arsize  = m0_arsize;
        s9_arburst = m0_arburst;
        s9_arlock  = m0_arlock;
        s9_arcache = m0_arcache;
        s9_arprot  = m0_arprot;
        s9_arqos   = m0_arqos;
        s9_arvalid = m0_arvalid & m0_slave_select[9];
        s9_rready  = m0_rready;
    end
 else if (m1_slave_select[9]) begin
        s9_awid    = m1_awid;
        s9_awaddr  = m1_awaddr;
        s9_awlen   = m1_awlen;
        s9_awsize  = m1_awsize;
        s9_awburst = m1_awburst;
        s9_awlock  = m1_awlock;
        s9_awcache = m1_awcache;
        s9_awprot  = m1_awprot;
        s9_awqos   = m1_awqos;
        s9_awvalid = m1_awvalid & m1_slave_select[9];
        s9_wdata   = m1_wdata;
        s9_wstrb   = m1_wstrb;
        s9_wlast   = m1_wlast;
        s9_wvalid  = m1_wvalid;
        s9_bready  = m1_bready;
        s9_arid    = m1_arid;
        s9_araddr  = m1_araddr;
        s9_arlen   = m1_arlen;
        s9_arsize  = m1_arsize;
        s9_arburst = m1_arburst;
        s9_arlock  = m1_arlock;
        s9_arcache = m1_arcache;
        s9_arprot  = m1_arprot;
        s9_arqos   = m1_arqos;
        s9_arvalid = m1_arvalid & m1_slave_select[9];
        s9_rready  = m1_rready;
    end
 else if (m2_slave_select[9]) begin
        s9_awid    = m2_awid;
        s9_awaddr  = m2_awaddr;
        s9_awlen   = m2_awlen;
        s9_awsize  = m2_awsize;
        s9_awburst = m2_awburst;
        s9_awlock  = m2_awlock;
        s9_awcache = m2_awcache;
        s9_awprot  = m2_awprot;
        s9_awqos   = m2_awqos;
        s9_awvalid = m2_awvalid & m2_slave_select[9];
        s9_wdata   = m2_wdata;
        s9_wstrb   = m2_wstrb;
        s9_wlast   = m2_wlast;
        s9_wvalid  = m2_wvalid;
        s9_bready  = m2_bready;
        s9_arid    = m2_arid;
        s9_araddr  = m2_araddr;
        s9_arlen   = m2_arlen;
        s9_arsize  = m2_arsize;
        s9_arburst = m2_arburst;
        s9_arlock  = m2_arlock;
        s9_arcache = m2_arcache;
        s9_arprot  = m2_arprot;
        s9_arqos   = m2_arqos;
        s9_arvalid = m2_arvalid & m2_slave_select[9];
        s9_rready  = m2_rready;
    end
 else if (m3_slave_select[9]) begin
        s9_awid    = m3_awid;
        s9_awaddr  = m3_awaddr;
        s9_awlen   = m3_awlen;
        s9_awsize  = m3_awsize;
        s9_awburst = m3_awburst;
        s9_awlock  = m3_awlock;
        s9_awcache = m3_awcache;
        s9_awprot  = m3_awprot;
        s9_awqos   = m3_awqos;
        s9_awvalid = m3_awvalid & m3_slave_select[9];
        s9_wdata   = m3_wdata;
        s9_wstrb   = m3_wstrb;
        s9_wlast   = m3_wlast;
        s9_wvalid  = m3_wvalid;
        s9_bready  = m3_bready;
        s9_arid    = m3_arid;
        s9_araddr  = m3_araddr;
        s9_arlen   = m3_arlen;
        s9_arsize  = m3_arsize;
        s9_arburst = m3_arburst;
        s9_arlock  = m3_arlock;
        s9_arcache = m3_arcache;
        s9_arprot  = m3_arprot;
        s9_arqos   = m3_arqos;
        s9_arvalid = m3_arvalid & m3_slave_select[9];
        s9_rready  = m3_rready;
    end
 else if (m4_slave_select[9]) begin
        s9_awid    = m4_awid;
        s9_awaddr  = m4_awaddr;
        s9_awlen   = m4_awlen;
        s9_awsize  = m4_awsize;
        s9_awburst = m4_awburst;
        s9_awlock  = m4_awlock;
        s9_awcache = m4_awcache;
        s9_awprot  = m4_awprot;
        s9_awqos   = m4_awqos;
        s9_awvalid = m4_awvalid & m4_slave_select[9];
        s9_wdata   = m4_wdata;
        s9_wstrb   = m4_wstrb;
        s9_wlast   = m4_wlast;
        s9_wvalid  = m4_wvalid;
        s9_bready  = m4_bready;
        s9_arid    = m4_arid;
        s9_araddr  = m4_araddr;
        s9_arlen   = m4_arlen;
        s9_arsize  = m4_arsize;
        s9_arburst = m4_arburst;
        s9_arlock  = m4_arlock;
        s9_arcache = m4_arcache;
        s9_arprot  = m4_arprot;
        s9_arqos   = m4_arqos;
        s9_arvalid = m4_arvalid & m4_slave_select[9];
        s9_rready  = m4_rready;
    end
 else if (m5_slave_select[9]) begin
        s9_awid    = m5_awid;
        s9_awaddr  = m5_awaddr;
        s9_awlen   = m5_awlen;
        s9_awsize  = m5_awsize;
        s9_awburst = m5_awburst;
        s9_awlock  = m5_awlock;
        s9_awcache = m5_awcache;
        s9_awprot  = m5_awprot;
        s9_awqos   = m5_awqos;
        s9_awvalid = m5_awvalid & m5_slave_select[9];
        s9_wdata   = m5_wdata;
        s9_wstrb   = m5_wstrb;
        s9_wlast   = m5_wlast;
        s9_wvalid  = m5_wvalid;
        s9_bready  = m5_bready;
        s9_arid    = m5_arid;
        s9_araddr  = m5_araddr;
        s9_arlen   = m5_arlen;
        s9_arsize  = m5_arsize;
        s9_arburst = m5_arburst;
        s9_arlock  = m5_arlock;
        s9_arcache = m5_arcache;
        s9_arprot  = m5_arprot;
        s9_arqos   = m5_arqos;
        s9_arvalid = m5_arvalid & m5_slave_select[9];
        s9_rready  = m5_rready;
    end
 else if (m6_slave_select[9]) begin
        s9_awid    = m6_awid;
        s9_awaddr  = m6_awaddr;
        s9_awlen   = m6_awlen;
        s9_awsize  = m6_awsize;
        s9_awburst = m6_awburst;
        s9_awlock  = m6_awlock;
        s9_awcache = m6_awcache;
        s9_awprot  = m6_awprot;
        s9_awqos   = m6_awqos;
        s9_awvalid = m6_awvalid & m6_slave_select[9];
        s9_wdata   = m6_wdata;
        s9_wstrb   = m6_wstrb;
        s9_wlast   = m6_wlast;
        s9_wvalid  = m6_wvalid;
        s9_bready  = m6_bready;
        s9_arid    = m6_arid;
        s9_araddr  = m6_araddr;
        s9_arlen   = m6_arlen;
        s9_arsize  = m6_arsize;
        s9_arburst = m6_arburst;
        s9_arlock  = m6_arlock;
        s9_arcache = m6_arcache;
        s9_arprot  = m6_arprot;
        s9_arqos   = m6_arqos;
        s9_arvalid = m6_arvalid & m6_slave_select[9];
        s9_rready  = m6_rready;
    end
 else if (m7_slave_select[9]) begin
        s9_awid    = m7_awid;
        s9_awaddr  = m7_awaddr;
        s9_awlen   = m7_awlen;
        s9_awsize  = m7_awsize;
        s9_awburst = m7_awburst;
        s9_awlock  = m7_awlock;
        s9_awcache = m7_awcache;
        s9_awprot  = m7_awprot;
        s9_awqos   = m7_awqos;
        s9_awvalid = m7_awvalid & m7_slave_select[9];
        s9_wdata   = m7_wdata;
        s9_wstrb   = m7_wstrb;
        s9_wlast   = m7_wlast;
        s9_wvalid  = m7_wvalid;
        s9_bready  = m7_bready;
        s9_arid    = m7_arid;
        s9_araddr  = m7_araddr;
        s9_arlen   = m7_arlen;
        s9_arsize  = m7_arsize;
        s9_arburst = m7_arburst;
        s9_arlock  = m7_arlock;
        s9_arcache = m7_arcache;
        s9_arprot  = m7_arprot;
        s9_arqos   = m7_arqos;
        s9_arvalid = m7_arvalid & m7_slave_select[9];
        s9_rready  = m7_rready;
    end
 else if (m8_slave_select[9]) begin
        s9_awid    = m8_awid;
        s9_awaddr  = m8_awaddr;
        s9_awlen   = m8_awlen;
        s9_awsize  = m8_awsize;
        s9_awburst = m8_awburst;
        s9_awlock  = m8_awlock;
        s9_awcache = m8_awcache;
        s9_awprot  = m8_awprot;
        s9_awqos   = m8_awqos;
        s9_awvalid = m8_awvalid & m8_slave_select[9];
        s9_wdata   = m8_wdata;
        s9_wstrb   = m8_wstrb;
        s9_wlast   = m8_wlast;
        s9_wvalid  = m8_wvalid;
        s9_bready  = m8_bready;
        s9_arid    = m8_arid;
        s9_araddr  = m8_araddr;
        s9_arlen   = m8_arlen;
        s9_arsize  = m8_arsize;
        s9_arburst = m8_arburst;
        s9_arlock  = m8_arlock;
        s9_arcache = m8_arcache;
        s9_arprot  = m8_arprot;
        s9_arqos   = m8_arqos;
        s9_arvalid = m8_arvalid & m8_slave_select[9];
        s9_rready  = m8_rready;
    end
 else if (m9_slave_select[9]) begin
        s9_awid    = m9_awid;
        s9_awaddr  = m9_awaddr;
        s9_awlen   = m9_awlen;
        s9_awsize  = m9_awsize;
        s9_awburst = m9_awburst;
        s9_awlock  = m9_awlock;
        s9_awcache = m9_awcache;
        s9_awprot  = m9_awprot;
        s9_awqos   = m9_awqos;
        s9_awvalid = m9_awvalid & m9_slave_select[9];
        s9_wdata   = m9_wdata;
        s9_wstrb   = m9_wstrb;
        s9_wlast   = m9_wlast;
        s9_wvalid  = m9_wvalid;
        s9_bready  = m9_bready;
        s9_arid    = m9_arid;
        s9_araddr  = m9_araddr;
        s9_arlen   = m9_arlen;
        s9_arsize  = m9_arsize;
        s9_arburst = m9_arburst;
        s9_arlock  = m9_arlock;
        s9_arcache = m9_arcache;
        s9_arprot  = m9_arprot;
        s9_arqos   = m9_arqos;
        s9_arvalid = m9_arvalid & m9_slave_select[9];
        s9_rready  = m9_rready;
    end
 else if (m10_slave_select[9]) begin
        s9_awid    = m10_awid;
        s9_awaddr  = m10_awaddr;
        s9_awlen   = m10_awlen;
        s9_awsize  = m10_awsize;
        s9_awburst = m10_awburst;
        s9_awlock  = m10_awlock;
        s9_awcache = m10_awcache;
        s9_awprot  = m10_awprot;
        s9_awqos   = m10_awqos;
        s9_awvalid = m10_awvalid & m10_slave_select[9];
        s9_wdata   = m10_wdata;
        s9_wstrb   = m10_wstrb;
        s9_wlast   = m10_wlast;
        s9_wvalid  = m10_wvalid;
        s9_bready  = m10_bready;
        s9_arid    = m10_arid;
        s9_araddr  = m10_araddr;
        s9_arlen   = m10_arlen;
        s9_arsize  = m10_arsize;
        s9_arburst = m10_arburst;
        s9_arlock  = m10_arlock;
        s9_arcache = m10_arcache;
        s9_arprot  = m10_arprot;
        s9_arqos   = m10_arqos;
        s9_arvalid = m10_arvalid & m10_slave_select[9];
        s9_rready  = m10_rready;
    end
 else if (m11_slave_select[9]) begin
        s9_awid    = m11_awid;
        s9_awaddr  = m11_awaddr;
        s9_awlen   = m11_awlen;
        s9_awsize  = m11_awsize;
        s9_awburst = m11_awburst;
        s9_awlock  = m11_awlock;
        s9_awcache = m11_awcache;
        s9_awprot  = m11_awprot;
        s9_awqos   = m11_awqos;
        s9_awvalid = m11_awvalid & m11_slave_select[9];
        s9_wdata   = m11_wdata;
        s9_wstrb   = m11_wstrb;
        s9_wlast   = m11_wlast;
        s9_wvalid  = m11_wvalid;
        s9_bready  = m11_bready;
        s9_arid    = m11_arid;
        s9_araddr  = m11_araddr;
        s9_arlen   = m11_arlen;
        s9_arsize  = m11_arsize;
        s9_arburst = m11_arburst;
        s9_arlock  = m11_arlock;
        s9_arcache = m11_arcache;
        s9_arprot  = m11_arprot;
        s9_arqos   = m11_arqos;
        s9_arvalid = m11_arvalid & m11_slave_select[9];
        s9_rready  = m11_rready;
    end
 else if (m12_slave_select[9]) begin
        s9_awid    = m12_awid;
        s9_awaddr  = m12_awaddr;
        s9_awlen   = m12_awlen;
        s9_awsize  = m12_awsize;
        s9_awburst = m12_awburst;
        s9_awlock  = m12_awlock;
        s9_awcache = m12_awcache;
        s9_awprot  = m12_awprot;
        s9_awqos   = m12_awqos;
        s9_awvalid = m12_awvalid & m12_slave_select[9];
        s9_wdata   = m12_wdata;
        s9_wstrb   = m12_wstrb;
        s9_wlast   = m12_wlast;
        s9_wvalid  = m12_wvalid;
        s9_bready  = m12_bready;
        s9_arid    = m12_arid;
        s9_araddr  = m12_araddr;
        s9_arlen   = m12_arlen;
        s9_arsize  = m12_arsize;
        s9_arburst = m12_arburst;
        s9_arlock  = m12_arlock;
        s9_arcache = m12_arcache;
        s9_arprot  = m12_arprot;
        s9_arqos   = m12_arqos;
        s9_arvalid = m12_arvalid & m12_slave_select[9];
        s9_rready  = m12_rready;
    end
 else if (m13_slave_select[9]) begin
        s9_awid    = m13_awid;
        s9_awaddr  = m13_awaddr;
        s9_awlen   = m13_awlen;
        s9_awsize  = m13_awsize;
        s9_awburst = m13_awburst;
        s9_awlock  = m13_awlock;
        s9_awcache = m13_awcache;
        s9_awprot  = m13_awprot;
        s9_awqos   = m13_awqos;
        s9_awvalid = m13_awvalid & m13_slave_select[9];
        s9_wdata   = m13_wdata;
        s9_wstrb   = m13_wstrb;
        s9_wlast   = m13_wlast;
        s9_wvalid  = m13_wvalid;
        s9_bready  = m13_bready;
        s9_arid    = m13_arid;
        s9_araddr  = m13_araddr;
        s9_arlen   = m13_arlen;
        s9_arsize  = m13_arsize;
        s9_arburst = m13_arburst;
        s9_arlock  = m13_arlock;
        s9_arcache = m13_arcache;
        s9_arprot  = m13_arprot;
        s9_arqos   = m13_arqos;
        s9_arvalid = m13_arvalid & m13_slave_select[9];
        s9_rready  = m13_rready;
    end
 else if (m14_slave_select[9]) begin
        s9_awid    = m14_awid;
        s9_awaddr  = m14_awaddr;
        s9_awlen   = m14_awlen;
        s9_awsize  = m14_awsize;
        s9_awburst = m14_awburst;
        s9_awlock  = m14_awlock;
        s9_awcache = m14_awcache;
        s9_awprot  = m14_awprot;
        s9_awqos   = m14_awqos;
        s9_awvalid = m14_awvalid & m14_slave_select[9];
        s9_wdata   = m14_wdata;
        s9_wstrb   = m14_wstrb;
        s9_wlast   = m14_wlast;
        s9_wvalid  = m14_wvalid;
        s9_bready  = m14_bready;
        s9_arid    = m14_arid;
        s9_araddr  = m14_araddr;
        s9_arlen   = m14_arlen;
        s9_arsize  = m14_arsize;
        s9_arburst = m14_arburst;
        s9_arlock  = m14_arlock;
        s9_arcache = m14_arcache;
        s9_arprot  = m14_arprot;
        s9_arqos   = m14_arqos;
        s9_arvalid = m14_arvalid & m14_slave_select[9];
        s9_rready  = m14_rready;
    end

end


// Slave 10 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s10_awid    = 'b0;
    s10_awaddr  = 'b0;
    s10_awlen   = 'b0;
    s10_awsize  = 'b0;
    s10_awburst = 'b0;
    s10_awlock  = 'b0;
    s10_awcache = 'b0;
    s10_awprot  = 'b0;
    s10_awqos   = 'b0;
    s10_awvalid = 'b0;
    s10_wdata   = 'b0;
    s10_wstrb   = 'b0;
    s10_wlast   = 'b0;
    s10_wvalid  = 'b0;
    s10_bready  = 'b0;
    s10_arid    = 'b0;
    s10_araddr  = 'b0;
    s10_arlen   = 'b0;
    s10_arsize  = 'b0;
    s10_arburst = 'b0;
    s10_arlock  = 'b0;
    s10_arcache = 'b0;
    s10_arprot  = 'b0;
    s10_arqos   = 'b0;
    s10_arvalid = 'b0;
    s10_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[10]) begin
        s10_awid    = m0_awid;
        s10_awaddr  = m0_awaddr;
        s10_awlen   = m0_awlen;
        s10_awsize  = m0_awsize;
        s10_awburst = m0_awburst;
        s10_awlock  = m0_awlock;
        s10_awcache = m0_awcache;
        s10_awprot  = m0_awprot;
        s10_awqos   = m0_awqos;
        s10_awvalid = m0_awvalid & m0_slave_select[10];
        s10_wdata   = m0_wdata;
        s10_wstrb   = m0_wstrb;
        s10_wlast   = m0_wlast;
        s10_wvalid  = m0_wvalid;
        s10_bready  = m0_bready;
        s10_arid    = m0_arid;
        s10_araddr  = m0_araddr;
        s10_arlen   = m0_arlen;
        s10_arsize  = m0_arsize;
        s10_arburst = m0_arburst;
        s10_arlock  = m0_arlock;
        s10_arcache = m0_arcache;
        s10_arprot  = m0_arprot;
        s10_arqos   = m0_arqos;
        s10_arvalid = m0_arvalid & m0_slave_select[10];
        s10_rready  = m0_rready;
    end
 else if (m1_slave_select[10]) begin
        s10_awid    = m1_awid;
        s10_awaddr  = m1_awaddr;
        s10_awlen   = m1_awlen;
        s10_awsize  = m1_awsize;
        s10_awburst = m1_awburst;
        s10_awlock  = m1_awlock;
        s10_awcache = m1_awcache;
        s10_awprot  = m1_awprot;
        s10_awqos   = m1_awqos;
        s10_awvalid = m1_awvalid & m1_slave_select[10];
        s10_wdata   = m1_wdata;
        s10_wstrb   = m1_wstrb;
        s10_wlast   = m1_wlast;
        s10_wvalid  = m1_wvalid;
        s10_bready  = m1_bready;
        s10_arid    = m1_arid;
        s10_araddr  = m1_araddr;
        s10_arlen   = m1_arlen;
        s10_arsize  = m1_arsize;
        s10_arburst = m1_arburst;
        s10_arlock  = m1_arlock;
        s10_arcache = m1_arcache;
        s10_arprot  = m1_arprot;
        s10_arqos   = m1_arqos;
        s10_arvalid = m1_arvalid & m1_slave_select[10];
        s10_rready  = m1_rready;
    end
 else if (m2_slave_select[10]) begin
        s10_awid    = m2_awid;
        s10_awaddr  = m2_awaddr;
        s10_awlen   = m2_awlen;
        s10_awsize  = m2_awsize;
        s10_awburst = m2_awburst;
        s10_awlock  = m2_awlock;
        s10_awcache = m2_awcache;
        s10_awprot  = m2_awprot;
        s10_awqos   = m2_awqos;
        s10_awvalid = m2_awvalid & m2_slave_select[10];
        s10_wdata   = m2_wdata;
        s10_wstrb   = m2_wstrb;
        s10_wlast   = m2_wlast;
        s10_wvalid  = m2_wvalid;
        s10_bready  = m2_bready;
        s10_arid    = m2_arid;
        s10_araddr  = m2_araddr;
        s10_arlen   = m2_arlen;
        s10_arsize  = m2_arsize;
        s10_arburst = m2_arburst;
        s10_arlock  = m2_arlock;
        s10_arcache = m2_arcache;
        s10_arprot  = m2_arprot;
        s10_arqos   = m2_arqos;
        s10_arvalid = m2_arvalid & m2_slave_select[10];
        s10_rready  = m2_rready;
    end
 else if (m3_slave_select[10]) begin
        s10_awid    = m3_awid;
        s10_awaddr  = m3_awaddr;
        s10_awlen   = m3_awlen;
        s10_awsize  = m3_awsize;
        s10_awburst = m3_awburst;
        s10_awlock  = m3_awlock;
        s10_awcache = m3_awcache;
        s10_awprot  = m3_awprot;
        s10_awqos   = m3_awqos;
        s10_awvalid = m3_awvalid & m3_slave_select[10];
        s10_wdata   = m3_wdata;
        s10_wstrb   = m3_wstrb;
        s10_wlast   = m3_wlast;
        s10_wvalid  = m3_wvalid;
        s10_bready  = m3_bready;
        s10_arid    = m3_arid;
        s10_araddr  = m3_araddr;
        s10_arlen   = m3_arlen;
        s10_arsize  = m3_arsize;
        s10_arburst = m3_arburst;
        s10_arlock  = m3_arlock;
        s10_arcache = m3_arcache;
        s10_arprot  = m3_arprot;
        s10_arqos   = m3_arqos;
        s10_arvalid = m3_arvalid & m3_slave_select[10];
        s10_rready  = m3_rready;
    end
 else if (m4_slave_select[10]) begin
        s10_awid    = m4_awid;
        s10_awaddr  = m4_awaddr;
        s10_awlen   = m4_awlen;
        s10_awsize  = m4_awsize;
        s10_awburst = m4_awburst;
        s10_awlock  = m4_awlock;
        s10_awcache = m4_awcache;
        s10_awprot  = m4_awprot;
        s10_awqos   = m4_awqos;
        s10_awvalid = m4_awvalid & m4_slave_select[10];
        s10_wdata   = m4_wdata;
        s10_wstrb   = m4_wstrb;
        s10_wlast   = m4_wlast;
        s10_wvalid  = m4_wvalid;
        s10_bready  = m4_bready;
        s10_arid    = m4_arid;
        s10_araddr  = m4_araddr;
        s10_arlen   = m4_arlen;
        s10_arsize  = m4_arsize;
        s10_arburst = m4_arburst;
        s10_arlock  = m4_arlock;
        s10_arcache = m4_arcache;
        s10_arprot  = m4_arprot;
        s10_arqos   = m4_arqos;
        s10_arvalid = m4_arvalid & m4_slave_select[10];
        s10_rready  = m4_rready;
    end
 else if (m5_slave_select[10]) begin
        s10_awid    = m5_awid;
        s10_awaddr  = m5_awaddr;
        s10_awlen   = m5_awlen;
        s10_awsize  = m5_awsize;
        s10_awburst = m5_awburst;
        s10_awlock  = m5_awlock;
        s10_awcache = m5_awcache;
        s10_awprot  = m5_awprot;
        s10_awqos   = m5_awqos;
        s10_awvalid = m5_awvalid & m5_slave_select[10];
        s10_wdata   = m5_wdata;
        s10_wstrb   = m5_wstrb;
        s10_wlast   = m5_wlast;
        s10_wvalid  = m5_wvalid;
        s10_bready  = m5_bready;
        s10_arid    = m5_arid;
        s10_araddr  = m5_araddr;
        s10_arlen   = m5_arlen;
        s10_arsize  = m5_arsize;
        s10_arburst = m5_arburst;
        s10_arlock  = m5_arlock;
        s10_arcache = m5_arcache;
        s10_arprot  = m5_arprot;
        s10_arqos   = m5_arqos;
        s10_arvalid = m5_arvalid & m5_slave_select[10];
        s10_rready  = m5_rready;
    end
 else if (m6_slave_select[10]) begin
        s10_awid    = m6_awid;
        s10_awaddr  = m6_awaddr;
        s10_awlen   = m6_awlen;
        s10_awsize  = m6_awsize;
        s10_awburst = m6_awburst;
        s10_awlock  = m6_awlock;
        s10_awcache = m6_awcache;
        s10_awprot  = m6_awprot;
        s10_awqos   = m6_awqos;
        s10_awvalid = m6_awvalid & m6_slave_select[10];
        s10_wdata   = m6_wdata;
        s10_wstrb   = m6_wstrb;
        s10_wlast   = m6_wlast;
        s10_wvalid  = m6_wvalid;
        s10_bready  = m6_bready;
        s10_arid    = m6_arid;
        s10_araddr  = m6_araddr;
        s10_arlen   = m6_arlen;
        s10_arsize  = m6_arsize;
        s10_arburst = m6_arburst;
        s10_arlock  = m6_arlock;
        s10_arcache = m6_arcache;
        s10_arprot  = m6_arprot;
        s10_arqos   = m6_arqos;
        s10_arvalid = m6_arvalid & m6_slave_select[10];
        s10_rready  = m6_rready;
    end
 else if (m7_slave_select[10]) begin
        s10_awid    = m7_awid;
        s10_awaddr  = m7_awaddr;
        s10_awlen   = m7_awlen;
        s10_awsize  = m7_awsize;
        s10_awburst = m7_awburst;
        s10_awlock  = m7_awlock;
        s10_awcache = m7_awcache;
        s10_awprot  = m7_awprot;
        s10_awqos   = m7_awqos;
        s10_awvalid = m7_awvalid & m7_slave_select[10];
        s10_wdata   = m7_wdata;
        s10_wstrb   = m7_wstrb;
        s10_wlast   = m7_wlast;
        s10_wvalid  = m7_wvalid;
        s10_bready  = m7_bready;
        s10_arid    = m7_arid;
        s10_araddr  = m7_araddr;
        s10_arlen   = m7_arlen;
        s10_arsize  = m7_arsize;
        s10_arburst = m7_arburst;
        s10_arlock  = m7_arlock;
        s10_arcache = m7_arcache;
        s10_arprot  = m7_arprot;
        s10_arqos   = m7_arqos;
        s10_arvalid = m7_arvalid & m7_slave_select[10];
        s10_rready  = m7_rready;
    end
 else if (m8_slave_select[10]) begin
        s10_awid    = m8_awid;
        s10_awaddr  = m8_awaddr;
        s10_awlen   = m8_awlen;
        s10_awsize  = m8_awsize;
        s10_awburst = m8_awburst;
        s10_awlock  = m8_awlock;
        s10_awcache = m8_awcache;
        s10_awprot  = m8_awprot;
        s10_awqos   = m8_awqos;
        s10_awvalid = m8_awvalid & m8_slave_select[10];
        s10_wdata   = m8_wdata;
        s10_wstrb   = m8_wstrb;
        s10_wlast   = m8_wlast;
        s10_wvalid  = m8_wvalid;
        s10_bready  = m8_bready;
        s10_arid    = m8_arid;
        s10_araddr  = m8_araddr;
        s10_arlen   = m8_arlen;
        s10_arsize  = m8_arsize;
        s10_arburst = m8_arburst;
        s10_arlock  = m8_arlock;
        s10_arcache = m8_arcache;
        s10_arprot  = m8_arprot;
        s10_arqos   = m8_arqos;
        s10_arvalid = m8_arvalid & m8_slave_select[10];
        s10_rready  = m8_rready;
    end
 else if (m9_slave_select[10]) begin
        s10_awid    = m9_awid;
        s10_awaddr  = m9_awaddr;
        s10_awlen   = m9_awlen;
        s10_awsize  = m9_awsize;
        s10_awburst = m9_awburst;
        s10_awlock  = m9_awlock;
        s10_awcache = m9_awcache;
        s10_awprot  = m9_awprot;
        s10_awqos   = m9_awqos;
        s10_awvalid = m9_awvalid & m9_slave_select[10];
        s10_wdata   = m9_wdata;
        s10_wstrb   = m9_wstrb;
        s10_wlast   = m9_wlast;
        s10_wvalid  = m9_wvalid;
        s10_bready  = m9_bready;
        s10_arid    = m9_arid;
        s10_araddr  = m9_araddr;
        s10_arlen   = m9_arlen;
        s10_arsize  = m9_arsize;
        s10_arburst = m9_arburst;
        s10_arlock  = m9_arlock;
        s10_arcache = m9_arcache;
        s10_arprot  = m9_arprot;
        s10_arqos   = m9_arqos;
        s10_arvalid = m9_arvalid & m9_slave_select[10];
        s10_rready  = m9_rready;
    end
 else if (m10_slave_select[10]) begin
        s10_awid    = m10_awid;
        s10_awaddr  = m10_awaddr;
        s10_awlen   = m10_awlen;
        s10_awsize  = m10_awsize;
        s10_awburst = m10_awburst;
        s10_awlock  = m10_awlock;
        s10_awcache = m10_awcache;
        s10_awprot  = m10_awprot;
        s10_awqos   = m10_awqos;
        s10_awvalid = m10_awvalid & m10_slave_select[10];
        s10_wdata   = m10_wdata;
        s10_wstrb   = m10_wstrb;
        s10_wlast   = m10_wlast;
        s10_wvalid  = m10_wvalid;
        s10_bready  = m10_bready;
        s10_arid    = m10_arid;
        s10_araddr  = m10_araddr;
        s10_arlen   = m10_arlen;
        s10_arsize  = m10_arsize;
        s10_arburst = m10_arburst;
        s10_arlock  = m10_arlock;
        s10_arcache = m10_arcache;
        s10_arprot  = m10_arprot;
        s10_arqos   = m10_arqos;
        s10_arvalid = m10_arvalid & m10_slave_select[10];
        s10_rready  = m10_rready;
    end
 else if (m11_slave_select[10]) begin
        s10_awid    = m11_awid;
        s10_awaddr  = m11_awaddr;
        s10_awlen   = m11_awlen;
        s10_awsize  = m11_awsize;
        s10_awburst = m11_awburst;
        s10_awlock  = m11_awlock;
        s10_awcache = m11_awcache;
        s10_awprot  = m11_awprot;
        s10_awqos   = m11_awqos;
        s10_awvalid = m11_awvalid & m11_slave_select[10];
        s10_wdata   = m11_wdata;
        s10_wstrb   = m11_wstrb;
        s10_wlast   = m11_wlast;
        s10_wvalid  = m11_wvalid;
        s10_bready  = m11_bready;
        s10_arid    = m11_arid;
        s10_araddr  = m11_araddr;
        s10_arlen   = m11_arlen;
        s10_arsize  = m11_arsize;
        s10_arburst = m11_arburst;
        s10_arlock  = m11_arlock;
        s10_arcache = m11_arcache;
        s10_arprot  = m11_arprot;
        s10_arqos   = m11_arqos;
        s10_arvalid = m11_arvalid & m11_slave_select[10];
        s10_rready  = m11_rready;
    end
 else if (m12_slave_select[10]) begin
        s10_awid    = m12_awid;
        s10_awaddr  = m12_awaddr;
        s10_awlen   = m12_awlen;
        s10_awsize  = m12_awsize;
        s10_awburst = m12_awburst;
        s10_awlock  = m12_awlock;
        s10_awcache = m12_awcache;
        s10_awprot  = m12_awprot;
        s10_awqos   = m12_awqos;
        s10_awvalid = m12_awvalid & m12_slave_select[10];
        s10_wdata   = m12_wdata;
        s10_wstrb   = m12_wstrb;
        s10_wlast   = m12_wlast;
        s10_wvalid  = m12_wvalid;
        s10_bready  = m12_bready;
        s10_arid    = m12_arid;
        s10_araddr  = m12_araddr;
        s10_arlen   = m12_arlen;
        s10_arsize  = m12_arsize;
        s10_arburst = m12_arburst;
        s10_arlock  = m12_arlock;
        s10_arcache = m12_arcache;
        s10_arprot  = m12_arprot;
        s10_arqos   = m12_arqos;
        s10_arvalid = m12_arvalid & m12_slave_select[10];
        s10_rready  = m12_rready;
    end
 else if (m13_slave_select[10]) begin
        s10_awid    = m13_awid;
        s10_awaddr  = m13_awaddr;
        s10_awlen   = m13_awlen;
        s10_awsize  = m13_awsize;
        s10_awburst = m13_awburst;
        s10_awlock  = m13_awlock;
        s10_awcache = m13_awcache;
        s10_awprot  = m13_awprot;
        s10_awqos   = m13_awqos;
        s10_awvalid = m13_awvalid & m13_slave_select[10];
        s10_wdata   = m13_wdata;
        s10_wstrb   = m13_wstrb;
        s10_wlast   = m13_wlast;
        s10_wvalid  = m13_wvalid;
        s10_bready  = m13_bready;
        s10_arid    = m13_arid;
        s10_araddr  = m13_araddr;
        s10_arlen   = m13_arlen;
        s10_arsize  = m13_arsize;
        s10_arburst = m13_arburst;
        s10_arlock  = m13_arlock;
        s10_arcache = m13_arcache;
        s10_arprot  = m13_arprot;
        s10_arqos   = m13_arqos;
        s10_arvalid = m13_arvalid & m13_slave_select[10];
        s10_rready  = m13_rready;
    end
 else if (m14_slave_select[10]) begin
        s10_awid    = m14_awid;
        s10_awaddr  = m14_awaddr;
        s10_awlen   = m14_awlen;
        s10_awsize  = m14_awsize;
        s10_awburst = m14_awburst;
        s10_awlock  = m14_awlock;
        s10_awcache = m14_awcache;
        s10_awprot  = m14_awprot;
        s10_awqos   = m14_awqos;
        s10_awvalid = m14_awvalid & m14_slave_select[10];
        s10_wdata   = m14_wdata;
        s10_wstrb   = m14_wstrb;
        s10_wlast   = m14_wlast;
        s10_wvalid  = m14_wvalid;
        s10_bready  = m14_bready;
        s10_arid    = m14_arid;
        s10_araddr  = m14_araddr;
        s10_arlen   = m14_arlen;
        s10_arsize  = m14_arsize;
        s10_arburst = m14_arburst;
        s10_arlock  = m14_arlock;
        s10_arcache = m14_arcache;
        s10_arprot  = m14_arprot;
        s10_arqos   = m14_arqos;
        s10_arvalid = m14_arvalid & m14_slave_select[10];
        s10_rready  = m14_rready;
    end

end


// Slave 11 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s11_awid    = 'b0;
    s11_awaddr  = 'b0;
    s11_awlen   = 'b0;
    s11_awsize  = 'b0;
    s11_awburst = 'b0;
    s11_awlock  = 'b0;
    s11_awcache = 'b0;
    s11_awprot  = 'b0;
    s11_awqos   = 'b0;
    s11_awvalid = 'b0;
    s11_wdata   = 'b0;
    s11_wstrb   = 'b0;
    s11_wlast   = 'b0;
    s11_wvalid  = 'b0;
    s11_bready  = 'b0;
    s11_arid    = 'b0;
    s11_araddr  = 'b0;
    s11_arlen   = 'b0;
    s11_arsize  = 'b0;
    s11_arburst = 'b0;
    s11_arlock  = 'b0;
    s11_arcache = 'b0;
    s11_arprot  = 'b0;
    s11_arqos   = 'b0;
    s11_arvalid = 'b0;
    s11_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[11]) begin
        s11_awid    = m0_awid;
        s11_awaddr  = m0_awaddr;
        s11_awlen   = m0_awlen;
        s11_awsize  = m0_awsize;
        s11_awburst = m0_awburst;
        s11_awlock  = m0_awlock;
        s11_awcache = m0_awcache;
        s11_awprot  = m0_awprot;
        s11_awqos   = m0_awqos;
        s11_awvalid = m0_awvalid & m0_slave_select[11];
        s11_wdata   = m0_wdata;
        s11_wstrb   = m0_wstrb;
        s11_wlast   = m0_wlast;
        s11_wvalid  = m0_wvalid;
        s11_bready  = m0_bready;
        s11_arid    = m0_arid;
        s11_araddr  = m0_araddr;
        s11_arlen   = m0_arlen;
        s11_arsize  = m0_arsize;
        s11_arburst = m0_arburst;
        s11_arlock  = m0_arlock;
        s11_arcache = m0_arcache;
        s11_arprot  = m0_arprot;
        s11_arqos   = m0_arqos;
        s11_arvalid = m0_arvalid & m0_slave_select[11];
        s11_rready  = m0_rready;
    end
 else if (m1_slave_select[11]) begin
        s11_awid    = m1_awid;
        s11_awaddr  = m1_awaddr;
        s11_awlen   = m1_awlen;
        s11_awsize  = m1_awsize;
        s11_awburst = m1_awburst;
        s11_awlock  = m1_awlock;
        s11_awcache = m1_awcache;
        s11_awprot  = m1_awprot;
        s11_awqos   = m1_awqos;
        s11_awvalid = m1_awvalid & m1_slave_select[11];
        s11_wdata   = m1_wdata;
        s11_wstrb   = m1_wstrb;
        s11_wlast   = m1_wlast;
        s11_wvalid  = m1_wvalid;
        s11_bready  = m1_bready;
        s11_arid    = m1_arid;
        s11_araddr  = m1_araddr;
        s11_arlen   = m1_arlen;
        s11_arsize  = m1_arsize;
        s11_arburst = m1_arburst;
        s11_arlock  = m1_arlock;
        s11_arcache = m1_arcache;
        s11_arprot  = m1_arprot;
        s11_arqos   = m1_arqos;
        s11_arvalid = m1_arvalid & m1_slave_select[11];
        s11_rready  = m1_rready;
    end
 else if (m2_slave_select[11]) begin
        s11_awid    = m2_awid;
        s11_awaddr  = m2_awaddr;
        s11_awlen   = m2_awlen;
        s11_awsize  = m2_awsize;
        s11_awburst = m2_awburst;
        s11_awlock  = m2_awlock;
        s11_awcache = m2_awcache;
        s11_awprot  = m2_awprot;
        s11_awqos   = m2_awqos;
        s11_awvalid = m2_awvalid & m2_slave_select[11];
        s11_wdata   = m2_wdata;
        s11_wstrb   = m2_wstrb;
        s11_wlast   = m2_wlast;
        s11_wvalid  = m2_wvalid;
        s11_bready  = m2_bready;
        s11_arid    = m2_arid;
        s11_araddr  = m2_araddr;
        s11_arlen   = m2_arlen;
        s11_arsize  = m2_arsize;
        s11_arburst = m2_arburst;
        s11_arlock  = m2_arlock;
        s11_arcache = m2_arcache;
        s11_arprot  = m2_arprot;
        s11_arqos   = m2_arqos;
        s11_arvalid = m2_arvalid & m2_slave_select[11];
        s11_rready  = m2_rready;
    end
 else if (m3_slave_select[11]) begin
        s11_awid    = m3_awid;
        s11_awaddr  = m3_awaddr;
        s11_awlen   = m3_awlen;
        s11_awsize  = m3_awsize;
        s11_awburst = m3_awburst;
        s11_awlock  = m3_awlock;
        s11_awcache = m3_awcache;
        s11_awprot  = m3_awprot;
        s11_awqos   = m3_awqos;
        s11_awvalid = m3_awvalid & m3_slave_select[11];
        s11_wdata   = m3_wdata;
        s11_wstrb   = m3_wstrb;
        s11_wlast   = m3_wlast;
        s11_wvalid  = m3_wvalid;
        s11_bready  = m3_bready;
        s11_arid    = m3_arid;
        s11_araddr  = m3_araddr;
        s11_arlen   = m3_arlen;
        s11_arsize  = m3_arsize;
        s11_arburst = m3_arburst;
        s11_arlock  = m3_arlock;
        s11_arcache = m3_arcache;
        s11_arprot  = m3_arprot;
        s11_arqos   = m3_arqos;
        s11_arvalid = m3_arvalid & m3_slave_select[11];
        s11_rready  = m3_rready;
    end
 else if (m4_slave_select[11]) begin
        s11_awid    = m4_awid;
        s11_awaddr  = m4_awaddr;
        s11_awlen   = m4_awlen;
        s11_awsize  = m4_awsize;
        s11_awburst = m4_awburst;
        s11_awlock  = m4_awlock;
        s11_awcache = m4_awcache;
        s11_awprot  = m4_awprot;
        s11_awqos   = m4_awqos;
        s11_awvalid = m4_awvalid & m4_slave_select[11];
        s11_wdata   = m4_wdata;
        s11_wstrb   = m4_wstrb;
        s11_wlast   = m4_wlast;
        s11_wvalid  = m4_wvalid;
        s11_bready  = m4_bready;
        s11_arid    = m4_arid;
        s11_araddr  = m4_araddr;
        s11_arlen   = m4_arlen;
        s11_arsize  = m4_arsize;
        s11_arburst = m4_arburst;
        s11_arlock  = m4_arlock;
        s11_arcache = m4_arcache;
        s11_arprot  = m4_arprot;
        s11_arqos   = m4_arqos;
        s11_arvalid = m4_arvalid & m4_slave_select[11];
        s11_rready  = m4_rready;
    end
 else if (m5_slave_select[11]) begin
        s11_awid    = m5_awid;
        s11_awaddr  = m5_awaddr;
        s11_awlen   = m5_awlen;
        s11_awsize  = m5_awsize;
        s11_awburst = m5_awburst;
        s11_awlock  = m5_awlock;
        s11_awcache = m5_awcache;
        s11_awprot  = m5_awprot;
        s11_awqos   = m5_awqos;
        s11_awvalid = m5_awvalid & m5_slave_select[11];
        s11_wdata   = m5_wdata;
        s11_wstrb   = m5_wstrb;
        s11_wlast   = m5_wlast;
        s11_wvalid  = m5_wvalid;
        s11_bready  = m5_bready;
        s11_arid    = m5_arid;
        s11_araddr  = m5_araddr;
        s11_arlen   = m5_arlen;
        s11_arsize  = m5_arsize;
        s11_arburst = m5_arburst;
        s11_arlock  = m5_arlock;
        s11_arcache = m5_arcache;
        s11_arprot  = m5_arprot;
        s11_arqos   = m5_arqos;
        s11_arvalid = m5_arvalid & m5_slave_select[11];
        s11_rready  = m5_rready;
    end
 else if (m6_slave_select[11]) begin
        s11_awid    = m6_awid;
        s11_awaddr  = m6_awaddr;
        s11_awlen   = m6_awlen;
        s11_awsize  = m6_awsize;
        s11_awburst = m6_awburst;
        s11_awlock  = m6_awlock;
        s11_awcache = m6_awcache;
        s11_awprot  = m6_awprot;
        s11_awqos   = m6_awqos;
        s11_awvalid = m6_awvalid & m6_slave_select[11];
        s11_wdata   = m6_wdata;
        s11_wstrb   = m6_wstrb;
        s11_wlast   = m6_wlast;
        s11_wvalid  = m6_wvalid;
        s11_bready  = m6_bready;
        s11_arid    = m6_arid;
        s11_araddr  = m6_araddr;
        s11_arlen   = m6_arlen;
        s11_arsize  = m6_arsize;
        s11_arburst = m6_arburst;
        s11_arlock  = m6_arlock;
        s11_arcache = m6_arcache;
        s11_arprot  = m6_arprot;
        s11_arqos   = m6_arqos;
        s11_arvalid = m6_arvalid & m6_slave_select[11];
        s11_rready  = m6_rready;
    end
 else if (m7_slave_select[11]) begin
        s11_awid    = m7_awid;
        s11_awaddr  = m7_awaddr;
        s11_awlen   = m7_awlen;
        s11_awsize  = m7_awsize;
        s11_awburst = m7_awburst;
        s11_awlock  = m7_awlock;
        s11_awcache = m7_awcache;
        s11_awprot  = m7_awprot;
        s11_awqos   = m7_awqos;
        s11_awvalid = m7_awvalid & m7_slave_select[11];
        s11_wdata   = m7_wdata;
        s11_wstrb   = m7_wstrb;
        s11_wlast   = m7_wlast;
        s11_wvalid  = m7_wvalid;
        s11_bready  = m7_bready;
        s11_arid    = m7_arid;
        s11_araddr  = m7_araddr;
        s11_arlen   = m7_arlen;
        s11_arsize  = m7_arsize;
        s11_arburst = m7_arburst;
        s11_arlock  = m7_arlock;
        s11_arcache = m7_arcache;
        s11_arprot  = m7_arprot;
        s11_arqos   = m7_arqos;
        s11_arvalid = m7_arvalid & m7_slave_select[11];
        s11_rready  = m7_rready;
    end
 else if (m8_slave_select[11]) begin
        s11_awid    = m8_awid;
        s11_awaddr  = m8_awaddr;
        s11_awlen   = m8_awlen;
        s11_awsize  = m8_awsize;
        s11_awburst = m8_awburst;
        s11_awlock  = m8_awlock;
        s11_awcache = m8_awcache;
        s11_awprot  = m8_awprot;
        s11_awqos   = m8_awqos;
        s11_awvalid = m8_awvalid & m8_slave_select[11];
        s11_wdata   = m8_wdata;
        s11_wstrb   = m8_wstrb;
        s11_wlast   = m8_wlast;
        s11_wvalid  = m8_wvalid;
        s11_bready  = m8_bready;
        s11_arid    = m8_arid;
        s11_araddr  = m8_araddr;
        s11_arlen   = m8_arlen;
        s11_arsize  = m8_arsize;
        s11_arburst = m8_arburst;
        s11_arlock  = m8_arlock;
        s11_arcache = m8_arcache;
        s11_arprot  = m8_arprot;
        s11_arqos   = m8_arqos;
        s11_arvalid = m8_arvalid & m8_slave_select[11];
        s11_rready  = m8_rready;
    end
 else if (m9_slave_select[11]) begin
        s11_awid    = m9_awid;
        s11_awaddr  = m9_awaddr;
        s11_awlen   = m9_awlen;
        s11_awsize  = m9_awsize;
        s11_awburst = m9_awburst;
        s11_awlock  = m9_awlock;
        s11_awcache = m9_awcache;
        s11_awprot  = m9_awprot;
        s11_awqos   = m9_awqos;
        s11_awvalid = m9_awvalid & m9_slave_select[11];
        s11_wdata   = m9_wdata;
        s11_wstrb   = m9_wstrb;
        s11_wlast   = m9_wlast;
        s11_wvalid  = m9_wvalid;
        s11_bready  = m9_bready;
        s11_arid    = m9_arid;
        s11_araddr  = m9_araddr;
        s11_arlen   = m9_arlen;
        s11_arsize  = m9_arsize;
        s11_arburst = m9_arburst;
        s11_arlock  = m9_arlock;
        s11_arcache = m9_arcache;
        s11_arprot  = m9_arprot;
        s11_arqos   = m9_arqos;
        s11_arvalid = m9_arvalid & m9_slave_select[11];
        s11_rready  = m9_rready;
    end
 else if (m10_slave_select[11]) begin
        s11_awid    = m10_awid;
        s11_awaddr  = m10_awaddr;
        s11_awlen   = m10_awlen;
        s11_awsize  = m10_awsize;
        s11_awburst = m10_awburst;
        s11_awlock  = m10_awlock;
        s11_awcache = m10_awcache;
        s11_awprot  = m10_awprot;
        s11_awqos   = m10_awqos;
        s11_awvalid = m10_awvalid & m10_slave_select[11];
        s11_wdata   = m10_wdata;
        s11_wstrb   = m10_wstrb;
        s11_wlast   = m10_wlast;
        s11_wvalid  = m10_wvalid;
        s11_bready  = m10_bready;
        s11_arid    = m10_arid;
        s11_araddr  = m10_araddr;
        s11_arlen   = m10_arlen;
        s11_arsize  = m10_arsize;
        s11_arburst = m10_arburst;
        s11_arlock  = m10_arlock;
        s11_arcache = m10_arcache;
        s11_arprot  = m10_arprot;
        s11_arqos   = m10_arqos;
        s11_arvalid = m10_arvalid & m10_slave_select[11];
        s11_rready  = m10_rready;
    end
 else if (m11_slave_select[11]) begin
        s11_awid    = m11_awid;
        s11_awaddr  = m11_awaddr;
        s11_awlen   = m11_awlen;
        s11_awsize  = m11_awsize;
        s11_awburst = m11_awburst;
        s11_awlock  = m11_awlock;
        s11_awcache = m11_awcache;
        s11_awprot  = m11_awprot;
        s11_awqos   = m11_awqos;
        s11_awvalid = m11_awvalid & m11_slave_select[11];
        s11_wdata   = m11_wdata;
        s11_wstrb   = m11_wstrb;
        s11_wlast   = m11_wlast;
        s11_wvalid  = m11_wvalid;
        s11_bready  = m11_bready;
        s11_arid    = m11_arid;
        s11_araddr  = m11_araddr;
        s11_arlen   = m11_arlen;
        s11_arsize  = m11_arsize;
        s11_arburst = m11_arburst;
        s11_arlock  = m11_arlock;
        s11_arcache = m11_arcache;
        s11_arprot  = m11_arprot;
        s11_arqos   = m11_arqos;
        s11_arvalid = m11_arvalid & m11_slave_select[11];
        s11_rready  = m11_rready;
    end
 else if (m12_slave_select[11]) begin
        s11_awid    = m12_awid;
        s11_awaddr  = m12_awaddr;
        s11_awlen   = m12_awlen;
        s11_awsize  = m12_awsize;
        s11_awburst = m12_awburst;
        s11_awlock  = m12_awlock;
        s11_awcache = m12_awcache;
        s11_awprot  = m12_awprot;
        s11_awqos   = m12_awqos;
        s11_awvalid = m12_awvalid & m12_slave_select[11];
        s11_wdata   = m12_wdata;
        s11_wstrb   = m12_wstrb;
        s11_wlast   = m12_wlast;
        s11_wvalid  = m12_wvalid;
        s11_bready  = m12_bready;
        s11_arid    = m12_arid;
        s11_araddr  = m12_araddr;
        s11_arlen   = m12_arlen;
        s11_arsize  = m12_arsize;
        s11_arburst = m12_arburst;
        s11_arlock  = m12_arlock;
        s11_arcache = m12_arcache;
        s11_arprot  = m12_arprot;
        s11_arqos   = m12_arqos;
        s11_arvalid = m12_arvalid & m12_slave_select[11];
        s11_rready  = m12_rready;
    end
 else if (m13_slave_select[11]) begin
        s11_awid    = m13_awid;
        s11_awaddr  = m13_awaddr;
        s11_awlen   = m13_awlen;
        s11_awsize  = m13_awsize;
        s11_awburst = m13_awburst;
        s11_awlock  = m13_awlock;
        s11_awcache = m13_awcache;
        s11_awprot  = m13_awprot;
        s11_awqos   = m13_awqos;
        s11_awvalid = m13_awvalid & m13_slave_select[11];
        s11_wdata   = m13_wdata;
        s11_wstrb   = m13_wstrb;
        s11_wlast   = m13_wlast;
        s11_wvalid  = m13_wvalid;
        s11_bready  = m13_bready;
        s11_arid    = m13_arid;
        s11_araddr  = m13_araddr;
        s11_arlen   = m13_arlen;
        s11_arsize  = m13_arsize;
        s11_arburst = m13_arburst;
        s11_arlock  = m13_arlock;
        s11_arcache = m13_arcache;
        s11_arprot  = m13_arprot;
        s11_arqos   = m13_arqos;
        s11_arvalid = m13_arvalid & m13_slave_select[11];
        s11_rready  = m13_rready;
    end
 else if (m14_slave_select[11]) begin
        s11_awid    = m14_awid;
        s11_awaddr  = m14_awaddr;
        s11_awlen   = m14_awlen;
        s11_awsize  = m14_awsize;
        s11_awburst = m14_awburst;
        s11_awlock  = m14_awlock;
        s11_awcache = m14_awcache;
        s11_awprot  = m14_awprot;
        s11_awqos   = m14_awqos;
        s11_awvalid = m14_awvalid & m14_slave_select[11];
        s11_wdata   = m14_wdata;
        s11_wstrb   = m14_wstrb;
        s11_wlast   = m14_wlast;
        s11_wvalid  = m14_wvalid;
        s11_bready  = m14_bready;
        s11_arid    = m14_arid;
        s11_araddr  = m14_araddr;
        s11_arlen   = m14_arlen;
        s11_arsize  = m14_arsize;
        s11_arburst = m14_arburst;
        s11_arlock  = m14_arlock;
        s11_arcache = m14_arcache;
        s11_arprot  = m14_arprot;
        s11_arqos   = m14_arqos;
        s11_arvalid = m14_arvalid & m14_slave_select[11];
        s11_rready  = m14_rready;
    end

end


// Slave 12 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s12_awid    = 'b0;
    s12_awaddr  = 'b0;
    s12_awlen   = 'b0;
    s12_awsize  = 'b0;
    s12_awburst = 'b0;
    s12_awlock  = 'b0;
    s12_awcache = 'b0;
    s12_awprot  = 'b0;
    s12_awqos   = 'b0;
    s12_awvalid = 'b0;
    s12_wdata   = 'b0;
    s12_wstrb   = 'b0;
    s12_wlast   = 'b0;
    s12_wvalid  = 'b0;
    s12_bready  = 'b0;
    s12_arid    = 'b0;
    s12_araddr  = 'b0;
    s12_arlen   = 'b0;
    s12_arsize  = 'b0;
    s12_arburst = 'b0;
    s12_arlock  = 'b0;
    s12_arcache = 'b0;
    s12_arprot  = 'b0;
    s12_arqos   = 'b0;
    s12_arvalid = 'b0;
    s12_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[12]) begin
        s12_awid    = m0_awid;
        s12_awaddr  = m0_awaddr;
        s12_awlen   = m0_awlen;
        s12_awsize  = m0_awsize;
        s12_awburst = m0_awburst;
        s12_awlock  = m0_awlock;
        s12_awcache = m0_awcache;
        s12_awprot  = m0_awprot;
        s12_awqos   = m0_awqos;
        s12_awvalid = m0_awvalid & m0_slave_select[12];
        s12_wdata   = m0_wdata;
        s12_wstrb   = m0_wstrb;
        s12_wlast   = m0_wlast;
        s12_wvalid  = m0_wvalid;
        s12_bready  = m0_bready;
        s12_arid    = m0_arid;
        s12_araddr  = m0_araddr;
        s12_arlen   = m0_arlen;
        s12_arsize  = m0_arsize;
        s12_arburst = m0_arburst;
        s12_arlock  = m0_arlock;
        s12_arcache = m0_arcache;
        s12_arprot  = m0_arprot;
        s12_arqos   = m0_arqos;
        s12_arvalid = m0_arvalid & m0_slave_select[12];
        s12_rready  = m0_rready;
    end
 else if (m1_slave_select[12]) begin
        s12_awid    = m1_awid;
        s12_awaddr  = m1_awaddr;
        s12_awlen   = m1_awlen;
        s12_awsize  = m1_awsize;
        s12_awburst = m1_awburst;
        s12_awlock  = m1_awlock;
        s12_awcache = m1_awcache;
        s12_awprot  = m1_awprot;
        s12_awqos   = m1_awqos;
        s12_awvalid = m1_awvalid & m1_slave_select[12];
        s12_wdata   = m1_wdata;
        s12_wstrb   = m1_wstrb;
        s12_wlast   = m1_wlast;
        s12_wvalid  = m1_wvalid;
        s12_bready  = m1_bready;
        s12_arid    = m1_arid;
        s12_araddr  = m1_araddr;
        s12_arlen   = m1_arlen;
        s12_arsize  = m1_arsize;
        s12_arburst = m1_arburst;
        s12_arlock  = m1_arlock;
        s12_arcache = m1_arcache;
        s12_arprot  = m1_arprot;
        s12_arqos   = m1_arqos;
        s12_arvalid = m1_arvalid & m1_slave_select[12];
        s12_rready  = m1_rready;
    end
 else if (m2_slave_select[12]) begin
        s12_awid    = m2_awid;
        s12_awaddr  = m2_awaddr;
        s12_awlen   = m2_awlen;
        s12_awsize  = m2_awsize;
        s12_awburst = m2_awburst;
        s12_awlock  = m2_awlock;
        s12_awcache = m2_awcache;
        s12_awprot  = m2_awprot;
        s12_awqos   = m2_awqos;
        s12_awvalid = m2_awvalid & m2_slave_select[12];
        s12_wdata   = m2_wdata;
        s12_wstrb   = m2_wstrb;
        s12_wlast   = m2_wlast;
        s12_wvalid  = m2_wvalid;
        s12_bready  = m2_bready;
        s12_arid    = m2_arid;
        s12_araddr  = m2_araddr;
        s12_arlen   = m2_arlen;
        s12_arsize  = m2_arsize;
        s12_arburst = m2_arburst;
        s12_arlock  = m2_arlock;
        s12_arcache = m2_arcache;
        s12_arprot  = m2_arprot;
        s12_arqos   = m2_arqos;
        s12_arvalid = m2_arvalid & m2_slave_select[12];
        s12_rready  = m2_rready;
    end
 else if (m3_slave_select[12]) begin
        s12_awid    = m3_awid;
        s12_awaddr  = m3_awaddr;
        s12_awlen   = m3_awlen;
        s12_awsize  = m3_awsize;
        s12_awburst = m3_awburst;
        s12_awlock  = m3_awlock;
        s12_awcache = m3_awcache;
        s12_awprot  = m3_awprot;
        s12_awqos   = m3_awqos;
        s12_awvalid = m3_awvalid & m3_slave_select[12];
        s12_wdata   = m3_wdata;
        s12_wstrb   = m3_wstrb;
        s12_wlast   = m3_wlast;
        s12_wvalid  = m3_wvalid;
        s12_bready  = m3_bready;
        s12_arid    = m3_arid;
        s12_araddr  = m3_araddr;
        s12_arlen   = m3_arlen;
        s12_arsize  = m3_arsize;
        s12_arburst = m3_arburst;
        s12_arlock  = m3_arlock;
        s12_arcache = m3_arcache;
        s12_arprot  = m3_arprot;
        s12_arqos   = m3_arqos;
        s12_arvalid = m3_arvalid & m3_slave_select[12];
        s12_rready  = m3_rready;
    end
 else if (m4_slave_select[12]) begin
        s12_awid    = m4_awid;
        s12_awaddr  = m4_awaddr;
        s12_awlen   = m4_awlen;
        s12_awsize  = m4_awsize;
        s12_awburst = m4_awburst;
        s12_awlock  = m4_awlock;
        s12_awcache = m4_awcache;
        s12_awprot  = m4_awprot;
        s12_awqos   = m4_awqos;
        s12_awvalid = m4_awvalid & m4_slave_select[12];
        s12_wdata   = m4_wdata;
        s12_wstrb   = m4_wstrb;
        s12_wlast   = m4_wlast;
        s12_wvalid  = m4_wvalid;
        s12_bready  = m4_bready;
        s12_arid    = m4_arid;
        s12_araddr  = m4_araddr;
        s12_arlen   = m4_arlen;
        s12_arsize  = m4_arsize;
        s12_arburst = m4_arburst;
        s12_arlock  = m4_arlock;
        s12_arcache = m4_arcache;
        s12_arprot  = m4_arprot;
        s12_arqos   = m4_arqos;
        s12_arvalid = m4_arvalid & m4_slave_select[12];
        s12_rready  = m4_rready;
    end
 else if (m5_slave_select[12]) begin
        s12_awid    = m5_awid;
        s12_awaddr  = m5_awaddr;
        s12_awlen   = m5_awlen;
        s12_awsize  = m5_awsize;
        s12_awburst = m5_awburst;
        s12_awlock  = m5_awlock;
        s12_awcache = m5_awcache;
        s12_awprot  = m5_awprot;
        s12_awqos   = m5_awqos;
        s12_awvalid = m5_awvalid & m5_slave_select[12];
        s12_wdata   = m5_wdata;
        s12_wstrb   = m5_wstrb;
        s12_wlast   = m5_wlast;
        s12_wvalid  = m5_wvalid;
        s12_bready  = m5_bready;
        s12_arid    = m5_arid;
        s12_araddr  = m5_araddr;
        s12_arlen   = m5_arlen;
        s12_arsize  = m5_arsize;
        s12_arburst = m5_arburst;
        s12_arlock  = m5_arlock;
        s12_arcache = m5_arcache;
        s12_arprot  = m5_arprot;
        s12_arqos   = m5_arqos;
        s12_arvalid = m5_arvalid & m5_slave_select[12];
        s12_rready  = m5_rready;
    end
 else if (m6_slave_select[12]) begin
        s12_awid    = m6_awid;
        s12_awaddr  = m6_awaddr;
        s12_awlen   = m6_awlen;
        s12_awsize  = m6_awsize;
        s12_awburst = m6_awburst;
        s12_awlock  = m6_awlock;
        s12_awcache = m6_awcache;
        s12_awprot  = m6_awprot;
        s12_awqos   = m6_awqos;
        s12_awvalid = m6_awvalid & m6_slave_select[12];
        s12_wdata   = m6_wdata;
        s12_wstrb   = m6_wstrb;
        s12_wlast   = m6_wlast;
        s12_wvalid  = m6_wvalid;
        s12_bready  = m6_bready;
        s12_arid    = m6_arid;
        s12_araddr  = m6_araddr;
        s12_arlen   = m6_arlen;
        s12_arsize  = m6_arsize;
        s12_arburst = m6_arburst;
        s12_arlock  = m6_arlock;
        s12_arcache = m6_arcache;
        s12_arprot  = m6_arprot;
        s12_arqos   = m6_arqos;
        s12_arvalid = m6_arvalid & m6_slave_select[12];
        s12_rready  = m6_rready;
    end
 else if (m7_slave_select[12]) begin
        s12_awid    = m7_awid;
        s12_awaddr  = m7_awaddr;
        s12_awlen   = m7_awlen;
        s12_awsize  = m7_awsize;
        s12_awburst = m7_awburst;
        s12_awlock  = m7_awlock;
        s12_awcache = m7_awcache;
        s12_awprot  = m7_awprot;
        s12_awqos   = m7_awqos;
        s12_awvalid = m7_awvalid & m7_slave_select[12];
        s12_wdata   = m7_wdata;
        s12_wstrb   = m7_wstrb;
        s12_wlast   = m7_wlast;
        s12_wvalid  = m7_wvalid;
        s12_bready  = m7_bready;
        s12_arid    = m7_arid;
        s12_araddr  = m7_araddr;
        s12_arlen   = m7_arlen;
        s12_arsize  = m7_arsize;
        s12_arburst = m7_arburst;
        s12_arlock  = m7_arlock;
        s12_arcache = m7_arcache;
        s12_arprot  = m7_arprot;
        s12_arqos   = m7_arqos;
        s12_arvalid = m7_arvalid & m7_slave_select[12];
        s12_rready  = m7_rready;
    end
 else if (m8_slave_select[12]) begin
        s12_awid    = m8_awid;
        s12_awaddr  = m8_awaddr;
        s12_awlen   = m8_awlen;
        s12_awsize  = m8_awsize;
        s12_awburst = m8_awburst;
        s12_awlock  = m8_awlock;
        s12_awcache = m8_awcache;
        s12_awprot  = m8_awprot;
        s12_awqos   = m8_awqos;
        s12_awvalid = m8_awvalid & m8_slave_select[12];
        s12_wdata   = m8_wdata;
        s12_wstrb   = m8_wstrb;
        s12_wlast   = m8_wlast;
        s12_wvalid  = m8_wvalid;
        s12_bready  = m8_bready;
        s12_arid    = m8_arid;
        s12_araddr  = m8_araddr;
        s12_arlen   = m8_arlen;
        s12_arsize  = m8_arsize;
        s12_arburst = m8_arburst;
        s12_arlock  = m8_arlock;
        s12_arcache = m8_arcache;
        s12_arprot  = m8_arprot;
        s12_arqos   = m8_arqos;
        s12_arvalid = m8_arvalid & m8_slave_select[12];
        s12_rready  = m8_rready;
    end
 else if (m9_slave_select[12]) begin
        s12_awid    = m9_awid;
        s12_awaddr  = m9_awaddr;
        s12_awlen   = m9_awlen;
        s12_awsize  = m9_awsize;
        s12_awburst = m9_awburst;
        s12_awlock  = m9_awlock;
        s12_awcache = m9_awcache;
        s12_awprot  = m9_awprot;
        s12_awqos   = m9_awqos;
        s12_awvalid = m9_awvalid & m9_slave_select[12];
        s12_wdata   = m9_wdata;
        s12_wstrb   = m9_wstrb;
        s12_wlast   = m9_wlast;
        s12_wvalid  = m9_wvalid;
        s12_bready  = m9_bready;
        s12_arid    = m9_arid;
        s12_araddr  = m9_araddr;
        s12_arlen   = m9_arlen;
        s12_arsize  = m9_arsize;
        s12_arburst = m9_arburst;
        s12_arlock  = m9_arlock;
        s12_arcache = m9_arcache;
        s12_arprot  = m9_arprot;
        s12_arqos   = m9_arqos;
        s12_arvalid = m9_arvalid & m9_slave_select[12];
        s12_rready  = m9_rready;
    end
 else if (m10_slave_select[12]) begin
        s12_awid    = m10_awid;
        s12_awaddr  = m10_awaddr;
        s12_awlen   = m10_awlen;
        s12_awsize  = m10_awsize;
        s12_awburst = m10_awburst;
        s12_awlock  = m10_awlock;
        s12_awcache = m10_awcache;
        s12_awprot  = m10_awprot;
        s12_awqos   = m10_awqos;
        s12_awvalid = m10_awvalid & m10_slave_select[12];
        s12_wdata   = m10_wdata;
        s12_wstrb   = m10_wstrb;
        s12_wlast   = m10_wlast;
        s12_wvalid  = m10_wvalid;
        s12_bready  = m10_bready;
        s12_arid    = m10_arid;
        s12_araddr  = m10_araddr;
        s12_arlen   = m10_arlen;
        s12_arsize  = m10_arsize;
        s12_arburst = m10_arburst;
        s12_arlock  = m10_arlock;
        s12_arcache = m10_arcache;
        s12_arprot  = m10_arprot;
        s12_arqos   = m10_arqos;
        s12_arvalid = m10_arvalid & m10_slave_select[12];
        s12_rready  = m10_rready;
    end
 else if (m11_slave_select[12]) begin
        s12_awid    = m11_awid;
        s12_awaddr  = m11_awaddr;
        s12_awlen   = m11_awlen;
        s12_awsize  = m11_awsize;
        s12_awburst = m11_awburst;
        s12_awlock  = m11_awlock;
        s12_awcache = m11_awcache;
        s12_awprot  = m11_awprot;
        s12_awqos   = m11_awqos;
        s12_awvalid = m11_awvalid & m11_slave_select[12];
        s12_wdata   = m11_wdata;
        s12_wstrb   = m11_wstrb;
        s12_wlast   = m11_wlast;
        s12_wvalid  = m11_wvalid;
        s12_bready  = m11_bready;
        s12_arid    = m11_arid;
        s12_araddr  = m11_araddr;
        s12_arlen   = m11_arlen;
        s12_arsize  = m11_arsize;
        s12_arburst = m11_arburst;
        s12_arlock  = m11_arlock;
        s12_arcache = m11_arcache;
        s12_arprot  = m11_arprot;
        s12_arqos   = m11_arqos;
        s12_arvalid = m11_arvalid & m11_slave_select[12];
        s12_rready  = m11_rready;
    end
 else if (m12_slave_select[12]) begin
        s12_awid    = m12_awid;
        s12_awaddr  = m12_awaddr;
        s12_awlen   = m12_awlen;
        s12_awsize  = m12_awsize;
        s12_awburst = m12_awburst;
        s12_awlock  = m12_awlock;
        s12_awcache = m12_awcache;
        s12_awprot  = m12_awprot;
        s12_awqos   = m12_awqos;
        s12_awvalid = m12_awvalid & m12_slave_select[12];
        s12_wdata   = m12_wdata;
        s12_wstrb   = m12_wstrb;
        s12_wlast   = m12_wlast;
        s12_wvalid  = m12_wvalid;
        s12_bready  = m12_bready;
        s12_arid    = m12_arid;
        s12_araddr  = m12_araddr;
        s12_arlen   = m12_arlen;
        s12_arsize  = m12_arsize;
        s12_arburst = m12_arburst;
        s12_arlock  = m12_arlock;
        s12_arcache = m12_arcache;
        s12_arprot  = m12_arprot;
        s12_arqos   = m12_arqos;
        s12_arvalid = m12_arvalid & m12_slave_select[12];
        s12_rready  = m12_rready;
    end
 else if (m13_slave_select[12]) begin
        s12_awid    = m13_awid;
        s12_awaddr  = m13_awaddr;
        s12_awlen   = m13_awlen;
        s12_awsize  = m13_awsize;
        s12_awburst = m13_awburst;
        s12_awlock  = m13_awlock;
        s12_awcache = m13_awcache;
        s12_awprot  = m13_awprot;
        s12_awqos   = m13_awqos;
        s12_awvalid = m13_awvalid & m13_slave_select[12];
        s12_wdata   = m13_wdata;
        s12_wstrb   = m13_wstrb;
        s12_wlast   = m13_wlast;
        s12_wvalid  = m13_wvalid;
        s12_bready  = m13_bready;
        s12_arid    = m13_arid;
        s12_araddr  = m13_araddr;
        s12_arlen   = m13_arlen;
        s12_arsize  = m13_arsize;
        s12_arburst = m13_arburst;
        s12_arlock  = m13_arlock;
        s12_arcache = m13_arcache;
        s12_arprot  = m13_arprot;
        s12_arqos   = m13_arqos;
        s12_arvalid = m13_arvalid & m13_slave_select[12];
        s12_rready  = m13_rready;
    end
 else if (m14_slave_select[12]) begin
        s12_awid    = m14_awid;
        s12_awaddr  = m14_awaddr;
        s12_awlen   = m14_awlen;
        s12_awsize  = m14_awsize;
        s12_awburst = m14_awburst;
        s12_awlock  = m14_awlock;
        s12_awcache = m14_awcache;
        s12_awprot  = m14_awprot;
        s12_awqos   = m14_awqos;
        s12_awvalid = m14_awvalid & m14_slave_select[12];
        s12_wdata   = m14_wdata;
        s12_wstrb   = m14_wstrb;
        s12_wlast   = m14_wlast;
        s12_wvalid  = m14_wvalid;
        s12_bready  = m14_bready;
        s12_arid    = m14_arid;
        s12_araddr  = m14_araddr;
        s12_arlen   = m14_arlen;
        s12_arsize  = m14_arsize;
        s12_arburst = m14_arburst;
        s12_arlock  = m14_arlock;
        s12_arcache = m14_arcache;
        s12_arprot  = m14_arprot;
        s12_arqos   = m14_arqos;
        s12_arvalid = m14_arvalid & m14_slave_select[12];
        s12_rready  = m14_rready;
    end

end


// Slave 13 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s13_awid    = 'b0;
    s13_awaddr  = 'b0;
    s13_awlen   = 'b0;
    s13_awsize  = 'b0;
    s13_awburst = 'b0;
    s13_awlock  = 'b0;
    s13_awcache = 'b0;
    s13_awprot  = 'b0;
    s13_awqos   = 'b0;
    s13_awvalid = 'b0;
    s13_wdata   = 'b0;
    s13_wstrb   = 'b0;
    s13_wlast   = 'b0;
    s13_wvalid  = 'b0;
    s13_bready  = 'b0;
    s13_arid    = 'b0;
    s13_araddr  = 'b0;
    s13_arlen   = 'b0;
    s13_arsize  = 'b0;
    s13_arburst = 'b0;
    s13_arlock  = 'b0;
    s13_arcache = 'b0;
    s13_arprot  = 'b0;
    s13_arqos   = 'b0;
    s13_arvalid = 'b0;
    s13_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[13]) begin
        s13_awid    = m0_awid;
        s13_awaddr  = m0_awaddr;
        s13_awlen   = m0_awlen;
        s13_awsize  = m0_awsize;
        s13_awburst = m0_awburst;
        s13_awlock  = m0_awlock;
        s13_awcache = m0_awcache;
        s13_awprot  = m0_awprot;
        s13_awqos   = m0_awqos;
        s13_awvalid = m0_awvalid & m0_slave_select[13];
        s13_wdata   = m0_wdata;
        s13_wstrb   = m0_wstrb;
        s13_wlast   = m0_wlast;
        s13_wvalid  = m0_wvalid;
        s13_bready  = m0_bready;
        s13_arid    = m0_arid;
        s13_araddr  = m0_araddr;
        s13_arlen   = m0_arlen;
        s13_arsize  = m0_arsize;
        s13_arburst = m0_arburst;
        s13_arlock  = m0_arlock;
        s13_arcache = m0_arcache;
        s13_arprot  = m0_arprot;
        s13_arqos   = m0_arqos;
        s13_arvalid = m0_arvalid & m0_slave_select[13];
        s13_rready  = m0_rready;
    end
 else if (m1_slave_select[13]) begin
        s13_awid    = m1_awid;
        s13_awaddr  = m1_awaddr;
        s13_awlen   = m1_awlen;
        s13_awsize  = m1_awsize;
        s13_awburst = m1_awburst;
        s13_awlock  = m1_awlock;
        s13_awcache = m1_awcache;
        s13_awprot  = m1_awprot;
        s13_awqos   = m1_awqos;
        s13_awvalid = m1_awvalid & m1_slave_select[13];
        s13_wdata   = m1_wdata;
        s13_wstrb   = m1_wstrb;
        s13_wlast   = m1_wlast;
        s13_wvalid  = m1_wvalid;
        s13_bready  = m1_bready;
        s13_arid    = m1_arid;
        s13_araddr  = m1_araddr;
        s13_arlen   = m1_arlen;
        s13_arsize  = m1_arsize;
        s13_arburst = m1_arburst;
        s13_arlock  = m1_arlock;
        s13_arcache = m1_arcache;
        s13_arprot  = m1_arprot;
        s13_arqos   = m1_arqos;
        s13_arvalid = m1_arvalid & m1_slave_select[13];
        s13_rready  = m1_rready;
    end
 else if (m2_slave_select[13]) begin
        s13_awid    = m2_awid;
        s13_awaddr  = m2_awaddr;
        s13_awlen   = m2_awlen;
        s13_awsize  = m2_awsize;
        s13_awburst = m2_awburst;
        s13_awlock  = m2_awlock;
        s13_awcache = m2_awcache;
        s13_awprot  = m2_awprot;
        s13_awqos   = m2_awqos;
        s13_awvalid = m2_awvalid & m2_slave_select[13];
        s13_wdata   = m2_wdata;
        s13_wstrb   = m2_wstrb;
        s13_wlast   = m2_wlast;
        s13_wvalid  = m2_wvalid;
        s13_bready  = m2_bready;
        s13_arid    = m2_arid;
        s13_araddr  = m2_araddr;
        s13_arlen   = m2_arlen;
        s13_arsize  = m2_arsize;
        s13_arburst = m2_arburst;
        s13_arlock  = m2_arlock;
        s13_arcache = m2_arcache;
        s13_arprot  = m2_arprot;
        s13_arqos   = m2_arqos;
        s13_arvalid = m2_arvalid & m2_slave_select[13];
        s13_rready  = m2_rready;
    end
 else if (m3_slave_select[13]) begin
        s13_awid    = m3_awid;
        s13_awaddr  = m3_awaddr;
        s13_awlen   = m3_awlen;
        s13_awsize  = m3_awsize;
        s13_awburst = m3_awburst;
        s13_awlock  = m3_awlock;
        s13_awcache = m3_awcache;
        s13_awprot  = m3_awprot;
        s13_awqos   = m3_awqos;
        s13_awvalid = m3_awvalid & m3_slave_select[13];
        s13_wdata   = m3_wdata;
        s13_wstrb   = m3_wstrb;
        s13_wlast   = m3_wlast;
        s13_wvalid  = m3_wvalid;
        s13_bready  = m3_bready;
        s13_arid    = m3_arid;
        s13_araddr  = m3_araddr;
        s13_arlen   = m3_arlen;
        s13_arsize  = m3_arsize;
        s13_arburst = m3_arburst;
        s13_arlock  = m3_arlock;
        s13_arcache = m3_arcache;
        s13_arprot  = m3_arprot;
        s13_arqos   = m3_arqos;
        s13_arvalid = m3_arvalid & m3_slave_select[13];
        s13_rready  = m3_rready;
    end
 else if (m4_slave_select[13]) begin
        s13_awid    = m4_awid;
        s13_awaddr  = m4_awaddr;
        s13_awlen   = m4_awlen;
        s13_awsize  = m4_awsize;
        s13_awburst = m4_awburst;
        s13_awlock  = m4_awlock;
        s13_awcache = m4_awcache;
        s13_awprot  = m4_awprot;
        s13_awqos   = m4_awqos;
        s13_awvalid = m4_awvalid & m4_slave_select[13];
        s13_wdata   = m4_wdata;
        s13_wstrb   = m4_wstrb;
        s13_wlast   = m4_wlast;
        s13_wvalid  = m4_wvalid;
        s13_bready  = m4_bready;
        s13_arid    = m4_arid;
        s13_araddr  = m4_araddr;
        s13_arlen   = m4_arlen;
        s13_arsize  = m4_arsize;
        s13_arburst = m4_arburst;
        s13_arlock  = m4_arlock;
        s13_arcache = m4_arcache;
        s13_arprot  = m4_arprot;
        s13_arqos   = m4_arqos;
        s13_arvalid = m4_arvalid & m4_slave_select[13];
        s13_rready  = m4_rready;
    end
 else if (m5_slave_select[13]) begin
        s13_awid    = m5_awid;
        s13_awaddr  = m5_awaddr;
        s13_awlen   = m5_awlen;
        s13_awsize  = m5_awsize;
        s13_awburst = m5_awburst;
        s13_awlock  = m5_awlock;
        s13_awcache = m5_awcache;
        s13_awprot  = m5_awprot;
        s13_awqos   = m5_awqos;
        s13_awvalid = m5_awvalid & m5_slave_select[13];
        s13_wdata   = m5_wdata;
        s13_wstrb   = m5_wstrb;
        s13_wlast   = m5_wlast;
        s13_wvalid  = m5_wvalid;
        s13_bready  = m5_bready;
        s13_arid    = m5_arid;
        s13_araddr  = m5_araddr;
        s13_arlen   = m5_arlen;
        s13_arsize  = m5_arsize;
        s13_arburst = m5_arburst;
        s13_arlock  = m5_arlock;
        s13_arcache = m5_arcache;
        s13_arprot  = m5_arprot;
        s13_arqos   = m5_arqos;
        s13_arvalid = m5_arvalid & m5_slave_select[13];
        s13_rready  = m5_rready;
    end
 else if (m6_slave_select[13]) begin
        s13_awid    = m6_awid;
        s13_awaddr  = m6_awaddr;
        s13_awlen   = m6_awlen;
        s13_awsize  = m6_awsize;
        s13_awburst = m6_awburst;
        s13_awlock  = m6_awlock;
        s13_awcache = m6_awcache;
        s13_awprot  = m6_awprot;
        s13_awqos   = m6_awqos;
        s13_awvalid = m6_awvalid & m6_slave_select[13];
        s13_wdata   = m6_wdata;
        s13_wstrb   = m6_wstrb;
        s13_wlast   = m6_wlast;
        s13_wvalid  = m6_wvalid;
        s13_bready  = m6_bready;
        s13_arid    = m6_arid;
        s13_araddr  = m6_araddr;
        s13_arlen   = m6_arlen;
        s13_arsize  = m6_arsize;
        s13_arburst = m6_arburst;
        s13_arlock  = m6_arlock;
        s13_arcache = m6_arcache;
        s13_arprot  = m6_arprot;
        s13_arqos   = m6_arqos;
        s13_arvalid = m6_arvalid & m6_slave_select[13];
        s13_rready  = m6_rready;
    end
 else if (m7_slave_select[13]) begin
        s13_awid    = m7_awid;
        s13_awaddr  = m7_awaddr;
        s13_awlen   = m7_awlen;
        s13_awsize  = m7_awsize;
        s13_awburst = m7_awburst;
        s13_awlock  = m7_awlock;
        s13_awcache = m7_awcache;
        s13_awprot  = m7_awprot;
        s13_awqos   = m7_awqos;
        s13_awvalid = m7_awvalid & m7_slave_select[13];
        s13_wdata   = m7_wdata;
        s13_wstrb   = m7_wstrb;
        s13_wlast   = m7_wlast;
        s13_wvalid  = m7_wvalid;
        s13_bready  = m7_bready;
        s13_arid    = m7_arid;
        s13_araddr  = m7_araddr;
        s13_arlen   = m7_arlen;
        s13_arsize  = m7_arsize;
        s13_arburst = m7_arburst;
        s13_arlock  = m7_arlock;
        s13_arcache = m7_arcache;
        s13_arprot  = m7_arprot;
        s13_arqos   = m7_arqos;
        s13_arvalid = m7_arvalid & m7_slave_select[13];
        s13_rready  = m7_rready;
    end
 else if (m8_slave_select[13]) begin
        s13_awid    = m8_awid;
        s13_awaddr  = m8_awaddr;
        s13_awlen   = m8_awlen;
        s13_awsize  = m8_awsize;
        s13_awburst = m8_awburst;
        s13_awlock  = m8_awlock;
        s13_awcache = m8_awcache;
        s13_awprot  = m8_awprot;
        s13_awqos   = m8_awqos;
        s13_awvalid = m8_awvalid & m8_slave_select[13];
        s13_wdata   = m8_wdata;
        s13_wstrb   = m8_wstrb;
        s13_wlast   = m8_wlast;
        s13_wvalid  = m8_wvalid;
        s13_bready  = m8_bready;
        s13_arid    = m8_arid;
        s13_araddr  = m8_araddr;
        s13_arlen   = m8_arlen;
        s13_arsize  = m8_arsize;
        s13_arburst = m8_arburst;
        s13_arlock  = m8_arlock;
        s13_arcache = m8_arcache;
        s13_arprot  = m8_arprot;
        s13_arqos   = m8_arqos;
        s13_arvalid = m8_arvalid & m8_slave_select[13];
        s13_rready  = m8_rready;
    end
 else if (m9_slave_select[13]) begin
        s13_awid    = m9_awid;
        s13_awaddr  = m9_awaddr;
        s13_awlen   = m9_awlen;
        s13_awsize  = m9_awsize;
        s13_awburst = m9_awburst;
        s13_awlock  = m9_awlock;
        s13_awcache = m9_awcache;
        s13_awprot  = m9_awprot;
        s13_awqos   = m9_awqos;
        s13_awvalid = m9_awvalid & m9_slave_select[13];
        s13_wdata   = m9_wdata;
        s13_wstrb   = m9_wstrb;
        s13_wlast   = m9_wlast;
        s13_wvalid  = m9_wvalid;
        s13_bready  = m9_bready;
        s13_arid    = m9_arid;
        s13_araddr  = m9_araddr;
        s13_arlen   = m9_arlen;
        s13_arsize  = m9_arsize;
        s13_arburst = m9_arburst;
        s13_arlock  = m9_arlock;
        s13_arcache = m9_arcache;
        s13_arprot  = m9_arprot;
        s13_arqos   = m9_arqos;
        s13_arvalid = m9_arvalid & m9_slave_select[13];
        s13_rready  = m9_rready;
    end
 else if (m10_slave_select[13]) begin
        s13_awid    = m10_awid;
        s13_awaddr  = m10_awaddr;
        s13_awlen   = m10_awlen;
        s13_awsize  = m10_awsize;
        s13_awburst = m10_awburst;
        s13_awlock  = m10_awlock;
        s13_awcache = m10_awcache;
        s13_awprot  = m10_awprot;
        s13_awqos   = m10_awqos;
        s13_awvalid = m10_awvalid & m10_slave_select[13];
        s13_wdata   = m10_wdata;
        s13_wstrb   = m10_wstrb;
        s13_wlast   = m10_wlast;
        s13_wvalid  = m10_wvalid;
        s13_bready  = m10_bready;
        s13_arid    = m10_arid;
        s13_araddr  = m10_araddr;
        s13_arlen   = m10_arlen;
        s13_arsize  = m10_arsize;
        s13_arburst = m10_arburst;
        s13_arlock  = m10_arlock;
        s13_arcache = m10_arcache;
        s13_arprot  = m10_arprot;
        s13_arqos   = m10_arqos;
        s13_arvalid = m10_arvalid & m10_slave_select[13];
        s13_rready  = m10_rready;
    end
 else if (m11_slave_select[13]) begin
        s13_awid    = m11_awid;
        s13_awaddr  = m11_awaddr;
        s13_awlen   = m11_awlen;
        s13_awsize  = m11_awsize;
        s13_awburst = m11_awburst;
        s13_awlock  = m11_awlock;
        s13_awcache = m11_awcache;
        s13_awprot  = m11_awprot;
        s13_awqos   = m11_awqos;
        s13_awvalid = m11_awvalid & m11_slave_select[13];
        s13_wdata   = m11_wdata;
        s13_wstrb   = m11_wstrb;
        s13_wlast   = m11_wlast;
        s13_wvalid  = m11_wvalid;
        s13_bready  = m11_bready;
        s13_arid    = m11_arid;
        s13_araddr  = m11_araddr;
        s13_arlen   = m11_arlen;
        s13_arsize  = m11_arsize;
        s13_arburst = m11_arburst;
        s13_arlock  = m11_arlock;
        s13_arcache = m11_arcache;
        s13_arprot  = m11_arprot;
        s13_arqos   = m11_arqos;
        s13_arvalid = m11_arvalid & m11_slave_select[13];
        s13_rready  = m11_rready;
    end
 else if (m12_slave_select[13]) begin
        s13_awid    = m12_awid;
        s13_awaddr  = m12_awaddr;
        s13_awlen   = m12_awlen;
        s13_awsize  = m12_awsize;
        s13_awburst = m12_awburst;
        s13_awlock  = m12_awlock;
        s13_awcache = m12_awcache;
        s13_awprot  = m12_awprot;
        s13_awqos   = m12_awqos;
        s13_awvalid = m12_awvalid & m12_slave_select[13];
        s13_wdata   = m12_wdata;
        s13_wstrb   = m12_wstrb;
        s13_wlast   = m12_wlast;
        s13_wvalid  = m12_wvalid;
        s13_bready  = m12_bready;
        s13_arid    = m12_arid;
        s13_araddr  = m12_araddr;
        s13_arlen   = m12_arlen;
        s13_arsize  = m12_arsize;
        s13_arburst = m12_arburst;
        s13_arlock  = m12_arlock;
        s13_arcache = m12_arcache;
        s13_arprot  = m12_arprot;
        s13_arqos   = m12_arqos;
        s13_arvalid = m12_arvalid & m12_slave_select[13];
        s13_rready  = m12_rready;
    end
 else if (m13_slave_select[13]) begin
        s13_awid    = m13_awid;
        s13_awaddr  = m13_awaddr;
        s13_awlen   = m13_awlen;
        s13_awsize  = m13_awsize;
        s13_awburst = m13_awburst;
        s13_awlock  = m13_awlock;
        s13_awcache = m13_awcache;
        s13_awprot  = m13_awprot;
        s13_awqos   = m13_awqos;
        s13_awvalid = m13_awvalid & m13_slave_select[13];
        s13_wdata   = m13_wdata;
        s13_wstrb   = m13_wstrb;
        s13_wlast   = m13_wlast;
        s13_wvalid  = m13_wvalid;
        s13_bready  = m13_bready;
        s13_arid    = m13_arid;
        s13_araddr  = m13_araddr;
        s13_arlen   = m13_arlen;
        s13_arsize  = m13_arsize;
        s13_arburst = m13_arburst;
        s13_arlock  = m13_arlock;
        s13_arcache = m13_arcache;
        s13_arprot  = m13_arprot;
        s13_arqos   = m13_arqos;
        s13_arvalid = m13_arvalid & m13_slave_select[13];
        s13_rready  = m13_rready;
    end
 else if (m14_slave_select[13]) begin
        s13_awid    = m14_awid;
        s13_awaddr  = m14_awaddr;
        s13_awlen   = m14_awlen;
        s13_awsize  = m14_awsize;
        s13_awburst = m14_awburst;
        s13_awlock  = m14_awlock;
        s13_awcache = m14_awcache;
        s13_awprot  = m14_awprot;
        s13_awqos   = m14_awqos;
        s13_awvalid = m14_awvalid & m14_slave_select[13];
        s13_wdata   = m14_wdata;
        s13_wstrb   = m14_wstrb;
        s13_wlast   = m14_wlast;
        s13_wvalid  = m14_wvalid;
        s13_bready  = m14_bready;
        s13_arid    = m14_arid;
        s13_araddr  = m14_araddr;
        s13_arlen   = m14_arlen;
        s13_arsize  = m14_arsize;
        s13_arburst = m14_arburst;
        s13_arlock  = m14_arlock;
        s13_arcache = m14_arcache;
        s13_arprot  = m14_arprot;
        s13_arqos   = m14_arqos;
        s13_arvalid = m14_arvalid & m14_slave_select[13];
        s13_rready  = m14_rready;
    end

end


// Slave 14 connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s14_awid    = 'b0;
    s14_awaddr  = 'b0;
    s14_awlen   = 'b0;
    s14_awsize  = 'b0;
    s14_awburst = 'b0;
    s14_awlock  = 'b0;
    s14_awcache = 'b0;
    s14_awprot  = 'b0;
    s14_awqos   = 'b0;
    s14_awvalid = 'b0;
    s14_wdata   = 'b0;
    s14_wstrb   = 'b0;
    s14_wlast   = 'b0;
    s14_wvalid  = 'b0;
    s14_bready  = 'b0;
    s14_arid    = 'b0;
    s14_araddr  = 'b0;
    s14_arlen   = 'b0;
    s14_arsize  = 'b0;
    s14_arburst = 'b0;
    s14_arlock  = 'b0;
    s14_arcache = 'b0;
    s14_arprot  = 'b0;
    s14_arqos   = 'b0;
    s14_arvalid = 'b0;
    s14_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[14]) begin
        s14_awid    = m0_awid;
        s14_awaddr  = m0_awaddr;
        s14_awlen   = m0_awlen;
        s14_awsize  = m0_awsize;
        s14_awburst = m0_awburst;
        s14_awlock  = m0_awlock;
        s14_awcache = m0_awcache;
        s14_awprot  = m0_awprot;
        s14_awqos   = m0_awqos;
        s14_awvalid = m0_awvalid & m0_slave_select[14];
        s14_wdata   = m0_wdata;
        s14_wstrb   = m0_wstrb;
        s14_wlast   = m0_wlast;
        s14_wvalid  = m0_wvalid;
        s14_bready  = m0_bready;
        s14_arid    = m0_arid;
        s14_araddr  = m0_araddr;
        s14_arlen   = m0_arlen;
        s14_arsize  = m0_arsize;
        s14_arburst = m0_arburst;
        s14_arlock  = m0_arlock;
        s14_arcache = m0_arcache;
        s14_arprot  = m0_arprot;
        s14_arqos   = m0_arqos;
        s14_arvalid = m0_arvalid & m0_slave_select[14];
        s14_rready  = m0_rready;
    end
 else if (m1_slave_select[14]) begin
        s14_awid    = m1_awid;
        s14_awaddr  = m1_awaddr;
        s14_awlen   = m1_awlen;
        s14_awsize  = m1_awsize;
        s14_awburst = m1_awburst;
        s14_awlock  = m1_awlock;
        s14_awcache = m1_awcache;
        s14_awprot  = m1_awprot;
        s14_awqos   = m1_awqos;
        s14_awvalid = m1_awvalid & m1_slave_select[14];
        s14_wdata   = m1_wdata;
        s14_wstrb   = m1_wstrb;
        s14_wlast   = m1_wlast;
        s14_wvalid  = m1_wvalid;
        s14_bready  = m1_bready;
        s14_arid    = m1_arid;
        s14_araddr  = m1_araddr;
        s14_arlen   = m1_arlen;
        s14_arsize  = m1_arsize;
        s14_arburst = m1_arburst;
        s14_arlock  = m1_arlock;
        s14_arcache = m1_arcache;
        s14_arprot  = m1_arprot;
        s14_arqos   = m1_arqos;
        s14_arvalid = m1_arvalid & m1_slave_select[14];
        s14_rready  = m1_rready;
    end
 else if (m2_slave_select[14]) begin
        s14_awid    = m2_awid;
        s14_awaddr  = m2_awaddr;
        s14_awlen   = m2_awlen;
        s14_awsize  = m2_awsize;
        s14_awburst = m2_awburst;
        s14_awlock  = m2_awlock;
        s14_awcache = m2_awcache;
        s14_awprot  = m2_awprot;
        s14_awqos   = m2_awqos;
        s14_awvalid = m2_awvalid & m2_slave_select[14];
        s14_wdata   = m2_wdata;
        s14_wstrb   = m2_wstrb;
        s14_wlast   = m2_wlast;
        s14_wvalid  = m2_wvalid;
        s14_bready  = m2_bready;
        s14_arid    = m2_arid;
        s14_araddr  = m2_araddr;
        s14_arlen   = m2_arlen;
        s14_arsize  = m2_arsize;
        s14_arburst = m2_arburst;
        s14_arlock  = m2_arlock;
        s14_arcache = m2_arcache;
        s14_arprot  = m2_arprot;
        s14_arqos   = m2_arqos;
        s14_arvalid = m2_arvalid & m2_slave_select[14];
        s14_rready  = m2_rready;
    end
 else if (m3_slave_select[14]) begin
        s14_awid    = m3_awid;
        s14_awaddr  = m3_awaddr;
        s14_awlen   = m3_awlen;
        s14_awsize  = m3_awsize;
        s14_awburst = m3_awburst;
        s14_awlock  = m3_awlock;
        s14_awcache = m3_awcache;
        s14_awprot  = m3_awprot;
        s14_awqos   = m3_awqos;
        s14_awvalid = m3_awvalid & m3_slave_select[14];
        s14_wdata   = m3_wdata;
        s14_wstrb   = m3_wstrb;
        s14_wlast   = m3_wlast;
        s14_wvalid  = m3_wvalid;
        s14_bready  = m3_bready;
        s14_arid    = m3_arid;
        s14_araddr  = m3_araddr;
        s14_arlen   = m3_arlen;
        s14_arsize  = m3_arsize;
        s14_arburst = m3_arburst;
        s14_arlock  = m3_arlock;
        s14_arcache = m3_arcache;
        s14_arprot  = m3_arprot;
        s14_arqos   = m3_arqos;
        s14_arvalid = m3_arvalid & m3_slave_select[14];
        s14_rready  = m3_rready;
    end
 else if (m4_slave_select[14]) begin
        s14_awid    = m4_awid;
        s14_awaddr  = m4_awaddr;
        s14_awlen   = m4_awlen;
        s14_awsize  = m4_awsize;
        s14_awburst = m4_awburst;
        s14_awlock  = m4_awlock;
        s14_awcache = m4_awcache;
        s14_awprot  = m4_awprot;
        s14_awqos   = m4_awqos;
        s14_awvalid = m4_awvalid & m4_slave_select[14];
        s14_wdata   = m4_wdata;
        s14_wstrb   = m4_wstrb;
        s14_wlast   = m4_wlast;
        s14_wvalid  = m4_wvalid;
        s14_bready  = m4_bready;
        s14_arid    = m4_arid;
        s14_araddr  = m4_araddr;
        s14_arlen   = m4_arlen;
        s14_arsize  = m4_arsize;
        s14_arburst = m4_arburst;
        s14_arlock  = m4_arlock;
        s14_arcache = m4_arcache;
        s14_arprot  = m4_arprot;
        s14_arqos   = m4_arqos;
        s14_arvalid = m4_arvalid & m4_slave_select[14];
        s14_rready  = m4_rready;
    end
 else if (m5_slave_select[14]) begin
        s14_awid    = m5_awid;
        s14_awaddr  = m5_awaddr;
        s14_awlen   = m5_awlen;
        s14_awsize  = m5_awsize;
        s14_awburst = m5_awburst;
        s14_awlock  = m5_awlock;
        s14_awcache = m5_awcache;
        s14_awprot  = m5_awprot;
        s14_awqos   = m5_awqos;
        s14_awvalid = m5_awvalid & m5_slave_select[14];
        s14_wdata   = m5_wdata;
        s14_wstrb   = m5_wstrb;
        s14_wlast   = m5_wlast;
        s14_wvalid  = m5_wvalid;
        s14_bready  = m5_bready;
        s14_arid    = m5_arid;
        s14_araddr  = m5_araddr;
        s14_arlen   = m5_arlen;
        s14_arsize  = m5_arsize;
        s14_arburst = m5_arburst;
        s14_arlock  = m5_arlock;
        s14_arcache = m5_arcache;
        s14_arprot  = m5_arprot;
        s14_arqos   = m5_arqos;
        s14_arvalid = m5_arvalid & m5_slave_select[14];
        s14_rready  = m5_rready;
    end
 else if (m6_slave_select[14]) begin
        s14_awid    = m6_awid;
        s14_awaddr  = m6_awaddr;
        s14_awlen   = m6_awlen;
        s14_awsize  = m6_awsize;
        s14_awburst = m6_awburst;
        s14_awlock  = m6_awlock;
        s14_awcache = m6_awcache;
        s14_awprot  = m6_awprot;
        s14_awqos   = m6_awqos;
        s14_awvalid = m6_awvalid & m6_slave_select[14];
        s14_wdata   = m6_wdata;
        s14_wstrb   = m6_wstrb;
        s14_wlast   = m6_wlast;
        s14_wvalid  = m6_wvalid;
        s14_bready  = m6_bready;
        s14_arid    = m6_arid;
        s14_araddr  = m6_araddr;
        s14_arlen   = m6_arlen;
        s14_arsize  = m6_arsize;
        s14_arburst = m6_arburst;
        s14_arlock  = m6_arlock;
        s14_arcache = m6_arcache;
        s14_arprot  = m6_arprot;
        s14_arqos   = m6_arqos;
        s14_arvalid = m6_arvalid & m6_slave_select[14];
        s14_rready  = m6_rready;
    end
 else if (m7_slave_select[14]) begin
        s14_awid    = m7_awid;
        s14_awaddr  = m7_awaddr;
        s14_awlen   = m7_awlen;
        s14_awsize  = m7_awsize;
        s14_awburst = m7_awburst;
        s14_awlock  = m7_awlock;
        s14_awcache = m7_awcache;
        s14_awprot  = m7_awprot;
        s14_awqos   = m7_awqos;
        s14_awvalid = m7_awvalid & m7_slave_select[14];
        s14_wdata   = m7_wdata;
        s14_wstrb   = m7_wstrb;
        s14_wlast   = m7_wlast;
        s14_wvalid  = m7_wvalid;
        s14_bready  = m7_bready;
        s14_arid    = m7_arid;
        s14_araddr  = m7_araddr;
        s14_arlen   = m7_arlen;
        s14_arsize  = m7_arsize;
        s14_arburst = m7_arburst;
        s14_arlock  = m7_arlock;
        s14_arcache = m7_arcache;
        s14_arprot  = m7_arprot;
        s14_arqos   = m7_arqos;
        s14_arvalid = m7_arvalid & m7_slave_select[14];
        s14_rready  = m7_rready;
    end
 else if (m8_slave_select[14]) begin
        s14_awid    = m8_awid;
        s14_awaddr  = m8_awaddr;
        s14_awlen   = m8_awlen;
        s14_awsize  = m8_awsize;
        s14_awburst = m8_awburst;
        s14_awlock  = m8_awlock;
        s14_awcache = m8_awcache;
        s14_awprot  = m8_awprot;
        s14_awqos   = m8_awqos;
        s14_awvalid = m8_awvalid & m8_slave_select[14];
        s14_wdata   = m8_wdata;
        s14_wstrb   = m8_wstrb;
        s14_wlast   = m8_wlast;
        s14_wvalid  = m8_wvalid;
        s14_bready  = m8_bready;
        s14_arid    = m8_arid;
        s14_araddr  = m8_araddr;
        s14_arlen   = m8_arlen;
        s14_arsize  = m8_arsize;
        s14_arburst = m8_arburst;
        s14_arlock  = m8_arlock;
        s14_arcache = m8_arcache;
        s14_arprot  = m8_arprot;
        s14_arqos   = m8_arqos;
        s14_arvalid = m8_arvalid & m8_slave_select[14];
        s14_rready  = m8_rready;
    end
 else if (m9_slave_select[14]) begin
        s14_awid    = m9_awid;
        s14_awaddr  = m9_awaddr;
        s14_awlen   = m9_awlen;
        s14_awsize  = m9_awsize;
        s14_awburst = m9_awburst;
        s14_awlock  = m9_awlock;
        s14_awcache = m9_awcache;
        s14_awprot  = m9_awprot;
        s14_awqos   = m9_awqos;
        s14_awvalid = m9_awvalid & m9_slave_select[14];
        s14_wdata   = m9_wdata;
        s14_wstrb   = m9_wstrb;
        s14_wlast   = m9_wlast;
        s14_wvalid  = m9_wvalid;
        s14_bready  = m9_bready;
        s14_arid    = m9_arid;
        s14_araddr  = m9_araddr;
        s14_arlen   = m9_arlen;
        s14_arsize  = m9_arsize;
        s14_arburst = m9_arburst;
        s14_arlock  = m9_arlock;
        s14_arcache = m9_arcache;
        s14_arprot  = m9_arprot;
        s14_arqos   = m9_arqos;
        s14_arvalid = m9_arvalid & m9_slave_select[14];
        s14_rready  = m9_rready;
    end
 else if (m10_slave_select[14]) begin
        s14_awid    = m10_awid;
        s14_awaddr  = m10_awaddr;
        s14_awlen   = m10_awlen;
        s14_awsize  = m10_awsize;
        s14_awburst = m10_awburst;
        s14_awlock  = m10_awlock;
        s14_awcache = m10_awcache;
        s14_awprot  = m10_awprot;
        s14_awqos   = m10_awqos;
        s14_awvalid = m10_awvalid & m10_slave_select[14];
        s14_wdata   = m10_wdata;
        s14_wstrb   = m10_wstrb;
        s14_wlast   = m10_wlast;
        s14_wvalid  = m10_wvalid;
        s14_bready  = m10_bready;
        s14_arid    = m10_arid;
        s14_araddr  = m10_araddr;
        s14_arlen   = m10_arlen;
        s14_arsize  = m10_arsize;
        s14_arburst = m10_arburst;
        s14_arlock  = m10_arlock;
        s14_arcache = m10_arcache;
        s14_arprot  = m10_arprot;
        s14_arqos   = m10_arqos;
        s14_arvalid = m10_arvalid & m10_slave_select[14];
        s14_rready  = m10_rready;
    end
 else if (m11_slave_select[14]) begin
        s14_awid    = m11_awid;
        s14_awaddr  = m11_awaddr;
        s14_awlen   = m11_awlen;
        s14_awsize  = m11_awsize;
        s14_awburst = m11_awburst;
        s14_awlock  = m11_awlock;
        s14_awcache = m11_awcache;
        s14_awprot  = m11_awprot;
        s14_awqos   = m11_awqos;
        s14_awvalid = m11_awvalid & m11_slave_select[14];
        s14_wdata   = m11_wdata;
        s14_wstrb   = m11_wstrb;
        s14_wlast   = m11_wlast;
        s14_wvalid  = m11_wvalid;
        s14_bready  = m11_bready;
        s14_arid    = m11_arid;
        s14_araddr  = m11_araddr;
        s14_arlen   = m11_arlen;
        s14_arsize  = m11_arsize;
        s14_arburst = m11_arburst;
        s14_arlock  = m11_arlock;
        s14_arcache = m11_arcache;
        s14_arprot  = m11_arprot;
        s14_arqos   = m11_arqos;
        s14_arvalid = m11_arvalid & m11_slave_select[14];
        s14_rready  = m11_rready;
    end
 else if (m12_slave_select[14]) begin
        s14_awid    = m12_awid;
        s14_awaddr  = m12_awaddr;
        s14_awlen   = m12_awlen;
        s14_awsize  = m12_awsize;
        s14_awburst = m12_awburst;
        s14_awlock  = m12_awlock;
        s14_awcache = m12_awcache;
        s14_awprot  = m12_awprot;
        s14_awqos   = m12_awqos;
        s14_awvalid = m12_awvalid & m12_slave_select[14];
        s14_wdata   = m12_wdata;
        s14_wstrb   = m12_wstrb;
        s14_wlast   = m12_wlast;
        s14_wvalid  = m12_wvalid;
        s14_bready  = m12_bready;
        s14_arid    = m12_arid;
        s14_araddr  = m12_araddr;
        s14_arlen   = m12_arlen;
        s14_arsize  = m12_arsize;
        s14_arburst = m12_arburst;
        s14_arlock  = m12_arlock;
        s14_arcache = m12_arcache;
        s14_arprot  = m12_arprot;
        s14_arqos   = m12_arqos;
        s14_arvalid = m12_arvalid & m12_slave_select[14];
        s14_rready  = m12_rready;
    end
 else if (m13_slave_select[14]) begin
        s14_awid    = m13_awid;
        s14_awaddr  = m13_awaddr;
        s14_awlen   = m13_awlen;
        s14_awsize  = m13_awsize;
        s14_awburst = m13_awburst;
        s14_awlock  = m13_awlock;
        s14_awcache = m13_awcache;
        s14_awprot  = m13_awprot;
        s14_awqos   = m13_awqos;
        s14_awvalid = m13_awvalid & m13_slave_select[14];
        s14_wdata   = m13_wdata;
        s14_wstrb   = m13_wstrb;
        s14_wlast   = m13_wlast;
        s14_wvalid  = m13_wvalid;
        s14_bready  = m13_bready;
        s14_arid    = m13_arid;
        s14_araddr  = m13_araddr;
        s14_arlen   = m13_arlen;
        s14_arsize  = m13_arsize;
        s14_arburst = m13_arburst;
        s14_arlock  = m13_arlock;
        s14_arcache = m13_arcache;
        s14_arprot  = m13_arprot;
        s14_arqos   = m13_arqos;
        s14_arvalid = m13_arvalid & m13_slave_select[14];
        s14_rready  = m13_rready;
    end
 else if (m14_slave_select[14]) begin
        s14_awid    = m14_awid;
        s14_awaddr  = m14_awaddr;
        s14_awlen   = m14_awlen;
        s14_awsize  = m14_awsize;
        s14_awburst = m14_awburst;
        s14_awlock  = m14_awlock;
        s14_awcache = m14_awcache;
        s14_awprot  = m14_awprot;
        s14_awqos   = m14_awqos;
        s14_awvalid = m14_awvalid & m14_slave_select[14];
        s14_wdata   = m14_wdata;
        s14_wstrb   = m14_wstrb;
        s14_wlast   = m14_wlast;
        s14_wvalid  = m14_wvalid;
        s14_bready  = m14_bready;
        s14_arid    = m14_arid;
        s14_araddr  = m14_araddr;
        s14_arlen   = m14_arlen;
        s14_arsize  = m14_arsize;
        s14_arburst = m14_arburst;
        s14_arlock  = m14_arlock;
        s14_arcache = m14_arcache;
        s14_arprot  = m14_arprot;
        s14_arqos   = m14_arqos;
        s14_arvalid = m14_arvalid & m14_slave_select[14];
        s14_rready  = m14_rready;
    end

end


// Route responses back to masters based on which slave they accessed


// Master 0 response multiplexing
always @(*) begin
    // Default values
    m0_awready = 'b0;
    m0_wready  = 'b0;
    m0_bid     = 'b0;
    m0_bresp   = 'b0;
    m0_bvalid  = 'b0;
    m0_arready = 'b0;
    m0_rid     = 'b0;
    m0_rdata   = 'b0;
    m0_rresp   = 'b0;
    m0_rlast   = 'b0;
    m0_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m0_slave_select[0]) begin
        m0_awready = s0_awready;
        m0_wready  = s0_wready;
        m0_bid     = s0_bid;
        m0_bresp   = s0_bresp;
        m0_bvalid  = s0_bvalid;
        m0_arready = s0_arready;
        m0_rid     = s0_rid;
        m0_rdata   = s0_rdata;
        m0_rresp   = s0_rresp;
        m0_rlast   = s0_rlast;
        m0_rvalid  = s0_rvalid;
    end
 else if (m0_slave_select[1]) begin
        m0_awready = s1_awready;
        m0_wready  = s1_wready;
        m0_bid     = s1_bid;
        m0_bresp   = s1_bresp;
        m0_bvalid  = s1_bvalid;
        m0_arready = s1_arready;
        m0_rid     = s1_rid;
        m0_rdata   = s1_rdata;
        m0_rresp   = s1_rresp;
        m0_rlast   = s1_rlast;
        m0_rvalid  = s1_rvalid;
    end
 else if (m0_slave_select[2]) begin
        m0_awready = s2_awready;
        m0_wready  = s2_wready;
        m0_bid     = s2_bid;
        m0_bresp   = s2_bresp;
        m0_bvalid  = s2_bvalid;
        m0_arready = s2_arready;
        m0_rid     = s2_rid;
        m0_rdata   = s2_rdata;
        m0_rresp   = s2_rresp;
        m0_rlast   = s2_rlast;
        m0_rvalid  = s2_rvalid;
    end
 else if (m0_slave_select[3]) begin
        m0_awready = s3_awready;
        m0_wready  = s3_wready;
        m0_bid     = s3_bid;
        m0_bresp   = s3_bresp;
        m0_bvalid  = s3_bvalid;
        m0_arready = s3_arready;
        m0_rid     = s3_rid;
        m0_rdata   = s3_rdata;
        m0_rresp   = s3_rresp;
        m0_rlast   = s3_rlast;
        m0_rvalid  = s3_rvalid;
    end
 else if (m0_slave_select[4]) begin
        m0_awready = s4_awready;
        m0_wready  = s4_wready;
        m0_bid     = s4_bid;
        m0_bresp   = s4_bresp;
        m0_bvalid  = s4_bvalid;
        m0_arready = s4_arready;
        m0_rid     = s4_rid;
        m0_rdata   = s4_rdata;
        m0_rresp   = s4_rresp;
        m0_rlast   = s4_rlast;
        m0_rvalid  = s4_rvalid;
    end
 else if (m0_slave_select[5]) begin
        m0_awready = s5_awready;
        m0_wready  = s5_wready;
        m0_bid     = s5_bid;
        m0_bresp   = s5_bresp;
        m0_bvalid  = s5_bvalid;
        m0_arready = s5_arready;
        m0_rid     = s5_rid;
        m0_rdata   = s5_rdata;
        m0_rresp   = s5_rresp;
        m0_rlast   = s5_rlast;
        m0_rvalid  = s5_rvalid;
    end
 else if (m0_slave_select[6]) begin
        m0_awready = s6_awready;
        m0_wready  = s6_wready;
        m0_bid     = s6_bid;
        m0_bresp   = s6_bresp;
        m0_bvalid  = s6_bvalid;
        m0_arready = s6_arready;
        m0_rid     = s6_rid;
        m0_rdata   = s6_rdata;
        m0_rresp   = s6_rresp;
        m0_rlast   = s6_rlast;
        m0_rvalid  = s6_rvalid;
    end
 else if (m0_slave_select[7]) begin
        m0_awready = s7_awready;
        m0_wready  = s7_wready;
        m0_bid     = s7_bid;
        m0_bresp   = s7_bresp;
        m0_bvalid  = s7_bvalid;
        m0_arready = s7_arready;
        m0_rid     = s7_rid;
        m0_rdata   = s7_rdata;
        m0_rresp   = s7_rresp;
        m0_rlast   = s7_rlast;
        m0_rvalid  = s7_rvalid;
    end
 else if (m0_slave_select[8]) begin
        m0_awready = s8_awready;
        m0_wready  = s8_wready;
        m0_bid     = s8_bid;
        m0_bresp   = s8_bresp;
        m0_bvalid  = s8_bvalid;
        m0_arready = s8_arready;
        m0_rid     = s8_rid;
        m0_rdata   = s8_rdata;
        m0_rresp   = s8_rresp;
        m0_rlast   = s8_rlast;
        m0_rvalid  = s8_rvalid;
    end
 else if (m0_slave_select[9]) begin
        m0_awready = s9_awready;
        m0_wready  = s9_wready;
        m0_bid     = s9_bid;
        m0_bresp   = s9_bresp;
        m0_bvalid  = s9_bvalid;
        m0_arready = s9_arready;
        m0_rid     = s9_rid;
        m0_rdata   = s9_rdata;
        m0_rresp   = s9_rresp;
        m0_rlast   = s9_rlast;
        m0_rvalid  = s9_rvalid;
    end
 else if (m0_slave_select[10]) begin
        m0_awready = s10_awready;
        m0_wready  = s10_wready;
        m0_bid     = s10_bid;
        m0_bresp   = s10_bresp;
        m0_bvalid  = s10_bvalid;
        m0_arready = s10_arready;
        m0_rid     = s10_rid;
        m0_rdata   = s10_rdata;
        m0_rresp   = s10_rresp;
        m0_rlast   = s10_rlast;
        m0_rvalid  = s10_rvalid;
    end
 else if (m0_slave_select[11]) begin
        m0_awready = s11_awready;
        m0_wready  = s11_wready;
        m0_bid     = s11_bid;
        m0_bresp   = s11_bresp;
        m0_bvalid  = s11_bvalid;
        m0_arready = s11_arready;
        m0_rid     = s11_rid;
        m0_rdata   = s11_rdata;
        m0_rresp   = s11_rresp;
        m0_rlast   = s11_rlast;
        m0_rvalid  = s11_rvalid;
    end
 else if (m0_slave_select[12]) begin
        m0_awready = s12_awready;
        m0_wready  = s12_wready;
        m0_bid     = s12_bid;
        m0_bresp   = s12_bresp;
        m0_bvalid  = s12_bvalid;
        m0_arready = s12_arready;
        m0_rid     = s12_rid;
        m0_rdata   = s12_rdata;
        m0_rresp   = s12_rresp;
        m0_rlast   = s12_rlast;
        m0_rvalid  = s12_rvalid;
    end
 else if (m0_slave_select[13]) begin
        m0_awready = s13_awready;
        m0_wready  = s13_wready;
        m0_bid     = s13_bid;
        m0_bresp   = s13_bresp;
        m0_bvalid  = s13_bvalid;
        m0_arready = s13_arready;
        m0_rid     = s13_rid;
        m0_rdata   = s13_rdata;
        m0_rresp   = s13_rresp;
        m0_rlast   = s13_rlast;
        m0_rvalid  = s13_rvalid;
    end
 else if (m0_slave_select[14]) begin
        m0_awready = s14_awready;
        m0_wready  = s14_wready;
        m0_bid     = s14_bid;
        m0_bresp   = s14_bresp;
        m0_bvalid  = s14_bvalid;
        m0_arready = s14_arready;
        m0_rid     = s14_rid;
        m0_rdata   = s14_rdata;
        m0_rresp   = s14_rresp;
        m0_rlast   = s14_rlast;
        m0_rvalid  = s14_rvalid;
    end

end


// Master 1 response multiplexing
always @(*) begin
    // Default values
    m1_awready = 'b0;
    m1_wready  = 'b0;
    m1_bid     = 'b0;
    m1_bresp   = 'b0;
    m1_bvalid  = 'b0;
    m1_arready = 'b0;
    m1_rid     = 'b0;
    m1_rdata   = 'b0;
    m1_rresp   = 'b0;
    m1_rlast   = 'b0;
    m1_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m1_slave_select[0]) begin
        m1_awready = s0_awready;
        m1_wready  = s0_wready;
        m1_bid     = s0_bid;
        m1_bresp   = s0_bresp;
        m1_bvalid  = s0_bvalid;
        m1_arready = s0_arready;
        m1_rid     = s0_rid;
        m1_rdata   = s0_rdata;
        m1_rresp   = s0_rresp;
        m1_rlast   = s0_rlast;
        m1_rvalid  = s0_rvalid;
    end
 else if (m1_slave_select[1]) begin
        m1_awready = s1_awready;
        m1_wready  = s1_wready;
        m1_bid     = s1_bid;
        m1_bresp   = s1_bresp;
        m1_bvalid  = s1_bvalid;
        m1_arready = s1_arready;
        m1_rid     = s1_rid;
        m1_rdata   = s1_rdata;
        m1_rresp   = s1_rresp;
        m1_rlast   = s1_rlast;
        m1_rvalid  = s1_rvalid;
    end
 else if (m1_slave_select[2]) begin
        m1_awready = s2_awready;
        m1_wready  = s2_wready;
        m1_bid     = s2_bid;
        m1_bresp   = s2_bresp;
        m1_bvalid  = s2_bvalid;
        m1_arready = s2_arready;
        m1_rid     = s2_rid;
        m1_rdata   = s2_rdata;
        m1_rresp   = s2_rresp;
        m1_rlast   = s2_rlast;
        m1_rvalid  = s2_rvalid;
    end
 else if (m1_slave_select[3]) begin
        m1_awready = s3_awready;
        m1_wready  = s3_wready;
        m1_bid     = s3_bid;
        m1_bresp   = s3_bresp;
        m1_bvalid  = s3_bvalid;
        m1_arready = s3_arready;
        m1_rid     = s3_rid;
        m1_rdata   = s3_rdata;
        m1_rresp   = s3_rresp;
        m1_rlast   = s3_rlast;
        m1_rvalid  = s3_rvalid;
    end
 else if (m1_slave_select[4]) begin
        m1_awready = s4_awready;
        m1_wready  = s4_wready;
        m1_bid     = s4_bid;
        m1_bresp   = s4_bresp;
        m1_bvalid  = s4_bvalid;
        m1_arready = s4_arready;
        m1_rid     = s4_rid;
        m1_rdata   = s4_rdata;
        m1_rresp   = s4_rresp;
        m1_rlast   = s4_rlast;
        m1_rvalid  = s4_rvalid;
    end
 else if (m1_slave_select[5]) begin
        m1_awready = s5_awready;
        m1_wready  = s5_wready;
        m1_bid     = s5_bid;
        m1_bresp   = s5_bresp;
        m1_bvalid  = s5_bvalid;
        m1_arready = s5_arready;
        m1_rid     = s5_rid;
        m1_rdata   = s5_rdata;
        m1_rresp   = s5_rresp;
        m1_rlast   = s5_rlast;
        m1_rvalid  = s5_rvalid;
    end
 else if (m1_slave_select[6]) begin
        m1_awready = s6_awready;
        m1_wready  = s6_wready;
        m1_bid     = s6_bid;
        m1_bresp   = s6_bresp;
        m1_bvalid  = s6_bvalid;
        m1_arready = s6_arready;
        m1_rid     = s6_rid;
        m1_rdata   = s6_rdata;
        m1_rresp   = s6_rresp;
        m1_rlast   = s6_rlast;
        m1_rvalid  = s6_rvalid;
    end
 else if (m1_slave_select[7]) begin
        m1_awready = s7_awready;
        m1_wready  = s7_wready;
        m1_bid     = s7_bid;
        m1_bresp   = s7_bresp;
        m1_bvalid  = s7_bvalid;
        m1_arready = s7_arready;
        m1_rid     = s7_rid;
        m1_rdata   = s7_rdata;
        m1_rresp   = s7_rresp;
        m1_rlast   = s7_rlast;
        m1_rvalid  = s7_rvalid;
    end
 else if (m1_slave_select[8]) begin
        m1_awready = s8_awready;
        m1_wready  = s8_wready;
        m1_bid     = s8_bid;
        m1_bresp   = s8_bresp;
        m1_bvalid  = s8_bvalid;
        m1_arready = s8_arready;
        m1_rid     = s8_rid;
        m1_rdata   = s8_rdata;
        m1_rresp   = s8_rresp;
        m1_rlast   = s8_rlast;
        m1_rvalid  = s8_rvalid;
    end
 else if (m1_slave_select[9]) begin
        m1_awready = s9_awready;
        m1_wready  = s9_wready;
        m1_bid     = s9_bid;
        m1_bresp   = s9_bresp;
        m1_bvalid  = s9_bvalid;
        m1_arready = s9_arready;
        m1_rid     = s9_rid;
        m1_rdata   = s9_rdata;
        m1_rresp   = s9_rresp;
        m1_rlast   = s9_rlast;
        m1_rvalid  = s9_rvalid;
    end
 else if (m1_slave_select[10]) begin
        m1_awready = s10_awready;
        m1_wready  = s10_wready;
        m1_bid     = s10_bid;
        m1_bresp   = s10_bresp;
        m1_bvalid  = s10_bvalid;
        m1_arready = s10_arready;
        m1_rid     = s10_rid;
        m1_rdata   = s10_rdata;
        m1_rresp   = s10_rresp;
        m1_rlast   = s10_rlast;
        m1_rvalid  = s10_rvalid;
    end
 else if (m1_slave_select[11]) begin
        m1_awready = s11_awready;
        m1_wready  = s11_wready;
        m1_bid     = s11_bid;
        m1_bresp   = s11_bresp;
        m1_bvalid  = s11_bvalid;
        m1_arready = s11_arready;
        m1_rid     = s11_rid;
        m1_rdata   = s11_rdata;
        m1_rresp   = s11_rresp;
        m1_rlast   = s11_rlast;
        m1_rvalid  = s11_rvalid;
    end
 else if (m1_slave_select[12]) begin
        m1_awready = s12_awready;
        m1_wready  = s12_wready;
        m1_bid     = s12_bid;
        m1_bresp   = s12_bresp;
        m1_bvalid  = s12_bvalid;
        m1_arready = s12_arready;
        m1_rid     = s12_rid;
        m1_rdata   = s12_rdata;
        m1_rresp   = s12_rresp;
        m1_rlast   = s12_rlast;
        m1_rvalid  = s12_rvalid;
    end
 else if (m1_slave_select[13]) begin
        m1_awready = s13_awready;
        m1_wready  = s13_wready;
        m1_bid     = s13_bid;
        m1_bresp   = s13_bresp;
        m1_bvalid  = s13_bvalid;
        m1_arready = s13_arready;
        m1_rid     = s13_rid;
        m1_rdata   = s13_rdata;
        m1_rresp   = s13_rresp;
        m1_rlast   = s13_rlast;
        m1_rvalid  = s13_rvalid;
    end
 else if (m1_slave_select[14]) begin
        m1_awready = s14_awready;
        m1_wready  = s14_wready;
        m1_bid     = s14_bid;
        m1_bresp   = s14_bresp;
        m1_bvalid  = s14_bvalid;
        m1_arready = s14_arready;
        m1_rid     = s14_rid;
        m1_rdata   = s14_rdata;
        m1_rresp   = s14_rresp;
        m1_rlast   = s14_rlast;
        m1_rvalid  = s14_rvalid;
    end

end


// Master 2 response multiplexing
always @(*) begin
    // Default values
    m2_awready = 'b0;
    m2_wready  = 'b0;
    m2_bid     = 'b0;
    m2_bresp   = 'b0;
    m2_bvalid  = 'b0;
    m2_arready = 'b0;
    m2_rid     = 'b0;
    m2_rdata   = 'b0;
    m2_rresp   = 'b0;
    m2_rlast   = 'b0;
    m2_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m2_slave_select[0]) begin
        m2_awready = s0_awready;
        m2_wready  = s0_wready;
        m2_bid     = s0_bid;
        m2_bresp   = s0_bresp;
        m2_bvalid  = s0_bvalid;
        m2_arready = s0_arready;
        m2_rid     = s0_rid;
        m2_rdata   = s0_rdata;
        m2_rresp   = s0_rresp;
        m2_rlast   = s0_rlast;
        m2_rvalid  = s0_rvalid;
    end
 else if (m2_slave_select[1]) begin
        m2_awready = s1_awready;
        m2_wready  = s1_wready;
        m2_bid     = s1_bid;
        m2_bresp   = s1_bresp;
        m2_bvalid  = s1_bvalid;
        m2_arready = s1_arready;
        m2_rid     = s1_rid;
        m2_rdata   = s1_rdata;
        m2_rresp   = s1_rresp;
        m2_rlast   = s1_rlast;
        m2_rvalid  = s1_rvalid;
    end
 else if (m2_slave_select[2]) begin
        m2_awready = s2_awready;
        m2_wready  = s2_wready;
        m2_bid     = s2_bid;
        m2_bresp   = s2_bresp;
        m2_bvalid  = s2_bvalid;
        m2_arready = s2_arready;
        m2_rid     = s2_rid;
        m2_rdata   = s2_rdata;
        m2_rresp   = s2_rresp;
        m2_rlast   = s2_rlast;
        m2_rvalid  = s2_rvalid;
    end
 else if (m2_slave_select[3]) begin
        m2_awready = s3_awready;
        m2_wready  = s3_wready;
        m2_bid     = s3_bid;
        m2_bresp   = s3_bresp;
        m2_bvalid  = s3_bvalid;
        m2_arready = s3_arready;
        m2_rid     = s3_rid;
        m2_rdata   = s3_rdata;
        m2_rresp   = s3_rresp;
        m2_rlast   = s3_rlast;
        m2_rvalid  = s3_rvalid;
    end
 else if (m2_slave_select[4]) begin
        m2_awready = s4_awready;
        m2_wready  = s4_wready;
        m2_bid     = s4_bid;
        m2_bresp   = s4_bresp;
        m2_bvalid  = s4_bvalid;
        m2_arready = s4_arready;
        m2_rid     = s4_rid;
        m2_rdata   = s4_rdata;
        m2_rresp   = s4_rresp;
        m2_rlast   = s4_rlast;
        m2_rvalid  = s4_rvalid;
    end
 else if (m2_slave_select[5]) begin
        m2_awready = s5_awready;
        m2_wready  = s5_wready;
        m2_bid     = s5_bid;
        m2_bresp   = s5_bresp;
        m2_bvalid  = s5_bvalid;
        m2_arready = s5_arready;
        m2_rid     = s5_rid;
        m2_rdata   = s5_rdata;
        m2_rresp   = s5_rresp;
        m2_rlast   = s5_rlast;
        m2_rvalid  = s5_rvalid;
    end
 else if (m2_slave_select[6]) begin
        m2_awready = s6_awready;
        m2_wready  = s6_wready;
        m2_bid     = s6_bid;
        m2_bresp   = s6_bresp;
        m2_bvalid  = s6_bvalid;
        m2_arready = s6_arready;
        m2_rid     = s6_rid;
        m2_rdata   = s6_rdata;
        m2_rresp   = s6_rresp;
        m2_rlast   = s6_rlast;
        m2_rvalid  = s6_rvalid;
    end
 else if (m2_slave_select[7]) begin
        m2_awready = s7_awready;
        m2_wready  = s7_wready;
        m2_bid     = s7_bid;
        m2_bresp   = s7_bresp;
        m2_bvalid  = s7_bvalid;
        m2_arready = s7_arready;
        m2_rid     = s7_rid;
        m2_rdata   = s7_rdata;
        m2_rresp   = s7_rresp;
        m2_rlast   = s7_rlast;
        m2_rvalid  = s7_rvalid;
    end
 else if (m2_slave_select[8]) begin
        m2_awready = s8_awready;
        m2_wready  = s8_wready;
        m2_bid     = s8_bid;
        m2_bresp   = s8_bresp;
        m2_bvalid  = s8_bvalid;
        m2_arready = s8_arready;
        m2_rid     = s8_rid;
        m2_rdata   = s8_rdata;
        m2_rresp   = s8_rresp;
        m2_rlast   = s8_rlast;
        m2_rvalid  = s8_rvalid;
    end
 else if (m2_slave_select[9]) begin
        m2_awready = s9_awready;
        m2_wready  = s9_wready;
        m2_bid     = s9_bid;
        m2_bresp   = s9_bresp;
        m2_bvalid  = s9_bvalid;
        m2_arready = s9_arready;
        m2_rid     = s9_rid;
        m2_rdata   = s9_rdata;
        m2_rresp   = s9_rresp;
        m2_rlast   = s9_rlast;
        m2_rvalid  = s9_rvalid;
    end
 else if (m2_slave_select[10]) begin
        m2_awready = s10_awready;
        m2_wready  = s10_wready;
        m2_bid     = s10_bid;
        m2_bresp   = s10_bresp;
        m2_bvalid  = s10_bvalid;
        m2_arready = s10_arready;
        m2_rid     = s10_rid;
        m2_rdata   = s10_rdata;
        m2_rresp   = s10_rresp;
        m2_rlast   = s10_rlast;
        m2_rvalid  = s10_rvalid;
    end
 else if (m2_slave_select[11]) begin
        m2_awready = s11_awready;
        m2_wready  = s11_wready;
        m2_bid     = s11_bid;
        m2_bresp   = s11_bresp;
        m2_bvalid  = s11_bvalid;
        m2_arready = s11_arready;
        m2_rid     = s11_rid;
        m2_rdata   = s11_rdata;
        m2_rresp   = s11_rresp;
        m2_rlast   = s11_rlast;
        m2_rvalid  = s11_rvalid;
    end
 else if (m2_slave_select[12]) begin
        m2_awready = s12_awready;
        m2_wready  = s12_wready;
        m2_bid     = s12_bid;
        m2_bresp   = s12_bresp;
        m2_bvalid  = s12_bvalid;
        m2_arready = s12_arready;
        m2_rid     = s12_rid;
        m2_rdata   = s12_rdata;
        m2_rresp   = s12_rresp;
        m2_rlast   = s12_rlast;
        m2_rvalid  = s12_rvalid;
    end
 else if (m2_slave_select[13]) begin
        m2_awready = s13_awready;
        m2_wready  = s13_wready;
        m2_bid     = s13_bid;
        m2_bresp   = s13_bresp;
        m2_bvalid  = s13_bvalid;
        m2_arready = s13_arready;
        m2_rid     = s13_rid;
        m2_rdata   = s13_rdata;
        m2_rresp   = s13_rresp;
        m2_rlast   = s13_rlast;
        m2_rvalid  = s13_rvalid;
    end
 else if (m2_slave_select[14]) begin
        m2_awready = s14_awready;
        m2_wready  = s14_wready;
        m2_bid     = s14_bid;
        m2_bresp   = s14_bresp;
        m2_bvalid  = s14_bvalid;
        m2_arready = s14_arready;
        m2_rid     = s14_rid;
        m2_rdata   = s14_rdata;
        m2_rresp   = s14_rresp;
        m2_rlast   = s14_rlast;
        m2_rvalid  = s14_rvalid;
    end

end


// Master 3 response multiplexing
always @(*) begin
    // Default values
    m3_awready = 'b0;
    m3_wready  = 'b0;
    m3_bid     = 'b0;
    m3_bresp   = 'b0;
    m3_bvalid  = 'b0;
    m3_arready = 'b0;
    m3_rid     = 'b0;
    m3_rdata   = 'b0;
    m3_rresp   = 'b0;
    m3_rlast   = 'b0;
    m3_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m3_slave_select[0]) begin
        m3_awready = s0_awready;
        m3_wready  = s0_wready;
        m3_bid     = s0_bid;
        m3_bresp   = s0_bresp;
        m3_bvalid  = s0_bvalid;
        m3_arready = s0_arready;
        m3_rid     = s0_rid;
        m3_rdata   = s0_rdata;
        m3_rresp   = s0_rresp;
        m3_rlast   = s0_rlast;
        m3_rvalid  = s0_rvalid;
    end
 else if (m3_slave_select[1]) begin
        m3_awready = s1_awready;
        m3_wready  = s1_wready;
        m3_bid     = s1_bid;
        m3_bresp   = s1_bresp;
        m3_bvalid  = s1_bvalid;
        m3_arready = s1_arready;
        m3_rid     = s1_rid;
        m3_rdata   = s1_rdata;
        m3_rresp   = s1_rresp;
        m3_rlast   = s1_rlast;
        m3_rvalid  = s1_rvalid;
    end
 else if (m3_slave_select[2]) begin
        m3_awready = s2_awready;
        m3_wready  = s2_wready;
        m3_bid     = s2_bid;
        m3_bresp   = s2_bresp;
        m3_bvalid  = s2_bvalid;
        m3_arready = s2_arready;
        m3_rid     = s2_rid;
        m3_rdata   = s2_rdata;
        m3_rresp   = s2_rresp;
        m3_rlast   = s2_rlast;
        m3_rvalid  = s2_rvalid;
    end
 else if (m3_slave_select[3]) begin
        m3_awready = s3_awready;
        m3_wready  = s3_wready;
        m3_bid     = s3_bid;
        m3_bresp   = s3_bresp;
        m3_bvalid  = s3_bvalid;
        m3_arready = s3_arready;
        m3_rid     = s3_rid;
        m3_rdata   = s3_rdata;
        m3_rresp   = s3_rresp;
        m3_rlast   = s3_rlast;
        m3_rvalid  = s3_rvalid;
    end
 else if (m3_slave_select[4]) begin
        m3_awready = s4_awready;
        m3_wready  = s4_wready;
        m3_bid     = s4_bid;
        m3_bresp   = s4_bresp;
        m3_bvalid  = s4_bvalid;
        m3_arready = s4_arready;
        m3_rid     = s4_rid;
        m3_rdata   = s4_rdata;
        m3_rresp   = s4_rresp;
        m3_rlast   = s4_rlast;
        m3_rvalid  = s4_rvalid;
    end
 else if (m3_slave_select[5]) begin
        m3_awready = s5_awready;
        m3_wready  = s5_wready;
        m3_bid     = s5_bid;
        m3_bresp   = s5_bresp;
        m3_bvalid  = s5_bvalid;
        m3_arready = s5_arready;
        m3_rid     = s5_rid;
        m3_rdata   = s5_rdata;
        m3_rresp   = s5_rresp;
        m3_rlast   = s5_rlast;
        m3_rvalid  = s5_rvalid;
    end
 else if (m3_slave_select[6]) begin
        m3_awready = s6_awready;
        m3_wready  = s6_wready;
        m3_bid     = s6_bid;
        m3_bresp   = s6_bresp;
        m3_bvalid  = s6_bvalid;
        m3_arready = s6_arready;
        m3_rid     = s6_rid;
        m3_rdata   = s6_rdata;
        m3_rresp   = s6_rresp;
        m3_rlast   = s6_rlast;
        m3_rvalid  = s6_rvalid;
    end
 else if (m3_slave_select[7]) begin
        m3_awready = s7_awready;
        m3_wready  = s7_wready;
        m3_bid     = s7_bid;
        m3_bresp   = s7_bresp;
        m3_bvalid  = s7_bvalid;
        m3_arready = s7_arready;
        m3_rid     = s7_rid;
        m3_rdata   = s7_rdata;
        m3_rresp   = s7_rresp;
        m3_rlast   = s7_rlast;
        m3_rvalid  = s7_rvalid;
    end
 else if (m3_slave_select[8]) begin
        m3_awready = s8_awready;
        m3_wready  = s8_wready;
        m3_bid     = s8_bid;
        m3_bresp   = s8_bresp;
        m3_bvalid  = s8_bvalid;
        m3_arready = s8_arready;
        m3_rid     = s8_rid;
        m3_rdata   = s8_rdata;
        m3_rresp   = s8_rresp;
        m3_rlast   = s8_rlast;
        m3_rvalid  = s8_rvalid;
    end
 else if (m3_slave_select[9]) begin
        m3_awready = s9_awready;
        m3_wready  = s9_wready;
        m3_bid     = s9_bid;
        m3_bresp   = s9_bresp;
        m3_bvalid  = s9_bvalid;
        m3_arready = s9_arready;
        m3_rid     = s9_rid;
        m3_rdata   = s9_rdata;
        m3_rresp   = s9_rresp;
        m3_rlast   = s9_rlast;
        m3_rvalid  = s9_rvalid;
    end
 else if (m3_slave_select[10]) begin
        m3_awready = s10_awready;
        m3_wready  = s10_wready;
        m3_bid     = s10_bid;
        m3_bresp   = s10_bresp;
        m3_bvalid  = s10_bvalid;
        m3_arready = s10_arready;
        m3_rid     = s10_rid;
        m3_rdata   = s10_rdata;
        m3_rresp   = s10_rresp;
        m3_rlast   = s10_rlast;
        m3_rvalid  = s10_rvalid;
    end
 else if (m3_slave_select[11]) begin
        m3_awready = s11_awready;
        m3_wready  = s11_wready;
        m3_bid     = s11_bid;
        m3_bresp   = s11_bresp;
        m3_bvalid  = s11_bvalid;
        m3_arready = s11_arready;
        m3_rid     = s11_rid;
        m3_rdata   = s11_rdata;
        m3_rresp   = s11_rresp;
        m3_rlast   = s11_rlast;
        m3_rvalid  = s11_rvalid;
    end
 else if (m3_slave_select[12]) begin
        m3_awready = s12_awready;
        m3_wready  = s12_wready;
        m3_bid     = s12_bid;
        m3_bresp   = s12_bresp;
        m3_bvalid  = s12_bvalid;
        m3_arready = s12_arready;
        m3_rid     = s12_rid;
        m3_rdata   = s12_rdata;
        m3_rresp   = s12_rresp;
        m3_rlast   = s12_rlast;
        m3_rvalid  = s12_rvalid;
    end
 else if (m3_slave_select[13]) begin
        m3_awready = s13_awready;
        m3_wready  = s13_wready;
        m3_bid     = s13_bid;
        m3_bresp   = s13_bresp;
        m3_bvalid  = s13_bvalid;
        m3_arready = s13_arready;
        m3_rid     = s13_rid;
        m3_rdata   = s13_rdata;
        m3_rresp   = s13_rresp;
        m3_rlast   = s13_rlast;
        m3_rvalid  = s13_rvalid;
    end
 else if (m3_slave_select[14]) begin
        m3_awready = s14_awready;
        m3_wready  = s14_wready;
        m3_bid     = s14_bid;
        m3_bresp   = s14_bresp;
        m3_bvalid  = s14_bvalid;
        m3_arready = s14_arready;
        m3_rid     = s14_rid;
        m3_rdata   = s14_rdata;
        m3_rresp   = s14_rresp;
        m3_rlast   = s14_rlast;
        m3_rvalid  = s14_rvalid;
    end

end


// Master 4 response multiplexing
always @(*) begin
    // Default values
    m4_awready = 'b0;
    m4_wready  = 'b0;
    m4_bid     = 'b0;
    m4_bresp   = 'b0;
    m4_bvalid  = 'b0;
    m4_arready = 'b0;
    m4_rid     = 'b0;
    m4_rdata   = 'b0;
    m4_rresp   = 'b0;
    m4_rlast   = 'b0;
    m4_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m4_slave_select[0]) begin
        m4_awready = s0_awready;
        m4_wready  = s0_wready;
        m4_bid     = s0_bid;
        m4_bresp   = s0_bresp;
        m4_bvalid  = s0_bvalid;
        m4_arready = s0_arready;
        m4_rid     = s0_rid;
        m4_rdata   = s0_rdata;
        m4_rresp   = s0_rresp;
        m4_rlast   = s0_rlast;
        m4_rvalid  = s0_rvalid;
    end
 else if (m4_slave_select[1]) begin
        m4_awready = s1_awready;
        m4_wready  = s1_wready;
        m4_bid     = s1_bid;
        m4_bresp   = s1_bresp;
        m4_bvalid  = s1_bvalid;
        m4_arready = s1_arready;
        m4_rid     = s1_rid;
        m4_rdata   = s1_rdata;
        m4_rresp   = s1_rresp;
        m4_rlast   = s1_rlast;
        m4_rvalid  = s1_rvalid;
    end
 else if (m4_slave_select[2]) begin
        m4_awready = s2_awready;
        m4_wready  = s2_wready;
        m4_bid     = s2_bid;
        m4_bresp   = s2_bresp;
        m4_bvalid  = s2_bvalid;
        m4_arready = s2_arready;
        m4_rid     = s2_rid;
        m4_rdata   = s2_rdata;
        m4_rresp   = s2_rresp;
        m4_rlast   = s2_rlast;
        m4_rvalid  = s2_rvalid;
    end
 else if (m4_slave_select[3]) begin
        m4_awready = s3_awready;
        m4_wready  = s3_wready;
        m4_bid     = s3_bid;
        m4_bresp   = s3_bresp;
        m4_bvalid  = s3_bvalid;
        m4_arready = s3_arready;
        m4_rid     = s3_rid;
        m4_rdata   = s3_rdata;
        m4_rresp   = s3_rresp;
        m4_rlast   = s3_rlast;
        m4_rvalid  = s3_rvalid;
    end
 else if (m4_slave_select[4]) begin
        m4_awready = s4_awready;
        m4_wready  = s4_wready;
        m4_bid     = s4_bid;
        m4_bresp   = s4_bresp;
        m4_bvalid  = s4_bvalid;
        m4_arready = s4_arready;
        m4_rid     = s4_rid;
        m4_rdata   = s4_rdata;
        m4_rresp   = s4_rresp;
        m4_rlast   = s4_rlast;
        m4_rvalid  = s4_rvalid;
    end
 else if (m4_slave_select[5]) begin
        m4_awready = s5_awready;
        m4_wready  = s5_wready;
        m4_bid     = s5_bid;
        m4_bresp   = s5_bresp;
        m4_bvalid  = s5_bvalid;
        m4_arready = s5_arready;
        m4_rid     = s5_rid;
        m4_rdata   = s5_rdata;
        m4_rresp   = s5_rresp;
        m4_rlast   = s5_rlast;
        m4_rvalid  = s5_rvalid;
    end
 else if (m4_slave_select[6]) begin
        m4_awready = s6_awready;
        m4_wready  = s6_wready;
        m4_bid     = s6_bid;
        m4_bresp   = s6_bresp;
        m4_bvalid  = s6_bvalid;
        m4_arready = s6_arready;
        m4_rid     = s6_rid;
        m4_rdata   = s6_rdata;
        m4_rresp   = s6_rresp;
        m4_rlast   = s6_rlast;
        m4_rvalid  = s6_rvalid;
    end
 else if (m4_slave_select[7]) begin
        m4_awready = s7_awready;
        m4_wready  = s7_wready;
        m4_bid     = s7_bid;
        m4_bresp   = s7_bresp;
        m4_bvalid  = s7_bvalid;
        m4_arready = s7_arready;
        m4_rid     = s7_rid;
        m4_rdata   = s7_rdata;
        m4_rresp   = s7_rresp;
        m4_rlast   = s7_rlast;
        m4_rvalid  = s7_rvalid;
    end
 else if (m4_slave_select[8]) begin
        m4_awready = s8_awready;
        m4_wready  = s8_wready;
        m4_bid     = s8_bid;
        m4_bresp   = s8_bresp;
        m4_bvalid  = s8_bvalid;
        m4_arready = s8_arready;
        m4_rid     = s8_rid;
        m4_rdata   = s8_rdata;
        m4_rresp   = s8_rresp;
        m4_rlast   = s8_rlast;
        m4_rvalid  = s8_rvalid;
    end
 else if (m4_slave_select[9]) begin
        m4_awready = s9_awready;
        m4_wready  = s9_wready;
        m4_bid     = s9_bid;
        m4_bresp   = s9_bresp;
        m4_bvalid  = s9_bvalid;
        m4_arready = s9_arready;
        m4_rid     = s9_rid;
        m4_rdata   = s9_rdata;
        m4_rresp   = s9_rresp;
        m4_rlast   = s9_rlast;
        m4_rvalid  = s9_rvalid;
    end
 else if (m4_slave_select[10]) begin
        m4_awready = s10_awready;
        m4_wready  = s10_wready;
        m4_bid     = s10_bid;
        m4_bresp   = s10_bresp;
        m4_bvalid  = s10_bvalid;
        m4_arready = s10_arready;
        m4_rid     = s10_rid;
        m4_rdata   = s10_rdata;
        m4_rresp   = s10_rresp;
        m4_rlast   = s10_rlast;
        m4_rvalid  = s10_rvalid;
    end
 else if (m4_slave_select[11]) begin
        m4_awready = s11_awready;
        m4_wready  = s11_wready;
        m4_bid     = s11_bid;
        m4_bresp   = s11_bresp;
        m4_bvalid  = s11_bvalid;
        m4_arready = s11_arready;
        m4_rid     = s11_rid;
        m4_rdata   = s11_rdata;
        m4_rresp   = s11_rresp;
        m4_rlast   = s11_rlast;
        m4_rvalid  = s11_rvalid;
    end
 else if (m4_slave_select[12]) begin
        m4_awready = s12_awready;
        m4_wready  = s12_wready;
        m4_bid     = s12_bid;
        m4_bresp   = s12_bresp;
        m4_bvalid  = s12_bvalid;
        m4_arready = s12_arready;
        m4_rid     = s12_rid;
        m4_rdata   = s12_rdata;
        m4_rresp   = s12_rresp;
        m4_rlast   = s12_rlast;
        m4_rvalid  = s12_rvalid;
    end
 else if (m4_slave_select[13]) begin
        m4_awready = s13_awready;
        m4_wready  = s13_wready;
        m4_bid     = s13_bid;
        m4_bresp   = s13_bresp;
        m4_bvalid  = s13_bvalid;
        m4_arready = s13_arready;
        m4_rid     = s13_rid;
        m4_rdata   = s13_rdata;
        m4_rresp   = s13_rresp;
        m4_rlast   = s13_rlast;
        m4_rvalid  = s13_rvalid;
    end
 else if (m4_slave_select[14]) begin
        m4_awready = s14_awready;
        m4_wready  = s14_wready;
        m4_bid     = s14_bid;
        m4_bresp   = s14_bresp;
        m4_bvalid  = s14_bvalid;
        m4_arready = s14_arready;
        m4_rid     = s14_rid;
        m4_rdata   = s14_rdata;
        m4_rresp   = s14_rresp;
        m4_rlast   = s14_rlast;
        m4_rvalid  = s14_rvalid;
    end

end


// Master 5 response multiplexing
always @(*) begin
    // Default values
    m5_awready = 'b0;
    m5_wready  = 'b0;
    m5_bid     = 'b0;
    m5_bresp   = 'b0;
    m5_bvalid  = 'b0;
    m5_arready = 'b0;
    m5_rid     = 'b0;
    m5_rdata   = 'b0;
    m5_rresp   = 'b0;
    m5_rlast   = 'b0;
    m5_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m5_slave_select[0]) begin
        m5_awready = s0_awready;
        m5_wready  = s0_wready;
        m5_bid     = s0_bid;
        m5_bresp   = s0_bresp;
        m5_bvalid  = s0_bvalid;
        m5_arready = s0_arready;
        m5_rid     = s0_rid;
        m5_rdata   = s0_rdata;
        m5_rresp   = s0_rresp;
        m5_rlast   = s0_rlast;
        m5_rvalid  = s0_rvalid;
    end
 else if (m5_slave_select[1]) begin
        m5_awready = s1_awready;
        m5_wready  = s1_wready;
        m5_bid     = s1_bid;
        m5_bresp   = s1_bresp;
        m5_bvalid  = s1_bvalid;
        m5_arready = s1_arready;
        m5_rid     = s1_rid;
        m5_rdata   = s1_rdata;
        m5_rresp   = s1_rresp;
        m5_rlast   = s1_rlast;
        m5_rvalid  = s1_rvalid;
    end
 else if (m5_slave_select[2]) begin
        m5_awready = s2_awready;
        m5_wready  = s2_wready;
        m5_bid     = s2_bid;
        m5_bresp   = s2_bresp;
        m5_bvalid  = s2_bvalid;
        m5_arready = s2_arready;
        m5_rid     = s2_rid;
        m5_rdata   = s2_rdata;
        m5_rresp   = s2_rresp;
        m5_rlast   = s2_rlast;
        m5_rvalid  = s2_rvalid;
    end
 else if (m5_slave_select[3]) begin
        m5_awready = s3_awready;
        m5_wready  = s3_wready;
        m5_bid     = s3_bid;
        m5_bresp   = s3_bresp;
        m5_bvalid  = s3_bvalid;
        m5_arready = s3_arready;
        m5_rid     = s3_rid;
        m5_rdata   = s3_rdata;
        m5_rresp   = s3_rresp;
        m5_rlast   = s3_rlast;
        m5_rvalid  = s3_rvalid;
    end
 else if (m5_slave_select[4]) begin
        m5_awready = s4_awready;
        m5_wready  = s4_wready;
        m5_bid     = s4_bid;
        m5_bresp   = s4_bresp;
        m5_bvalid  = s4_bvalid;
        m5_arready = s4_arready;
        m5_rid     = s4_rid;
        m5_rdata   = s4_rdata;
        m5_rresp   = s4_rresp;
        m5_rlast   = s4_rlast;
        m5_rvalid  = s4_rvalid;
    end
 else if (m5_slave_select[5]) begin
        m5_awready = s5_awready;
        m5_wready  = s5_wready;
        m5_bid     = s5_bid;
        m5_bresp   = s5_bresp;
        m5_bvalid  = s5_bvalid;
        m5_arready = s5_arready;
        m5_rid     = s5_rid;
        m5_rdata   = s5_rdata;
        m5_rresp   = s5_rresp;
        m5_rlast   = s5_rlast;
        m5_rvalid  = s5_rvalid;
    end
 else if (m5_slave_select[6]) begin
        m5_awready = s6_awready;
        m5_wready  = s6_wready;
        m5_bid     = s6_bid;
        m5_bresp   = s6_bresp;
        m5_bvalid  = s6_bvalid;
        m5_arready = s6_arready;
        m5_rid     = s6_rid;
        m5_rdata   = s6_rdata;
        m5_rresp   = s6_rresp;
        m5_rlast   = s6_rlast;
        m5_rvalid  = s6_rvalid;
    end
 else if (m5_slave_select[7]) begin
        m5_awready = s7_awready;
        m5_wready  = s7_wready;
        m5_bid     = s7_bid;
        m5_bresp   = s7_bresp;
        m5_bvalid  = s7_bvalid;
        m5_arready = s7_arready;
        m5_rid     = s7_rid;
        m5_rdata   = s7_rdata;
        m5_rresp   = s7_rresp;
        m5_rlast   = s7_rlast;
        m5_rvalid  = s7_rvalid;
    end
 else if (m5_slave_select[8]) begin
        m5_awready = s8_awready;
        m5_wready  = s8_wready;
        m5_bid     = s8_bid;
        m5_bresp   = s8_bresp;
        m5_bvalid  = s8_bvalid;
        m5_arready = s8_arready;
        m5_rid     = s8_rid;
        m5_rdata   = s8_rdata;
        m5_rresp   = s8_rresp;
        m5_rlast   = s8_rlast;
        m5_rvalid  = s8_rvalid;
    end
 else if (m5_slave_select[9]) begin
        m5_awready = s9_awready;
        m5_wready  = s9_wready;
        m5_bid     = s9_bid;
        m5_bresp   = s9_bresp;
        m5_bvalid  = s9_bvalid;
        m5_arready = s9_arready;
        m5_rid     = s9_rid;
        m5_rdata   = s9_rdata;
        m5_rresp   = s9_rresp;
        m5_rlast   = s9_rlast;
        m5_rvalid  = s9_rvalid;
    end
 else if (m5_slave_select[10]) begin
        m5_awready = s10_awready;
        m5_wready  = s10_wready;
        m5_bid     = s10_bid;
        m5_bresp   = s10_bresp;
        m5_bvalid  = s10_bvalid;
        m5_arready = s10_arready;
        m5_rid     = s10_rid;
        m5_rdata   = s10_rdata;
        m5_rresp   = s10_rresp;
        m5_rlast   = s10_rlast;
        m5_rvalid  = s10_rvalid;
    end
 else if (m5_slave_select[11]) begin
        m5_awready = s11_awready;
        m5_wready  = s11_wready;
        m5_bid     = s11_bid;
        m5_bresp   = s11_bresp;
        m5_bvalid  = s11_bvalid;
        m5_arready = s11_arready;
        m5_rid     = s11_rid;
        m5_rdata   = s11_rdata;
        m5_rresp   = s11_rresp;
        m5_rlast   = s11_rlast;
        m5_rvalid  = s11_rvalid;
    end
 else if (m5_slave_select[12]) begin
        m5_awready = s12_awready;
        m5_wready  = s12_wready;
        m5_bid     = s12_bid;
        m5_bresp   = s12_bresp;
        m5_bvalid  = s12_bvalid;
        m5_arready = s12_arready;
        m5_rid     = s12_rid;
        m5_rdata   = s12_rdata;
        m5_rresp   = s12_rresp;
        m5_rlast   = s12_rlast;
        m5_rvalid  = s12_rvalid;
    end
 else if (m5_slave_select[13]) begin
        m5_awready = s13_awready;
        m5_wready  = s13_wready;
        m5_bid     = s13_bid;
        m5_bresp   = s13_bresp;
        m5_bvalid  = s13_bvalid;
        m5_arready = s13_arready;
        m5_rid     = s13_rid;
        m5_rdata   = s13_rdata;
        m5_rresp   = s13_rresp;
        m5_rlast   = s13_rlast;
        m5_rvalid  = s13_rvalid;
    end
 else if (m5_slave_select[14]) begin
        m5_awready = s14_awready;
        m5_wready  = s14_wready;
        m5_bid     = s14_bid;
        m5_bresp   = s14_bresp;
        m5_bvalid  = s14_bvalid;
        m5_arready = s14_arready;
        m5_rid     = s14_rid;
        m5_rdata   = s14_rdata;
        m5_rresp   = s14_rresp;
        m5_rlast   = s14_rlast;
        m5_rvalid  = s14_rvalid;
    end

end


// Master 6 response multiplexing
always @(*) begin
    // Default values
    m6_awready = 'b0;
    m6_wready  = 'b0;
    m6_bid     = 'b0;
    m6_bresp   = 'b0;
    m6_bvalid  = 'b0;
    m6_arready = 'b0;
    m6_rid     = 'b0;
    m6_rdata   = 'b0;
    m6_rresp   = 'b0;
    m6_rlast   = 'b0;
    m6_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m6_slave_select[0]) begin
        m6_awready = s0_awready;
        m6_wready  = s0_wready;
        m6_bid     = s0_bid;
        m6_bresp   = s0_bresp;
        m6_bvalid  = s0_bvalid;
        m6_arready = s0_arready;
        m6_rid     = s0_rid;
        m6_rdata   = s0_rdata;
        m6_rresp   = s0_rresp;
        m6_rlast   = s0_rlast;
        m6_rvalid  = s0_rvalid;
    end
 else if (m6_slave_select[1]) begin
        m6_awready = s1_awready;
        m6_wready  = s1_wready;
        m6_bid     = s1_bid;
        m6_bresp   = s1_bresp;
        m6_bvalid  = s1_bvalid;
        m6_arready = s1_arready;
        m6_rid     = s1_rid;
        m6_rdata   = s1_rdata;
        m6_rresp   = s1_rresp;
        m6_rlast   = s1_rlast;
        m6_rvalid  = s1_rvalid;
    end
 else if (m6_slave_select[2]) begin
        m6_awready = s2_awready;
        m6_wready  = s2_wready;
        m6_bid     = s2_bid;
        m6_bresp   = s2_bresp;
        m6_bvalid  = s2_bvalid;
        m6_arready = s2_arready;
        m6_rid     = s2_rid;
        m6_rdata   = s2_rdata;
        m6_rresp   = s2_rresp;
        m6_rlast   = s2_rlast;
        m6_rvalid  = s2_rvalid;
    end
 else if (m6_slave_select[3]) begin
        m6_awready = s3_awready;
        m6_wready  = s3_wready;
        m6_bid     = s3_bid;
        m6_bresp   = s3_bresp;
        m6_bvalid  = s3_bvalid;
        m6_arready = s3_arready;
        m6_rid     = s3_rid;
        m6_rdata   = s3_rdata;
        m6_rresp   = s3_rresp;
        m6_rlast   = s3_rlast;
        m6_rvalid  = s3_rvalid;
    end
 else if (m6_slave_select[4]) begin
        m6_awready = s4_awready;
        m6_wready  = s4_wready;
        m6_bid     = s4_bid;
        m6_bresp   = s4_bresp;
        m6_bvalid  = s4_bvalid;
        m6_arready = s4_arready;
        m6_rid     = s4_rid;
        m6_rdata   = s4_rdata;
        m6_rresp   = s4_rresp;
        m6_rlast   = s4_rlast;
        m6_rvalid  = s4_rvalid;
    end
 else if (m6_slave_select[5]) begin
        m6_awready = s5_awready;
        m6_wready  = s5_wready;
        m6_bid     = s5_bid;
        m6_bresp   = s5_bresp;
        m6_bvalid  = s5_bvalid;
        m6_arready = s5_arready;
        m6_rid     = s5_rid;
        m6_rdata   = s5_rdata;
        m6_rresp   = s5_rresp;
        m6_rlast   = s5_rlast;
        m6_rvalid  = s5_rvalid;
    end
 else if (m6_slave_select[6]) begin
        m6_awready = s6_awready;
        m6_wready  = s6_wready;
        m6_bid     = s6_bid;
        m6_bresp   = s6_bresp;
        m6_bvalid  = s6_bvalid;
        m6_arready = s6_arready;
        m6_rid     = s6_rid;
        m6_rdata   = s6_rdata;
        m6_rresp   = s6_rresp;
        m6_rlast   = s6_rlast;
        m6_rvalid  = s6_rvalid;
    end
 else if (m6_slave_select[7]) begin
        m6_awready = s7_awready;
        m6_wready  = s7_wready;
        m6_bid     = s7_bid;
        m6_bresp   = s7_bresp;
        m6_bvalid  = s7_bvalid;
        m6_arready = s7_arready;
        m6_rid     = s7_rid;
        m6_rdata   = s7_rdata;
        m6_rresp   = s7_rresp;
        m6_rlast   = s7_rlast;
        m6_rvalid  = s7_rvalid;
    end
 else if (m6_slave_select[8]) begin
        m6_awready = s8_awready;
        m6_wready  = s8_wready;
        m6_bid     = s8_bid;
        m6_bresp   = s8_bresp;
        m6_bvalid  = s8_bvalid;
        m6_arready = s8_arready;
        m6_rid     = s8_rid;
        m6_rdata   = s8_rdata;
        m6_rresp   = s8_rresp;
        m6_rlast   = s8_rlast;
        m6_rvalid  = s8_rvalid;
    end
 else if (m6_slave_select[9]) begin
        m6_awready = s9_awready;
        m6_wready  = s9_wready;
        m6_bid     = s9_bid;
        m6_bresp   = s9_bresp;
        m6_bvalid  = s9_bvalid;
        m6_arready = s9_arready;
        m6_rid     = s9_rid;
        m6_rdata   = s9_rdata;
        m6_rresp   = s9_rresp;
        m6_rlast   = s9_rlast;
        m6_rvalid  = s9_rvalid;
    end
 else if (m6_slave_select[10]) begin
        m6_awready = s10_awready;
        m6_wready  = s10_wready;
        m6_bid     = s10_bid;
        m6_bresp   = s10_bresp;
        m6_bvalid  = s10_bvalid;
        m6_arready = s10_arready;
        m6_rid     = s10_rid;
        m6_rdata   = s10_rdata;
        m6_rresp   = s10_rresp;
        m6_rlast   = s10_rlast;
        m6_rvalid  = s10_rvalid;
    end
 else if (m6_slave_select[11]) begin
        m6_awready = s11_awready;
        m6_wready  = s11_wready;
        m6_bid     = s11_bid;
        m6_bresp   = s11_bresp;
        m6_bvalid  = s11_bvalid;
        m6_arready = s11_arready;
        m6_rid     = s11_rid;
        m6_rdata   = s11_rdata;
        m6_rresp   = s11_rresp;
        m6_rlast   = s11_rlast;
        m6_rvalid  = s11_rvalid;
    end
 else if (m6_slave_select[12]) begin
        m6_awready = s12_awready;
        m6_wready  = s12_wready;
        m6_bid     = s12_bid;
        m6_bresp   = s12_bresp;
        m6_bvalid  = s12_bvalid;
        m6_arready = s12_arready;
        m6_rid     = s12_rid;
        m6_rdata   = s12_rdata;
        m6_rresp   = s12_rresp;
        m6_rlast   = s12_rlast;
        m6_rvalid  = s12_rvalid;
    end
 else if (m6_slave_select[13]) begin
        m6_awready = s13_awready;
        m6_wready  = s13_wready;
        m6_bid     = s13_bid;
        m6_bresp   = s13_bresp;
        m6_bvalid  = s13_bvalid;
        m6_arready = s13_arready;
        m6_rid     = s13_rid;
        m6_rdata   = s13_rdata;
        m6_rresp   = s13_rresp;
        m6_rlast   = s13_rlast;
        m6_rvalid  = s13_rvalid;
    end
 else if (m6_slave_select[14]) begin
        m6_awready = s14_awready;
        m6_wready  = s14_wready;
        m6_bid     = s14_bid;
        m6_bresp   = s14_bresp;
        m6_bvalid  = s14_bvalid;
        m6_arready = s14_arready;
        m6_rid     = s14_rid;
        m6_rdata   = s14_rdata;
        m6_rresp   = s14_rresp;
        m6_rlast   = s14_rlast;
        m6_rvalid  = s14_rvalid;
    end

end


// Master 7 response multiplexing
always @(*) begin
    // Default values
    m7_awready = 'b0;
    m7_wready  = 'b0;
    m7_bid     = 'b0;
    m7_bresp   = 'b0;
    m7_bvalid  = 'b0;
    m7_arready = 'b0;
    m7_rid     = 'b0;
    m7_rdata   = 'b0;
    m7_rresp   = 'b0;
    m7_rlast   = 'b0;
    m7_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m7_slave_select[0]) begin
        m7_awready = s0_awready;
        m7_wready  = s0_wready;
        m7_bid     = s0_bid;
        m7_bresp   = s0_bresp;
        m7_bvalid  = s0_bvalid;
        m7_arready = s0_arready;
        m7_rid     = s0_rid;
        m7_rdata   = s0_rdata;
        m7_rresp   = s0_rresp;
        m7_rlast   = s0_rlast;
        m7_rvalid  = s0_rvalid;
    end
 else if (m7_slave_select[1]) begin
        m7_awready = s1_awready;
        m7_wready  = s1_wready;
        m7_bid     = s1_bid;
        m7_bresp   = s1_bresp;
        m7_bvalid  = s1_bvalid;
        m7_arready = s1_arready;
        m7_rid     = s1_rid;
        m7_rdata   = s1_rdata;
        m7_rresp   = s1_rresp;
        m7_rlast   = s1_rlast;
        m7_rvalid  = s1_rvalid;
    end
 else if (m7_slave_select[2]) begin
        m7_awready = s2_awready;
        m7_wready  = s2_wready;
        m7_bid     = s2_bid;
        m7_bresp   = s2_bresp;
        m7_bvalid  = s2_bvalid;
        m7_arready = s2_arready;
        m7_rid     = s2_rid;
        m7_rdata   = s2_rdata;
        m7_rresp   = s2_rresp;
        m7_rlast   = s2_rlast;
        m7_rvalid  = s2_rvalid;
    end
 else if (m7_slave_select[3]) begin
        m7_awready = s3_awready;
        m7_wready  = s3_wready;
        m7_bid     = s3_bid;
        m7_bresp   = s3_bresp;
        m7_bvalid  = s3_bvalid;
        m7_arready = s3_arready;
        m7_rid     = s3_rid;
        m7_rdata   = s3_rdata;
        m7_rresp   = s3_rresp;
        m7_rlast   = s3_rlast;
        m7_rvalid  = s3_rvalid;
    end
 else if (m7_slave_select[4]) begin
        m7_awready = s4_awready;
        m7_wready  = s4_wready;
        m7_bid     = s4_bid;
        m7_bresp   = s4_bresp;
        m7_bvalid  = s4_bvalid;
        m7_arready = s4_arready;
        m7_rid     = s4_rid;
        m7_rdata   = s4_rdata;
        m7_rresp   = s4_rresp;
        m7_rlast   = s4_rlast;
        m7_rvalid  = s4_rvalid;
    end
 else if (m7_slave_select[5]) begin
        m7_awready = s5_awready;
        m7_wready  = s5_wready;
        m7_bid     = s5_bid;
        m7_bresp   = s5_bresp;
        m7_bvalid  = s5_bvalid;
        m7_arready = s5_arready;
        m7_rid     = s5_rid;
        m7_rdata   = s5_rdata;
        m7_rresp   = s5_rresp;
        m7_rlast   = s5_rlast;
        m7_rvalid  = s5_rvalid;
    end
 else if (m7_slave_select[6]) begin
        m7_awready = s6_awready;
        m7_wready  = s6_wready;
        m7_bid     = s6_bid;
        m7_bresp   = s6_bresp;
        m7_bvalid  = s6_bvalid;
        m7_arready = s6_arready;
        m7_rid     = s6_rid;
        m7_rdata   = s6_rdata;
        m7_rresp   = s6_rresp;
        m7_rlast   = s6_rlast;
        m7_rvalid  = s6_rvalid;
    end
 else if (m7_slave_select[7]) begin
        m7_awready = s7_awready;
        m7_wready  = s7_wready;
        m7_bid     = s7_bid;
        m7_bresp   = s7_bresp;
        m7_bvalid  = s7_bvalid;
        m7_arready = s7_arready;
        m7_rid     = s7_rid;
        m7_rdata   = s7_rdata;
        m7_rresp   = s7_rresp;
        m7_rlast   = s7_rlast;
        m7_rvalid  = s7_rvalid;
    end
 else if (m7_slave_select[8]) begin
        m7_awready = s8_awready;
        m7_wready  = s8_wready;
        m7_bid     = s8_bid;
        m7_bresp   = s8_bresp;
        m7_bvalid  = s8_bvalid;
        m7_arready = s8_arready;
        m7_rid     = s8_rid;
        m7_rdata   = s8_rdata;
        m7_rresp   = s8_rresp;
        m7_rlast   = s8_rlast;
        m7_rvalid  = s8_rvalid;
    end
 else if (m7_slave_select[9]) begin
        m7_awready = s9_awready;
        m7_wready  = s9_wready;
        m7_bid     = s9_bid;
        m7_bresp   = s9_bresp;
        m7_bvalid  = s9_bvalid;
        m7_arready = s9_arready;
        m7_rid     = s9_rid;
        m7_rdata   = s9_rdata;
        m7_rresp   = s9_rresp;
        m7_rlast   = s9_rlast;
        m7_rvalid  = s9_rvalid;
    end
 else if (m7_slave_select[10]) begin
        m7_awready = s10_awready;
        m7_wready  = s10_wready;
        m7_bid     = s10_bid;
        m7_bresp   = s10_bresp;
        m7_bvalid  = s10_bvalid;
        m7_arready = s10_arready;
        m7_rid     = s10_rid;
        m7_rdata   = s10_rdata;
        m7_rresp   = s10_rresp;
        m7_rlast   = s10_rlast;
        m7_rvalid  = s10_rvalid;
    end
 else if (m7_slave_select[11]) begin
        m7_awready = s11_awready;
        m7_wready  = s11_wready;
        m7_bid     = s11_bid;
        m7_bresp   = s11_bresp;
        m7_bvalid  = s11_bvalid;
        m7_arready = s11_arready;
        m7_rid     = s11_rid;
        m7_rdata   = s11_rdata;
        m7_rresp   = s11_rresp;
        m7_rlast   = s11_rlast;
        m7_rvalid  = s11_rvalid;
    end
 else if (m7_slave_select[12]) begin
        m7_awready = s12_awready;
        m7_wready  = s12_wready;
        m7_bid     = s12_bid;
        m7_bresp   = s12_bresp;
        m7_bvalid  = s12_bvalid;
        m7_arready = s12_arready;
        m7_rid     = s12_rid;
        m7_rdata   = s12_rdata;
        m7_rresp   = s12_rresp;
        m7_rlast   = s12_rlast;
        m7_rvalid  = s12_rvalid;
    end
 else if (m7_slave_select[13]) begin
        m7_awready = s13_awready;
        m7_wready  = s13_wready;
        m7_bid     = s13_bid;
        m7_bresp   = s13_bresp;
        m7_bvalid  = s13_bvalid;
        m7_arready = s13_arready;
        m7_rid     = s13_rid;
        m7_rdata   = s13_rdata;
        m7_rresp   = s13_rresp;
        m7_rlast   = s13_rlast;
        m7_rvalid  = s13_rvalid;
    end
 else if (m7_slave_select[14]) begin
        m7_awready = s14_awready;
        m7_wready  = s14_wready;
        m7_bid     = s14_bid;
        m7_bresp   = s14_bresp;
        m7_bvalid  = s14_bvalid;
        m7_arready = s14_arready;
        m7_rid     = s14_rid;
        m7_rdata   = s14_rdata;
        m7_rresp   = s14_rresp;
        m7_rlast   = s14_rlast;
        m7_rvalid  = s14_rvalid;
    end

end


// Master 8 response multiplexing
always @(*) begin
    // Default values
    m8_awready = 'b0;
    m8_wready  = 'b0;
    m8_bid     = 'b0;
    m8_bresp   = 'b0;
    m8_bvalid  = 'b0;
    m8_arready = 'b0;
    m8_rid     = 'b0;
    m8_rdata   = 'b0;
    m8_rresp   = 'b0;
    m8_rlast   = 'b0;
    m8_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m8_slave_select[0]) begin
        m8_awready = s0_awready;
        m8_wready  = s0_wready;
        m8_bid     = s0_bid;
        m8_bresp   = s0_bresp;
        m8_bvalid  = s0_bvalid;
        m8_arready = s0_arready;
        m8_rid     = s0_rid;
        m8_rdata   = s0_rdata;
        m8_rresp   = s0_rresp;
        m8_rlast   = s0_rlast;
        m8_rvalid  = s0_rvalid;
    end
 else if (m8_slave_select[1]) begin
        m8_awready = s1_awready;
        m8_wready  = s1_wready;
        m8_bid     = s1_bid;
        m8_bresp   = s1_bresp;
        m8_bvalid  = s1_bvalid;
        m8_arready = s1_arready;
        m8_rid     = s1_rid;
        m8_rdata   = s1_rdata;
        m8_rresp   = s1_rresp;
        m8_rlast   = s1_rlast;
        m8_rvalid  = s1_rvalid;
    end
 else if (m8_slave_select[2]) begin
        m8_awready = s2_awready;
        m8_wready  = s2_wready;
        m8_bid     = s2_bid;
        m8_bresp   = s2_bresp;
        m8_bvalid  = s2_bvalid;
        m8_arready = s2_arready;
        m8_rid     = s2_rid;
        m8_rdata   = s2_rdata;
        m8_rresp   = s2_rresp;
        m8_rlast   = s2_rlast;
        m8_rvalid  = s2_rvalid;
    end
 else if (m8_slave_select[3]) begin
        m8_awready = s3_awready;
        m8_wready  = s3_wready;
        m8_bid     = s3_bid;
        m8_bresp   = s3_bresp;
        m8_bvalid  = s3_bvalid;
        m8_arready = s3_arready;
        m8_rid     = s3_rid;
        m8_rdata   = s3_rdata;
        m8_rresp   = s3_rresp;
        m8_rlast   = s3_rlast;
        m8_rvalid  = s3_rvalid;
    end
 else if (m8_slave_select[4]) begin
        m8_awready = s4_awready;
        m8_wready  = s4_wready;
        m8_bid     = s4_bid;
        m8_bresp   = s4_bresp;
        m8_bvalid  = s4_bvalid;
        m8_arready = s4_arready;
        m8_rid     = s4_rid;
        m8_rdata   = s4_rdata;
        m8_rresp   = s4_rresp;
        m8_rlast   = s4_rlast;
        m8_rvalid  = s4_rvalid;
    end
 else if (m8_slave_select[5]) begin
        m8_awready = s5_awready;
        m8_wready  = s5_wready;
        m8_bid     = s5_bid;
        m8_bresp   = s5_bresp;
        m8_bvalid  = s5_bvalid;
        m8_arready = s5_arready;
        m8_rid     = s5_rid;
        m8_rdata   = s5_rdata;
        m8_rresp   = s5_rresp;
        m8_rlast   = s5_rlast;
        m8_rvalid  = s5_rvalid;
    end
 else if (m8_slave_select[6]) begin
        m8_awready = s6_awready;
        m8_wready  = s6_wready;
        m8_bid     = s6_bid;
        m8_bresp   = s6_bresp;
        m8_bvalid  = s6_bvalid;
        m8_arready = s6_arready;
        m8_rid     = s6_rid;
        m8_rdata   = s6_rdata;
        m8_rresp   = s6_rresp;
        m8_rlast   = s6_rlast;
        m8_rvalid  = s6_rvalid;
    end
 else if (m8_slave_select[7]) begin
        m8_awready = s7_awready;
        m8_wready  = s7_wready;
        m8_bid     = s7_bid;
        m8_bresp   = s7_bresp;
        m8_bvalid  = s7_bvalid;
        m8_arready = s7_arready;
        m8_rid     = s7_rid;
        m8_rdata   = s7_rdata;
        m8_rresp   = s7_rresp;
        m8_rlast   = s7_rlast;
        m8_rvalid  = s7_rvalid;
    end
 else if (m8_slave_select[8]) begin
        m8_awready = s8_awready;
        m8_wready  = s8_wready;
        m8_bid     = s8_bid;
        m8_bresp   = s8_bresp;
        m8_bvalid  = s8_bvalid;
        m8_arready = s8_arready;
        m8_rid     = s8_rid;
        m8_rdata   = s8_rdata;
        m8_rresp   = s8_rresp;
        m8_rlast   = s8_rlast;
        m8_rvalid  = s8_rvalid;
    end
 else if (m8_slave_select[9]) begin
        m8_awready = s9_awready;
        m8_wready  = s9_wready;
        m8_bid     = s9_bid;
        m8_bresp   = s9_bresp;
        m8_bvalid  = s9_bvalid;
        m8_arready = s9_arready;
        m8_rid     = s9_rid;
        m8_rdata   = s9_rdata;
        m8_rresp   = s9_rresp;
        m8_rlast   = s9_rlast;
        m8_rvalid  = s9_rvalid;
    end
 else if (m8_slave_select[10]) begin
        m8_awready = s10_awready;
        m8_wready  = s10_wready;
        m8_bid     = s10_bid;
        m8_bresp   = s10_bresp;
        m8_bvalid  = s10_bvalid;
        m8_arready = s10_arready;
        m8_rid     = s10_rid;
        m8_rdata   = s10_rdata;
        m8_rresp   = s10_rresp;
        m8_rlast   = s10_rlast;
        m8_rvalid  = s10_rvalid;
    end
 else if (m8_slave_select[11]) begin
        m8_awready = s11_awready;
        m8_wready  = s11_wready;
        m8_bid     = s11_bid;
        m8_bresp   = s11_bresp;
        m8_bvalid  = s11_bvalid;
        m8_arready = s11_arready;
        m8_rid     = s11_rid;
        m8_rdata   = s11_rdata;
        m8_rresp   = s11_rresp;
        m8_rlast   = s11_rlast;
        m8_rvalid  = s11_rvalid;
    end
 else if (m8_slave_select[12]) begin
        m8_awready = s12_awready;
        m8_wready  = s12_wready;
        m8_bid     = s12_bid;
        m8_bresp   = s12_bresp;
        m8_bvalid  = s12_bvalid;
        m8_arready = s12_arready;
        m8_rid     = s12_rid;
        m8_rdata   = s12_rdata;
        m8_rresp   = s12_rresp;
        m8_rlast   = s12_rlast;
        m8_rvalid  = s12_rvalid;
    end
 else if (m8_slave_select[13]) begin
        m8_awready = s13_awready;
        m8_wready  = s13_wready;
        m8_bid     = s13_bid;
        m8_bresp   = s13_bresp;
        m8_bvalid  = s13_bvalid;
        m8_arready = s13_arready;
        m8_rid     = s13_rid;
        m8_rdata   = s13_rdata;
        m8_rresp   = s13_rresp;
        m8_rlast   = s13_rlast;
        m8_rvalid  = s13_rvalid;
    end
 else if (m8_slave_select[14]) begin
        m8_awready = s14_awready;
        m8_wready  = s14_wready;
        m8_bid     = s14_bid;
        m8_bresp   = s14_bresp;
        m8_bvalid  = s14_bvalid;
        m8_arready = s14_arready;
        m8_rid     = s14_rid;
        m8_rdata   = s14_rdata;
        m8_rresp   = s14_rresp;
        m8_rlast   = s14_rlast;
        m8_rvalid  = s14_rvalid;
    end

end


// Master 9 response multiplexing
always @(*) begin
    // Default values
    m9_awready = 'b0;
    m9_wready  = 'b0;
    m9_bid     = 'b0;
    m9_bresp   = 'b0;
    m9_bvalid  = 'b0;
    m9_arready = 'b0;
    m9_rid     = 'b0;
    m9_rdata   = 'b0;
    m9_rresp   = 'b0;
    m9_rlast   = 'b0;
    m9_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m9_slave_select[0]) begin
        m9_awready = s0_awready;
        m9_wready  = s0_wready;
        m9_bid     = s0_bid;
        m9_bresp   = s0_bresp;
        m9_bvalid  = s0_bvalid;
        m9_arready = s0_arready;
        m9_rid     = s0_rid;
        m9_rdata   = s0_rdata;
        m9_rresp   = s0_rresp;
        m9_rlast   = s0_rlast;
        m9_rvalid  = s0_rvalid;
    end
 else if (m9_slave_select[1]) begin
        m9_awready = s1_awready;
        m9_wready  = s1_wready;
        m9_bid     = s1_bid;
        m9_bresp   = s1_bresp;
        m9_bvalid  = s1_bvalid;
        m9_arready = s1_arready;
        m9_rid     = s1_rid;
        m9_rdata   = s1_rdata;
        m9_rresp   = s1_rresp;
        m9_rlast   = s1_rlast;
        m9_rvalid  = s1_rvalid;
    end
 else if (m9_slave_select[2]) begin
        m9_awready = s2_awready;
        m9_wready  = s2_wready;
        m9_bid     = s2_bid;
        m9_bresp   = s2_bresp;
        m9_bvalid  = s2_bvalid;
        m9_arready = s2_arready;
        m9_rid     = s2_rid;
        m9_rdata   = s2_rdata;
        m9_rresp   = s2_rresp;
        m9_rlast   = s2_rlast;
        m9_rvalid  = s2_rvalid;
    end
 else if (m9_slave_select[3]) begin
        m9_awready = s3_awready;
        m9_wready  = s3_wready;
        m9_bid     = s3_bid;
        m9_bresp   = s3_bresp;
        m9_bvalid  = s3_bvalid;
        m9_arready = s3_arready;
        m9_rid     = s3_rid;
        m9_rdata   = s3_rdata;
        m9_rresp   = s3_rresp;
        m9_rlast   = s3_rlast;
        m9_rvalid  = s3_rvalid;
    end
 else if (m9_slave_select[4]) begin
        m9_awready = s4_awready;
        m9_wready  = s4_wready;
        m9_bid     = s4_bid;
        m9_bresp   = s4_bresp;
        m9_bvalid  = s4_bvalid;
        m9_arready = s4_arready;
        m9_rid     = s4_rid;
        m9_rdata   = s4_rdata;
        m9_rresp   = s4_rresp;
        m9_rlast   = s4_rlast;
        m9_rvalid  = s4_rvalid;
    end
 else if (m9_slave_select[5]) begin
        m9_awready = s5_awready;
        m9_wready  = s5_wready;
        m9_bid     = s5_bid;
        m9_bresp   = s5_bresp;
        m9_bvalid  = s5_bvalid;
        m9_arready = s5_arready;
        m9_rid     = s5_rid;
        m9_rdata   = s5_rdata;
        m9_rresp   = s5_rresp;
        m9_rlast   = s5_rlast;
        m9_rvalid  = s5_rvalid;
    end
 else if (m9_slave_select[6]) begin
        m9_awready = s6_awready;
        m9_wready  = s6_wready;
        m9_bid     = s6_bid;
        m9_bresp   = s6_bresp;
        m9_bvalid  = s6_bvalid;
        m9_arready = s6_arready;
        m9_rid     = s6_rid;
        m9_rdata   = s6_rdata;
        m9_rresp   = s6_rresp;
        m9_rlast   = s6_rlast;
        m9_rvalid  = s6_rvalid;
    end
 else if (m9_slave_select[7]) begin
        m9_awready = s7_awready;
        m9_wready  = s7_wready;
        m9_bid     = s7_bid;
        m9_bresp   = s7_bresp;
        m9_bvalid  = s7_bvalid;
        m9_arready = s7_arready;
        m9_rid     = s7_rid;
        m9_rdata   = s7_rdata;
        m9_rresp   = s7_rresp;
        m9_rlast   = s7_rlast;
        m9_rvalid  = s7_rvalid;
    end
 else if (m9_slave_select[8]) begin
        m9_awready = s8_awready;
        m9_wready  = s8_wready;
        m9_bid     = s8_bid;
        m9_bresp   = s8_bresp;
        m9_bvalid  = s8_bvalid;
        m9_arready = s8_arready;
        m9_rid     = s8_rid;
        m9_rdata   = s8_rdata;
        m9_rresp   = s8_rresp;
        m9_rlast   = s8_rlast;
        m9_rvalid  = s8_rvalid;
    end
 else if (m9_slave_select[9]) begin
        m9_awready = s9_awready;
        m9_wready  = s9_wready;
        m9_bid     = s9_bid;
        m9_bresp   = s9_bresp;
        m9_bvalid  = s9_bvalid;
        m9_arready = s9_arready;
        m9_rid     = s9_rid;
        m9_rdata   = s9_rdata;
        m9_rresp   = s9_rresp;
        m9_rlast   = s9_rlast;
        m9_rvalid  = s9_rvalid;
    end
 else if (m9_slave_select[10]) begin
        m9_awready = s10_awready;
        m9_wready  = s10_wready;
        m9_bid     = s10_bid;
        m9_bresp   = s10_bresp;
        m9_bvalid  = s10_bvalid;
        m9_arready = s10_arready;
        m9_rid     = s10_rid;
        m9_rdata   = s10_rdata;
        m9_rresp   = s10_rresp;
        m9_rlast   = s10_rlast;
        m9_rvalid  = s10_rvalid;
    end
 else if (m9_slave_select[11]) begin
        m9_awready = s11_awready;
        m9_wready  = s11_wready;
        m9_bid     = s11_bid;
        m9_bresp   = s11_bresp;
        m9_bvalid  = s11_bvalid;
        m9_arready = s11_arready;
        m9_rid     = s11_rid;
        m9_rdata   = s11_rdata;
        m9_rresp   = s11_rresp;
        m9_rlast   = s11_rlast;
        m9_rvalid  = s11_rvalid;
    end
 else if (m9_slave_select[12]) begin
        m9_awready = s12_awready;
        m9_wready  = s12_wready;
        m9_bid     = s12_bid;
        m9_bresp   = s12_bresp;
        m9_bvalid  = s12_bvalid;
        m9_arready = s12_arready;
        m9_rid     = s12_rid;
        m9_rdata   = s12_rdata;
        m9_rresp   = s12_rresp;
        m9_rlast   = s12_rlast;
        m9_rvalid  = s12_rvalid;
    end
 else if (m9_slave_select[13]) begin
        m9_awready = s13_awready;
        m9_wready  = s13_wready;
        m9_bid     = s13_bid;
        m9_bresp   = s13_bresp;
        m9_bvalid  = s13_bvalid;
        m9_arready = s13_arready;
        m9_rid     = s13_rid;
        m9_rdata   = s13_rdata;
        m9_rresp   = s13_rresp;
        m9_rlast   = s13_rlast;
        m9_rvalid  = s13_rvalid;
    end
 else if (m9_slave_select[14]) begin
        m9_awready = s14_awready;
        m9_wready  = s14_wready;
        m9_bid     = s14_bid;
        m9_bresp   = s14_bresp;
        m9_bvalid  = s14_bvalid;
        m9_arready = s14_arready;
        m9_rid     = s14_rid;
        m9_rdata   = s14_rdata;
        m9_rresp   = s14_rresp;
        m9_rlast   = s14_rlast;
        m9_rvalid  = s14_rvalid;
    end

end


// Master 10 response multiplexing
always @(*) begin
    // Default values
    m10_awready = 'b0;
    m10_wready  = 'b0;
    m10_bid     = 'b0;
    m10_bresp   = 'b0;
    m10_bvalid  = 'b0;
    m10_arready = 'b0;
    m10_rid     = 'b0;
    m10_rdata   = 'b0;
    m10_rresp   = 'b0;
    m10_rlast   = 'b0;
    m10_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m10_slave_select[0]) begin
        m10_awready = s0_awready;
        m10_wready  = s0_wready;
        m10_bid     = s0_bid;
        m10_bresp   = s0_bresp;
        m10_bvalid  = s0_bvalid;
        m10_arready = s0_arready;
        m10_rid     = s0_rid;
        m10_rdata   = s0_rdata;
        m10_rresp   = s0_rresp;
        m10_rlast   = s0_rlast;
        m10_rvalid  = s0_rvalid;
    end
 else if (m10_slave_select[1]) begin
        m10_awready = s1_awready;
        m10_wready  = s1_wready;
        m10_bid     = s1_bid;
        m10_bresp   = s1_bresp;
        m10_bvalid  = s1_bvalid;
        m10_arready = s1_arready;
        m10_rid     = s1_rid;
        m10_rdata   = s1_rdata;
        m10_rresp   = s1_rresp;
        m10_rlast   = s1_rlast;
        m10_rvalid  = s1_rvalid;
    end
 else if (m10_slave_select[2]) begin
        m10_awready = s2_awready;
        m10_wready  = s2_wready;
        m10_bid     = s2_bid;
        m10_bresp   = s2_bresp;
        m10_bvalid  = s2_bvalid;
        m10_arready = s2_arready;
        m10_rid     = s2_rid;
        m10_rdata   = s2_rdata;
        m10_rresp   = s2_rresp;
        m10_rlast   = s2_rlast;
        m10_rvalid  = s2_rvalid;
    end
 else if (m10_slave_select[3]) begin
        m10_awready = s3_awready;
        m10_wready  = s3_wready;
        m10_bid     = s3_bid;
        m10_bresp   = s3_bresp;
        m10_bvalid  = s3_bvalid;
        m10_arready = s3_arready;
        m10_rid     = s3_rid;
        m10_rdata   = s3_rdata;
        m10_rresp   = s3_rresp;
        m10_rlast   = s3_rlast;
        m10_rvalid  = s3_rvalid;
    end
 else if (m10_slave_select[4]) begin
        m10_awready = s4_awready;
        m10_wready  = s4_wready;
        m10_bid     = s4_bid;
        m10_bresp   = s4_bresp;
        m10_bvalid  = s4_bvalid;
        m10_arready = s4_arready;
        m10_rid     = s4_rid;
        m10_rdata   = s4_rdata;
        m10_rresp   = s4_rresp;
        m10_rlast   = s4_rlast;
        m10_rvalid  = s4_rvalid;
    end
 else if (m10_slave_select[5]) begin
        m10_awready = s5_awready;
        m10_wready  = s5_wready;
        m10_bid     = s5_bid;
        m10_bresp   = s5_bresp;
        m10_bvalid  = s5_bvalid;
        m10_arready = s5_arready;
        m10_rid     = s5_rid;
        m10_rdata   = s5_rdata;
        m10_rresp   = s5_rresp;
        m10_rlast   = s5_rlast;
        m10_rvalid  = s5_rvalid;
    end
 else if (m10_slave_select[6]) begin
        m10_awready = s6_awready;
        m10_wready  = s6_wready;
        m10_bid     = s6_bid;
        m10_bresp   = s6_bresp;
        m10_bvalid  = s6_bvalid;
        m10_arready = s6_arready;
        m10_rid     = s6_rid;
        m10_rdata   = s6_rdata;
        m10_rresp   = s6_rresp;
        m10_rlast   = s6_rlast;
        m10_rvalid  = s6_rvalid;
    end
 else if (m10_slave_select[7]) begin
        m10_awready = s7_awready;
        m10_wready  = s7_wready;
        m10_bid     = s7_bid;
        m10_bresp   = s7_bresp;
        m10_bvalid  = s7_bvalid;
        m10_arready = s7_arready;
        m10_rid     = s7_rid;
        m10_rdata   = s7_rdata;
        m10_rresp   = s7_rresp;
        m10_rlast   = s7_rlast;
        m10_rvalid  = s7_rvalid;
    end
 else if (m10_slave_select[8]) begin
        m10_awready = s8_awready;
        m10_wready  = s8_wready;
        m10_bid     = s8_bid;
        m10_bresp   = s8_bresp;
        m10_bvalid  = s8_bvalid;
        m10_arready = s8_arready;
        m10_rid     = s8_rid;
        m10_rdata   = s8_rdata;
        m10_rresp   = s8_rresp;
        m10_rlast   = s8_rlast;
        m10_rvalid  = s8_rvalid;
    end
 else if (m10_slave_select[9]) begin
        m10_awready = s9_awready;
        m10_wready  = s9_wready;
        m10_bid     = s9_bid;
        m10_bresp   = s9_bresp;
        m10_bvalid  = s9_bvalid;
        m10_arready = s9_arready;
        m10_rid     = s9_rid;
        m10_rdata   = s9_rdata;
        m10_rresp   = s9_rresp;
        m10_rlast   = s9_rlast;
        m10_rvalid  = s9_rvalid;
    end
 else if (m10_slave_select[10]) begin
        m10_awready = s10_awready;
        m10_wready  = s10_wready;
        m10_bid     = s10_bid;
        m10_bresp   = s10_bresp;
        m10_bvalid  = s10_bvalid;
        m10_arready = s10_arready;
        m10_rid     = s10_rid;
        m10_rdata   = s10_rdata;
        m10_rresp   = s10_rresp;
        m10_rlast   = s10_rlast;
        m10_rvalid  = s10_rvalid;
    end
 else if (m10_slave_select[11]) begin
        m10_awready = s11_awready;
        m10_wready  = s11_wready;
        m10_bid     = s11_bid;
        m10_bresp   = s11_bresp;
        m10_bvalid  = s11_bvalid;
        m10_arready = s11_arready;
        m10_rid     = s11_rid;
        m10_rdata   = s11_rdata;
        m10_rresp   = s11_rresp;
        m10_rlast   = s11_rlast;
        m10_rvalid  = s11_rvalid;
    end
 else if (m10_slave_select[12]) begin
        m10_awready = s12_awready;
        m10_wready  = s12_wready;
        m10_bid     = s12_bid;
        m10_bresp   = s12_bresp;
        m10_bvalid  = s12_bvalid;
        m10_arready = s12_arready;
        m10_rid     = s12_rid;
        m10_rdata   = s12_rdata;
        m10_rresp   = s12_rresp;
        m10_rlast   = s12_rlast;
        m10_rvalid  = s12_rvalid;
    end
 else if (m10_slave_select[13]) begin
        m10_awready = s13_awready;
        m10_wready  = s13_wready;
        m10_bid     = s13_bid;
        m10_bresp   = s13_bresp;
        m10_bvalid  = s13_bvalid;
        m10_arready = s13_arready;
        m10_rid     = s13_rid;
        m10_rdata   = s13_rdata;
        m10_rresp   = s13_rresp;
        m10_rlast   = s13_rlast;
        m10_rvalid  = s13_rvalid;
    end
 else if (m10_slave_select[14]) begin
        m10_awready = s14_awready;
        m10_wready  = s14_wready;
        m10_bid     = s14_bid;
        m10_bresp   = s14_bresp;
        m10_bvalid  = s14_bvalid;
        m10_arready = s14_arready;
        m10_rid     = s14_rid;
        m10_rdata   = s14_rdata;
        m10_rresp   = s14_rresp;
        m10_rlast   = s14_rlast;
        m10_rvalid  = s14_rvalid;
    end

end


// Master 11 response multiplexing
always @(*) begin
    // Default values
    m11_awready = 'b0;
    m11_wready  = 'b0;
    m11_bid     = 'b0;
    m11_bresp   = 'b0;
    m11_bvalid  = 'b0;
    m11_arready = 'b0;
    m11_rid     = 'b0;
    m11_rdata   = 'b0;
    m11_rresp   = 'b0;
    m11_rlast   = 'b0;
    m11_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m11_slave_select[0]) begin
        m11_awready = s0_awready;
        m11_wready  = s0_wready;
        m11_bid     = s0_bid;
        m11_bresp   = s0_bresp;
        m11_bvalid  = s0_bvalid;
        m11_arready = s0_arready;
        m11_rid     = s0_rid;
        m11_rdata   = s0_rdata;
        m11_rresp   = s0_rresp;
        m11_rlast   = s0_rlast;
        m11_rvalid  = s0_rvalid;
    end
 else if (m11_slave_select[1]) begin
        m11_awready = s1_awready;
        m11_wready  = s1_wready;
        m11_bid     = s1_bid;
        m11_bresp   = s1_bresp;
        m11_bvalid  = s1_bvalid;
        m11_arready = s1_arready;
        m11_rid     = s1_rid;
        m11_rdata   = s1_rdata;
        m11_rresp   = s1_rresp;
        m11_rlast   = s1_rlast;
        m11_rvalid  = s1_rvalid;
    end
 else if (m11_slave_select[2]) begin
        m11_awready = s2_awready;
        m11_wready  = s2_wready;
        m11_bid     = s2_bid;
        m11_bresp   = s2_bresp;
        m11_bvalid  = s2_bvalid;
        m11_arready = s2_arready;
        m11_rid     = s2_rid;
        m11_rdata   = s2_rdata;
        m11_rresp   = s2_rresp;
        m11_rlast   = s2_rlast;
        m11_rvalid  = s2_rvalid;
    end
 else if (m11_slave_select[3]) begin
        m11_awready = s3_awready;
        m11_wready  = s3_wready;
        m11_bid     = s3_bid;
        m11_bresp   = s3_bresp;
        m11_bvalid  = s3_bvalid;
        m11_arready = s3_arready;
        m11_rid     = s3_rid;
        m11_rdata   = s3_rdata;
        m11_rresp   = s3_rresp;
        m11_rlast   = s3_rlast;
        m11_rvalid  = s3_rvalid;
    end
 else if (m11_slave_select[4]) begin
        m11_awready = s4_awready;
        m11_wready  = s4_wready;
        m11_bid     = s4_bid;
        m11_bresp   = s4_bresp;
        m11_bvalid  = s4_bvalid;
        m11_arready = s4_arready;
        m11_rid     = s4_rid;
        m11_rdata   = s4_rdata;
        m11_rresp   = s4_rresp;
        m11_rlast   = s4_rlast;
        m11_rvalid  = s4_rvalid;
    end
 else if (m11_slave_select[5]) begin
        m11_awready = s5_awready;
        m11_wready  = s5_wready;
        m11_bid     = s5_bid;
        m11_bresp   = s5_bresp;
        m11_bvalid  = s5_bvalid;
        m11_arready = s5_arready;
        m11_rid     = s5_rid;
        m11_rdata   = s5_rdata;
        m11_rresp   = s5_rresp;
        m11_rlast   = s5_rlast;
        m11_rvalid  = s5_rvalid;
    end
 else if (m11_slave_select[6]) begin
        m11_awready = s6_awready;
        m11_wready  = s6_wready;
        m11_bid     = s6_bid;
        m11_bresp   = s6_bresp;
        m11_bvalid  = s6_bvalid;
        m11_arready = s6_arready;
        m11_rid     = s6_rid;
        m11_rdata   = s6_rdata;
        m11_rresp   = s6_rresp;
        m11_rlast   = s6_rlast;
        m11_rvalid  = s6_rvalid;
    end
 else if (m11_slave_select[7]) begin
        m11_awready = s7_awready;
        m11_wready  = s7_wready;
        m11_bid     = s7_bid;
        m11_bresp   = s7_bresp;
        m11_bvalid  = s7_bvalid;
        m11_arready = s7_arready;
        m11_rid     = s7_rid;
        m11_rdata   = s7_rdata;
        m11_rresp   = s7_rresp;
        m11_rlast   = s7_rlast;
        m11_rvalid  = s7_rvalid;
    end
 else if (m11_slave_select[8]) begin
        m11_awready = s8_awready;
        m11_wready  = s8_wready;
        m11_bid     = s8_bid;
        m11_bresp   = s8_bresp;
        m11_bvalid  = s8_bvalid;
        m11_arready = s8_arready;
        m11_rid     = s8_rid;
        m11_rdata   = s8_rdata;
        m11_rresp   = s8_rresp;
        m11_rlast   = s8_rlast;
        m11_rvalid  = s8_rvalid;
    end
 else if (m11_slave_select[9]) begin
        m11_awready = s9_awready;
        m11_wready  = s9_wready;
        m11_bid     = s9_bid;
        m11_bresp   = s9_bresp;
        m11_bvalid  = s9_bvalid;
        m11_arready = s9_arready;
        m11_rid     = s9_rid;
        m11_rdata   = s9_rdata;
        m11_rresp   = s9_rresp;
        m11_rlast   = s9_rlast;
        m11_rvalid  = s9_rvalid;
    end
 else if (m11_slave_select[10]) begin
        m11_awready = s10_awready;
        m11_wready  = s10_wready;
        m11_bid     = s10_bid;
        m11_bresp   = s10_bresp;
        m11_bvalid  = s10_bvalid;
        m11_arready = s10_arready;
        m11_rid     = s10_rid;
        m11_rdata   = s10_rdata;
        m11_rresp   = s10_rresp;
        m11_rlast   = s10_rlast;
        m11_rvalid  = s10_rvalid;
    end
 else if (m11_slave_select[11]) begin
        m11_awready = s11_awready;
        m11_wready  = s11_wready;
        m11_bid     = s11_bid;
        m11_bresp   = s11_bresp;
        m11_bvalid  = s11_bvalid;
        m11_arready = s11_arready;
        m11_rid     = s11_rid;
        m11_rdata   = s11_rdata;
        m11_rresp   = s11_rresp;
        m11_rlast   = s11_rlast;
        m11_rvalid  = s11_rvalid;
    end
 else if (m11_slave_select[12]) begin
        m11_awready = s12_awready;
        m11_wready  = s12_wready;
        m11_bid     = s12_bid;
        m11_bresp   = s12_bresp;
        m11_bvalid  = s12_bvalid;
        m11_arready = s12_arready;
        m11_rid     = s12_rid;
        m11_rdata   = s12_rdata;
        m11_rresp   = s12_rresp;
        m11_rlast   = s12_rlast;
        m11_rvalid  = s12_rvalid;
    end
 else if (m11_slave_select[13]) begin
        m11_awready = s13_awready;
        m11_wready  = s13_wready;
        m11_bid     = s13_bid;
        m11_bresp   = s13_bresp;
        m11_bvalid  = s13_bvalid;
        m11_arready = s13_arready;
        m11_rid     = s13_rid;
        m11_rdata   = s13_rdata;
        m11_rresp   = s13_rresp;
        m11_rlast   = s13_rlast;
        m11_rvalid  = s13_rvalid;
    end
 else if (m11_slave_select[14]) begin
        m11_awready = s14_awready;
        m11_wready  = s14_wready;
        m11_bid     = s14_bid;
        m11_bresp   = s14_bresp;
        m11_bvalid  = s14_bvalid;
        m11_arready = s14_arready;
        m11_rid     = s14_rid;
        m11_rdata   = s14_rdata;
        m11_rresp   = s14_rresp;
        m11_rlast   = s14_rlast;
        m11_rvalid  = s14_rvalid;
    end

end


// Master 12 response multiplexing
always @(*) begin
    // Default values
    m12_awready = 'b0;
    m12_wready  = 'b0;
    m12_bid     = 'b0;
    m12_bresp   = 'b0;
    m12_bvalid  = 'b0;
    m12_arready = 'b0;
    m12_rid     = 'b0;
    m12_rdata   = 'b0;
    m12_rresp   = 'b0;
    m12_rlast   = 'b0;
    m12_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m12_slave_select[0]) begin
        m12_awready = s0_awready;
        m12_wready  = s0_wready;
        m12_bid     = s0_bid;
        m12_bresp   = s0_bresp;
        m12_bvalid  = s0_bvalid;
        m12_arready = s0_arready;
        m12_rid     = s0_rid;
        m12_rdata   = s0_rdata;
        m12_rresp   = s0_rresp;
        m12_rlast   = s0_rlast;
        m12_rvalid  = s0_rvalid;
    end
 else if (m12_slave_select[1]) begin
        m12_awready = s1_awready;
        m12_wready  = s1_wready;
        m12_bid     = s1_bid;
        m12_bresp   = s1_bresp;
        m12_bvalid  = s1_bvalid;
        m12_arready = s1_arready;
        m12_rid     = s1_rid;
        m12_rdata   = s1_rdata;
        m12_rresp   = s1_rresp;
        m12_rlast   = s1_rlast;
        m12_rvalid  = s1_rvalid;
    end
 else if (m12_slave_select[2]) begin
        m12_awready = s2_awready;
        m12_wready  = s2_wready;
        m12_bid     = s2_bid;
        m12_bresp   = s2_bresp;
        m12_bvalid  = s2_bvalid;
        m12_arready = s2_arready;
        m12_rid     = s2_rid;
        m12_rdata   = s2_rdata;
        m12_rresp   = s2_rresp;
        m12_rlast   = s2_rlast;
        m12_rvalid  = s2_rvalid;
    end
 else if (m12_slave_select[3]) begin
        m12_awready = s3_awready;
        m12_wready  = s3_wready;
        m12_bid     = s3_bid;
        m12_bresp   = s3_bresp;
        m12_bvalid  = s3_bvalid;
        m12_arready = s3_arready;
        m12_rid     = s3_rid;
        m12_rdata   = s3_rdata;
        m12_rresp   = s3_rresp;
        m12_rlast   = s3_rlast;
        m12_rvalid  = s3_rvalid;
    end
 else if (m12_slave_select[4]) begin
        m12_awready = s4_awready;
        m12_wready  = s4_wready;
        m12_bid     = s4_bid;
        m12_bresp   = s4_bresp;
        m12_bvalid  = s4_bvalid;
        m12_arready = s4_arready;
        m12_rid     = s4_rid;
        m12_rdata   = s4_rdata;
        m12_rresp   = s4_rresp;
        m12_rlast   = s4_rlast;
        m12_rvalid  = s4_rvalid;
    end
 else if (m12_slave_select[5]) begin
        m12_awready = s5_awready;
        m12_wready  = s5_wready;
        m12_bid     = s5_bid;
        m12_bresp   = s5_bresp;
        m12_bvalid  = s5_bvalid;
        m12_arready = s5_arready;
        m12_rid     = s5_rid;
        m12_rdata   = s5_rdata;
        m12_rresp   = s5_rresp;
        m12_rlast   = s5_rlast;
        m12_rvalid  = s5_rvalid;
    end
 else if (m12_slave_select[6]) begin
        m12_awready = s6_awready;
        m12_wready  = s6_wready;
        m12_bid     = s6_bid;
        m12_bresp   = s6_bresp;
        m12_bvalid  = s6_bvalid;
        m12_arready = s6_arready;
        m12_rid     = s6_rid;
        m12_rdata   = s6_rdata;
        m12_rresp   = s6_rresp;
        m12_rlast   = s6_rlast;
        m12_rvalid  = s6_rvalid;
    end
 else if (m12_slave_select[7]) begin
        m12_awready = s7_awready;
        m12_wready  = s7_wready;
        m12_bid     = s7_bid;
        m12_bresp   = s7_bresp;
        m12_bvalid  = s7_bvalid;
        m12_arready = s7_arready;
        m12_rid     = s7_rid;
        m12_rdata   = s7_rdata;
        m12_rresp   = s7_rresp;
        m12_rlast   = s7_rlast;
        m12_rvalid  = s7_rvalid;
    end
 else if (m12_slave_select[8]) begin
        m12_awready = s8_awready;
        m12_wready  = s8_wready;
        m12_bid     = s8_bid;
        m12_bresp   = s8_bresp;
        m12_bvalid  = s8_bvalid;
        m12_arready = s8_arready;
        m12_rid     = s8_rid;
        m12_rdata   = s8_rdata;
        m12_rresp   = s8_rresp;
        m12_rlast   = s8_rlast;
        m12_rvalid  = s8_rvalid;
    end
 else if (m12_slave_select[9]) begin
        m12_awready = s9_awready;
        m12_wready  = s9_wready;
        m12_bid     = s9_bid;
        m12_bresp   = s9_bresp;
        m12_bvalid  = s9_bvalid;
        m12_arready = s9_arready;
        m12_rid     = s9_rid;
        m12_rdata   = s9_rdata;
        m12_rresp   = s9_rresp;
        m12_rlast   = s9_rlast;
        m12_rvalid  = s9_rvalid;
    end
 else if (m12_slave_select[10]) begin
        m12_awready = s10_awready;
        m12_wready  = s10_wready;
        m12_bid     = s10_bid;
        m12_bresp   = s10_bresp;
        m12_bvalid  = s10_bvalid;
        m12_arready = s10_arready;
        m12_rid     = s10_rid;
        m12_rdata   = s10_rdata;
        m12_rresp   = s10_rresp;
        m12_rlast   = s10_rlast;
        m12_rvalid  = s10_rvalid;
    end
 else if (m12_slave_select[11]) begin
        m12_awready = s11_awready;
        m12_wready  = s11_wready;
        m12_bid     = s11_bid;
        m12_bresp   = s11_bresp;
        m12_bvalid  = s11_bvalid;
        m12_arready = s11_arready;
        m12_rid     = s11_rid;
        m12_rdata   = s11_rdata;
        m12_rresp   = s11_rresp;
        m12_rlast   = s11_rlast;
        m12_rvalid  = s11_rvalid;
    end
 else if (m12_slave_select[12]) begin
        m12_awready = s12_awready;
        m12_wready  = s12_wready;
        m12_bid     = s12_bid;
        m12_bresp   = s12_bresp;
        m12_bvalid  = s12_bvalid;
        m12_arready = s12_arready;
        m12_rid     = s12_rid;
        m12_rdata   = s12_rdata;
        m12_rresp   = s12_rresp;
        m12_rlast   = s12_rlast;
        m12_rvalid  = s12_rvalid;
    end
 else if (m12_slave_select[13]) begin
        m12_awready = s13_awready;
        m12_wready  = s13_wready;
        m12_bid     = s13_bid;
        m12_bresp   = s13_bresp;
        m12_bvalid  = s13_bvalid;
        m12_arready = s13_arready;
        m12_rid     = s13_rid;
        m12_rdata   = s13_rdata;
        m12_rresp   = s13_rresp;
        m12_rlast   = s13_rlast;
        m12_rvalid  = s13_rvalid;
    end
 else if (m12_slave_select[14]) begin
        m12_awready = s14_awready;
        m12_wready  = s14_wready;
        m12_bid     = s14_bid;
        m12_bresp   = s14_bresp;
        m12_bvalid  = s14_bvalid;
        m12_arready = s14_arready;
        m12_rid     = s14_rid;
        m12_rdata   = s14_rdata;
        m12_rresp   = s14_rresp;
        m12_rlast   = s14_rlast;
        m12_rvalid  = s14_rvalid;
    end

end


// Master 13 response multiplexing
always @(*) begin
    // Default values
    m13_awready = 'b0;
    m13_wready  = 'b0;
    m13_bid     = 'b0;
    m13_bresp   = 'b0;
    m13_bvalid  = 'b0;
    m13_arready = 'b0;
    m13_rid     = 'b0;
    m13_rdata   = 'b0;
    m13_rresp   = 'b0;
    m13_rlast   = 'b0;
    m13_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m13_slave_select[0]) begin
        m13_awready = s0_awready;
        m13_wready  = s0_wready;
        m13_bid     = s0_bid;
        m13_bresp   = s0_bresp;
        m13_bvalid  = s0_bvalid;
        m13_arready = s0_arready;
        m13_rid     = s0_rid;
        m13_rdata   = s0_rdata;
        m13_rresp   = s0_rresp;
        m13_rlast   = s0_rlast;
        m13_rvalid  = s0_rvalid;
    end
 else if (m13_slave_select[1]) begin
        m13_awready = s1_awready;
        m13_wready  = s1_wready;
        m13_bid     = s1_bid;
        m13_bresp   = s1_bresp;
        m13_bvalid  = s1_bvalid;
        m13_arready = s1_arready;
        m13_rid     = s1_rid;
        m13_rdata   = s1_rdata;
        m13_rresp   = s1_rresp;
        m13_rlast   = s1_rlast;
        m13_rvalid  = s1_rvalid;
    end
 else if (m13_slave_select[2]) begin
        m13_awready = s2_awready;
        m13_wready  = s2_wready;
        m13_bid     = s2_bid;
        m13_bresp   = s2_bresp;
        m13_bvalid  = s2_bvalid;
        m13_arready = s2_arready;
        m13_rid     = s2_rid;
        m13_rdata   = s2_rdata;
        m13_rresp   = s2_rresp;
        m13_rlast   = s2_rlast;
        m13_rvalid  = s2_rvalid;
    end
 else if (m13_slave_select[3]) begin
        m13_awready = s3_awready;
        m13_wready  = s3_wready;
        m13_bid     = s3_bid;
        m13_bresp   = s3_bresp;
        m13_bvalid  = s3_bvalid;
        m13_arready = s3_arready;
        m13_rid     = s3_rid;
        m13_rdata   = s3_rdata;
        m13_rresp   = s3_rresp;
        m13_rlast   = s3_rlast;
        m13_rvalid  = s3_rvalid;
    end
 else if (m13_slave_select[4]) begin
        m13_awready = s4_awready;
        m13_wready  = s4_wready;
        m13_bid     = s4_bid;
        m13_bresp   = s4_bresp;
        m13_bvalid  = s4_bvalid;
        m13_arready = s4_arready;
        m13_rid     = s4_rid;
        m13_rdata   = s4_rdata;
        m13_rresp   = s4_rresp;
        m13_rlast   = s4_rlast;
        m13_rvalid  = s4_rvalid;
    end
 else if (m13_slave_select[5]) begin
        m13_awready = s5_awready;
        m13_wready  = s5_wready;
        m13_bid     = s5_bid;
        m13_bresp   = s5_bresp;
        m13_bvalid  = s5_bvalid;
        m13_arready = s5_arready;
        m13_rid     = s5_rid;
        m13_rdata   = s5_rdata;
        m13_rresp   = s5_rresp;
        m13_rlast   = s5_rlast;
        m13_rvalid  = s5_rvalid;
    end
 else if (m13_slave_select[6]) begin
        m13_awready = s6_awready;
        m13_wready  = s6_wready;
        m13_bid     = s6_bid;
        m13_bresp   = s6_bresp;
        m13_bvalid  = s6_bvalid;
        m13_arready = s6_arready;
        m13_rid     = s6_rid;
        m13_rdata   = s6_rdata;
        m13_rresp   = s6_rresp;
        m13_rlast   = s6_rlast;
        m13_rvalid  = s6_rvalid;
    end
 else if (m13_slave_select[7]) begin
        m13_awready = s7_awready;
        m13_wready  = s7_wready;
        m13_bid     = s7_bid;
        m13_bresp   = s7_bresp;
        m13_bvalid  = s7_bvalid;
        m13_arready = s7_arready;
        m13_rid     = s7_rid;
        m13_rdata   = s7_rdata;
        m13_rresp   = s7_rresp;
        m13_rlast   = s7_rlast;
        m13_rvalid  = s7_rvalid;
    end
 else if (m13_slave_select[8]) begin
        m13_awready = s8_awready;
        m13_wready  = s8_wready;
        m13_bid     = s8_bid;
        m13_bresp   = s8_bresp;
        m13_bvalid  = s8_bvalid;
        m13_arready = s8_arready;
        m13_rid     = s8_rid;
        m13_rdata   = s8_rdata;
        m13_rresp   = s8_rresp;
        m13_rlast   = s8_rlast;
        m13_rvalid  = s8_rvalid;
    end
 else if (m13_slave_select[9]) begin
        m13_awready = s9_awready;
        m13_wready  = s9_wready;
        m13_bid     = s9_bid;
        m13_bresp   = s9_bresp;
        m13_bvalid  = s9_bvalid;
        m13_arready = s9_arready;
        m13_rid     = s9_rid;
        m13_rdata   = s9_rdata;
        m13_rresp   = s9_rresp;
        m13_rlast   = s9_rlast;
        m13_rvalid  = s9_rvalid;
    end
 else if (m13_slave_select[10]) begin
        m13_awready = s10_awready;
        m13_wready  = s10_wready;
        m13_bid     = s10_bid;
        m13_bresp   = s10_bresp;
        m13_bvalid  = s10_bvalid;
        m13_arready = s10_arready;
        m13_rid     = s10_rid;
        m13_rdata   = s10_rdata;
        m13_rresp   = s10_rresp;
        m13_rlast   = s10_rlast;
        m13_rvalid  = s10_rvalid;
    end
 else if (m13_slave_select[11]) begin
        m13_awready = s11_awready;
        m13_wready  = s11_wready;
        m13_bid     = s11_bid;
        m13_bresp   = s11_bresp;
        m13_bvalid  = s11_bvalid;
        m13_arready = s11_arready;
        m13_rid     = s11_rid;
        m13_rdata   = s11_rdata;
        m13_rresp   = s11_rresp;
        m13_rlast   = s11_rlast;
        m13_rvalid  = s11_rvalid;
    end
 else if (m13_slave_select[12]) begin
        m13_awready = s12_awready;
        m13_wready  = s12_wready;
        m13_bid     = s12_bid;
        m13_bresp   = s12_bresp;
        m13_bvalid  = s12_bvalid;
        m13_arready = s12_arready;
        m13_rid     = s12_rid;
        m13_rdata   = s12_rdata;
        m13_rresp   = s12_rresp;
        m13_rlast   = s12_rlast;
        m13_rvalid  = s12_rvalid;
    end
 else if (m13_slave_select[13]) begin
        m13_awready = s13_awready;
        m13_wready  = s13_wready;
        m13_bid     = s13_bid;
        m13_bresp   = s13_bresp;
        m13_bvalid  = s13_bvalid;
        m13_arready = s13_arready;
        m13_rid     = s13_rid;
        m13_rdata   = s13_rdata;
        m13_rresp   = s13_rresp;
        m13_rlast   = s13_rlast;
        m13_rvalid  = s13_rvalid;
    end
 else if (m13_slave_select[14]) begin
        m13_awready = s14_awready;
        m13_wready  = s14_wready;
        m13_bid     = s14_bid;
        m13_bresp   = s14_bresp;
        m13_bvalid  = s14_bvalid;
        m13_arready = s14_arready;
        m13_rid     = s14_rid;
        m13_rdata   = s14_rdata;
        m13_rresp   = s14_rresp;
        m13_rlast   = s14_rlast;
        m13_rvalid  = s14_rvalid;
    end

end


// Master 14 response multiplexing
always @(*) begin
    // Default values
    m14_awready = 'b0;
    m14_wready  = 'b0;
    m14_bid     = 'b0;
    m14_bresp   = 'b0;
    m14_bvalid  = 'b0;
    m14_arready = 'b0;
    m14_rid     = 'b0;
    m14_rdata   = 'b0;
    m14_rresp   = 'b0;
    m14_rlast   = 'b0;
    m14_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m14_slave_select[0]) begin
        m14_awready = s0_awready;
        m14_wready  = s0_wready;
        m14_bid     = s0_bid;
        m14_bresp   = s0_bresp;
        m14_bvalid  = s0_bvalid;
        m14_arready = s0_arready;
        m14_rid     = s0_rid;
        m14_rdata   = s0_rdata;
        m14_rresp   = s0_rresp;
        m14_rlast   = s0_rlast;
        m14_rvalid  = s0_rvalid;
    end
 else if (m14_slave_select[1]) begin
        m14_awready = s1_awready;
        m14_wready  = s1_wready;
        m14_bid     = s1_bid;
        m14_bresp   = s1_bresp;
        m14_bvalid  = s1_bvalid;
        m14_arready = s1_arready;
        m14_rid     = s1_rid;
        m14_rdata   = s1_rdata;
        m14_rresp   = s1_rresp;
        m14_rlast   = s1_rlast;
        m14_rvalid  = s1_rvalid;
    end
 else if (m14_slave_select[2]) begin
        m14_awready = s2_awready;
        m14_wready  = s2_wready;
        m14_bid     = s2_bid;
        m14_bresp   = s2_bresp;
        m14_bvalid  = s2_bvalid;
        m14_arready = s2_arready;
        m14_rid     = s2_rid;
        m14_rdata   = s2_rdata;
        m14_rresp   = s2_rresp;
        m14_rlast   = s2_rlast;
        m14_rvalid  = s2_rvalid;
    end
 else if (m14_slave_select[3]) begin
        m14_awready = s3_awready;
        m14_wready  = s3_wready;
        m14_bid     = s3_bid;
        m14_bresp   = s3_bresp;
        m14_bvalid  = s3_bvalid;
        m14_arready = s3_arready;
        m14_rid     = s3_rid;
        m14_rdata   = s3_rdata;
        m14_rresp   = s3_rresp;
        m14_rlast   = s3_rlast;
        m14_rvalid  = s3_rvalid;
    end
 else if (m14_slave_select[4]) begin
        m14_awready = s4_awready;
        m14_wready  = s4_wready;
        m14_bid     = s4_bid;
        m14_bresp   = s4_bresp;
        m14_bvalid  = s4_bvalid;
        m14_arready = s4_arready;
        m14_rid     = s4_rid;
        m14_rdata   = s4_rdata;
        m14_rresp   = s4_rresp;
        m14_rlast   = s4_rlast;
        m14_rvalid  = s4_rvalid;
    end
 else if (m14_slave_select[5]) begin
        m14_awready = s5_awready;
        m14_wready  = s5_wready;
        m14_bid     = s5_bid;
        m14_bresp   = s5_bresp;
        m14_bvalid  = s5_bvalid;
        m14_arready = s5_arready;
        m14_rid     = s5_rid;
        m14_rdata   = s5_rdata;
        m14_rresp   = s5_rresp;
        m14_rlast   = s5_rlast;
        m14_rvalid  = s5_rvalid;
    end
 else if (m14_slave_select[6]) begin
        m14_awready = s6_awready;
        m14_wready  = s6_wready;
        m14_bid     = s6_bid;
        m14_bresp   = s6_bresp;
        m14_bvalid  = s6_bvalid;
        m14_arready = s6_arready;
        m14_rid     = s6_rid;
        m14_rdata   = s6_rdata;
        m14_rresp   = s6_rresp;
        m14_rlast   = s6_rlast;
        m14_rvalid  = s6_rvalid;
    end
 else if (m14_slave_select[7]) begin
        m14_awready = s7_awready;
        m14_wready  = s7_wready;
        m14_bid     = s7_bid;
        m14_bresp   = s7_bresp;
        m14_bvalid  = s7_bvalid;
        m14_arready = s7_arready;
        m14_rid     = s7_rid;
        m14_rdata   = s7_rdata;
        m14_rresp   = s7_rresp;
        m14_rlast   = s7_rlast;
        m14_rvalid  = s7_rvalid;
    end
 else if (m14_slave_select[8]) begin
        m14_awready = s8_awready;
        m14_wready  = s8_wready;
        m14_bid     = s8_bid;
        m14_bresp   = s8_bresp;
        m14_bvalid  = s8_bvalid;
        m14_arready = s8_arready;
        m14_rid     = s8_rid;
        m14_rdata   = s8_rdata;
        m14_rresp   = s8_rresp;
        m14_rlast   = s8_rlast;
        m14_rvalid  = s8_rvalid;
    end
 else if (m14_slave_select[9]) begin
        m14_awready = s9_awready;
        m14_wready  = s9_wready;
        m14_bid     = s9_bid;
        m14_bresp   = s9_bresp;
        m14_bvalid  = s9_bvalid;
        m14_arready = s9_arready;
        m14_rid     = s9_rid;
        m14_rdata   = s9_rdata;
        m14_rresp   = s9_rresp;
        m14_rlast   = s9_rlast;
        m14_rvalid  = s9_rvalid;
    end
 else if (m14_slave_select[10]) begin
        m14_awready = s10_awready;
        m14_wready  = s10_wready;
        m14_bid     = s10_bid;
        m14_bresp   = s10_bresp;
        m14_bvalid  = s10_bvalid;
        m14_arready = s10_arready;
        m14_rid     = s10_rid;
        m14_rdata   = s10_rdata;
        m14_rresp   = s10_rresp;
        m14_rlast   = s10_rlast;
        m14_rvalid  = s10_rvalid;
    end
 else if (m14_slave_select[11]) begin
        m14_awready = s11_awready;
        m14_wready  = s11_wready;
        m14_bid     = s11_bid;
        m14_bresp   = s11_bresp;
        m14_bvalid  = s11_bvalid;
        m14_arready = s11_arready;
        m14_rid     = s11_rid;
        m14_rdata   = s11_rdata;
        m14_rresp   = s11_rresp;
        m14_rlast   = s11_rlast;
        m14_rvalid  = s11_rvalid;
    end
 else if (m14_slave_select[12]) begin
        m14_awready = s12_awready;
        m14_wready  = s12_wready;
        m14_bid     = s12_bid;
        m14_bresp   = s12_bresp;
        m14_bvalid  = s12_bvalid;
        m14_arready = s12_arready;
        m14_rid     = s12_rid;
        m14_rdata   = s12_rdata;
        m14_rresp   = s12_rresp;
        m14_rlast   = s12_rlast;
        m14_rvalid  = s12_rvalid;
    end
 else if (m14_slave_select[13]) begin
        m14_awready = s13_awready;
        m14_wready  = s13_wready;
        m14_bid     = s13_bid;
        m14_bresp   = s13_bresp;
        m14_bvalid  = s13_bvalid;
        m14_arready = s13_arready;
        m14_rid     = s13_rid;
        m14_rdata   = s13_rdata;
        m14_rresp   = s13_rresp;
        m14_rlast   = s13_rlast;
        m14_rvalid  = s13_rvalid;
    end
 else if (m14_slave_select[14]) begin
        m14_awready = s14_awready;
        m14_wready  = s14_wready;
        m14_bid     = s14_bid;
        m14_bresp   = s14_bresp;
        m14_bvalid  = s14_bvalid;
        m14_arready = s14_arready;
        m14_rid     = s14_rid;
        m14_rdata   = s14_rdata;
        m14_rresp   = s14_rresp;
        m14_rlast   = s14_rlast;
        m14_rvalid  = s14_rvalid;
    end

end

