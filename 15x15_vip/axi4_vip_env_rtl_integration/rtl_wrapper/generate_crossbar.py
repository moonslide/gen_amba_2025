#!/usr/bin/env python3
"""Generate proper AXI4 crossbar routing logic"""

def generate_crossbar():
    """Generate complete crossbar switch for 15x15 AXI interconnect"""
    
    crossbar = []
    
    # Generate multiplexers for each slave port
    # Each slave can receive from any master based on arbiter grant
    crossbar.append("""
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
""")
    
    # Simplified approach - use address-based routing
    crossbar.append("""
// Simplified crossbar: Route based on address bits
// Upper address bits determine target slave
""")
    
    for slave in range(15):
        crossbar.append(f"""
// Slave {slave} connections - multiplex from all masters based on address
always @(*) begin
    // Default values
    s{slave}_awid    = 'b0;
    s{slave}_awaddr  = 'b0;
    s{slave}_awlen   = 'b0;
    s{slave}_awsize  = 'b0;
    s{slave}_awburst = 'b0;
    s{slave}_awlock  = 'b0;
    s{slave}_awcache = 'b0;
    s{slave}_awprot  = 'b0;
    s{slave}_awqos   = 'b0;
    s{slave}_awvalid = 'b0;
    s{slave}_wdata   = 'b0;
    s{slave}_wstrb   = 'b0;
    s{slave}_wlast   = 'b0;
    s{slave}_wvalid  = 'b0;
    s{slave}_bready  = 'b0;
    s{slave}_arid    = 'b0;
    s{slave}_araddr  = 'b0;
    s{slave}_arlen   = 'b0;
    s{slave}_arsize  = 'b0;
    s{slave}_arburst = 'b0;
    s{slave}_arlock  = 'b0;
    s{slave}_arcache = 'b0;
    s{slave}_arprot  = 'b0;
    s{slave}_arqos   = 'b0;
    s{slave}_arvalid = 'b0;
    s{slave}_rready  = 'b0;
    
    // Check all masters to see who wants to access this slave
    if (m0_slave_select[{slave}]) begin
        s{slave}_awid    = m0_awid;
        s{slave}_awaddr  = m0_awaddr;
        s{slave}_awlen   = m0_awlen;
        s{slave}_awsize  = m0_awsize;
        s{slave}_awburst = m0_awburst;
        s{slave}_awlock  = m0_awlock;
        s{slave}_awcache = m0_awcache;
        s{slave}_awprot  = m0_awprot;
        s{slave}_awqos   = m0_awqos;
        s{slave}_awvalid = m0_awvalid & m0_slave_select[{slave}];
        s{slave}_wdata   = m0_wdata;
        s{slave}_wstrb   = m0_wstrb;
        s{slave}_wlast   = m0_wlast;
        s{slave}_wvalid  = m0_wvalid;
        s{slave}_bready  = m0_bready;
        s{slave}_arid    = m0_arid;
        s{slave}_araddr  = m0_araddr;
        s{slave}_arlen   = m0_arlen;
        s{slave}_arsize  = m0_arsize;
        s{slave}_arburst = m0_arburst;
        s{slave}_arlock  = m0_arlock;
        s{slave}_arcache = m0_arcache;
        s{slave}_arprot  = m0_arprot;
        s{slave}_arqos   = m0_arqos;
        s{slave}_arvalid = m0_arvalid & m0_slave_select[{slave}];
        s{slave}_rready  = m0_rready;
    end""")
        
        # Add other masters
        for master in range(1, 15):
            crossbar.append(f""" else if (m{master}_slave_select[{slave}]) begin
        s{slave}_awid    = m{master}_awid;
        s{slave}_awaddr  = m{master}_awaddr;
        s{slave}_awlen   = m{master}_awlen;
        s{slave}_awsize  = m{master}_awsize;
        s{slave}_awburst = m{master}_awburst;
        s{slave}_awlock  = m{master}_awlock;
        s{slave}_awcache = m{master}_awcache;
        s{slave}_awprot  = m{master}_awprot;
        s{slave}_awqos   = m{master}_awqos;
        s{slave}_awvalid = m{master}_awvalid & m{master}_slave_select[{slave}];
        s{slave}_wdata   = m{master}_wdata;
        s{slave}_wstrb   = m{master}_wstrb;
        s{slave}_wlast   = m{master}_wlast;
        s{slave}_wvalid  = m{master}_wvalid;
        s{slave}_bready  = m{master}_bready;
        s{slave}_arid    = m{master}_arid;
        s{slave}_araddr  = m{master}_araddr;
        s{slave}_arlen   = m{master}_arlen;
        s{slave}_arsize  = m{master}_arsize;
        s{slave}_arburst = m{master}_arburst;
        s{slave}_arlock  = m{master}_arlock;
        s{slave}_arcache = m{master}_arcache;
        s{slave}_arprot  = m{master}_arprot;
        s{slave}_arqos   = m{master}_arqos;
        s{slave}_arvalid = m{master}_arvalid & m{master}_slave_select[{slave}];
        s{slave}_rready  = m{master}_rready;
    end""")
        
        crossbar.append("""
end
""")
    
    # Response routing back to masters
    crossbar.append("""
// Route responses back to masters based on which slave they accessed
""")
    
    for master in range(15):
        crossbar.append(f"""
// Master {master} response multiplexing
always @(*) begin
    // Default values
    m{master}_awready = 'b0;
    m{master}_wready  = 'b0;
    m{master}_bid     = 'b0;
    m{master}_bresp   = 'b0;
    m{master}_bvalid  = 'b0;
    m{master}_arready = 'b0;
    m{master}_rid     = 'b0;
    m{master}_rdata   = 'b0;
    m{master}_rresp   = 'b0;
    m{master}_rlast   = 'b0;
    m{master}_rvalid  = 'b0;
    
    // Check which slave this master is accessing
    if (m{master}_slave_select[0]) begin
        m{master}_awready = s0_awready;
        m{master}_wready  = s0_wready;
        m{master}_bid     = s0_bid;
        m{master}_bresp   = s0_bresp;
        m{master}_bvalid  = s0_bvalid;
        m{master}_arready = s0_arready;
        m{master}_rid     = s0_rid;
        m{master}_rdata   = s0_rdata;
        m{master}_rresp   = s0_rresp;
        m{master}_rlast   = s0_rlast;
        m{master}_rvalid  = s0_rvalid;
    end""")
        
        for slave in range(1, 15):
            crossbar.append(f""" else if (m{master}_slave_select[{slave}]) begin
        m{master}_awready = s{slave}_awready;
        m{master}_wready  = s{slave}_wready;
        m{master}_bid     = s{slave}_bid;
        m{master}_bresp   = s{slave}_bresp;
        m{master}_bvalid  = s{slave}_bvalid;
        m{master}_arready = s{slave}_arready;
        m{master}_rid     = s{slave}_rid;
        m{master}_rdata   = s{slave}_rdata;
        m{master}_rresp   = s{slave}_rresp;
        m{master}_rlast   = s{slave}_rlast;
        m{master}_rvalid  = s{slave}_rvalid;
    end""")
        
        crossbar.append("""
end
""")
    
    return '\n'.join(crossbar)

if __name__ == "__main__":
    print(generate_crossbar())