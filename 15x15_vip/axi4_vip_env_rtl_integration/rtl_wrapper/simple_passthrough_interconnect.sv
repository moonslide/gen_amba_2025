//==============================================================================
// Simple Pass-through Interconnect for Testing
// Routes first 3 masters to first 3 slaves with proper ID handling
// This is a simplified interconnect for debugging UVM_ERROR issues
//==============================================================================

module axi4_interconnect_m15s15 #(
    parameter DATA_WIDTH = 256,
    parameter ADDR_WIDTH = 64,
    parameter ID_WIDTH   = 4,
    parameter USER_WIDTH = 1
)(
    input wire aclk,
    input wire aresetn,
    
    // Master 0 interfaces
    input  wire [ID_WIDTH-1:0]    m0_awid,
    input  wire [ADDR_WIDTH-1:0]  m0_awaddr,
    input  wire [7:0]             m0_awlen,
    input  wire [2:0]             m0_awsize,
    input  wire [1:0]             m0_awburst,
    input  wire                   m0_awlock,
    input  wire [3:0]             m0_awcache,
    input  wire [2:0]             m0_awprot,
    input  wire [3:0]             m0_awqos,
    input  wire                   m0_awvalid,
    output reg                    m0_awready,
    
    input  wire [DATA_WIDTH-1:0]  m0_wdata,
    input  wire [DATA_WIDTH/8-1:0] m0_wstrb,
    input  wire                   m0_wlast,
    input  wire                   m0_wvalid,
    output reg                    m0_wready,
    
    output reg  [ID_WIDTH-1:0]    m0_bid,
    output reg  [1:0]             m0_bresp,
    output reg                    m0_bvalid,
    input  wire                   m0_bready,
    
    input  wire [ID_WIDTH-1:0]    m0_arid,
    input  wire [ADDR_WIDTH-1:0]  m0_araddr,
    input  wire [7:0]             m0_arlen,
    input  wire [2:0]             m0_arsize,
    input  wire [1:0]             m0_arburst,
    input  wire                   m0_arlock,
    input  wire [3:0]             m0_arcache,
    input  wire [2:0]             m0_arprot,
    input  wire [3:0]             m0_arqos,
    input  wire                   m0_arvalid,
    output reg                    m0_arready,
    
    output reg  [ID_WIDTH-1:0]    m0_rid,
    output reg  [DATA_WIDTH-1:0]  m0_rdata,
    output reg  [1:0]             m0_rresp,
    output reg                    m0_rlast,
    output reg                    m0_rvalid,
    input  wire                   m0_rready,
    
    // Master 1 interfaces (simplified - just declare ports)
    input  wire [ID_WIDTH-1:0]    m1_awid,
    input  wire [ADDR_WIDTH-1:0]  m1_awaddr,
    input  wire [7:0]             m1_awlen,
    input  wire [2:0]             m1_awsize,
    input  wire [1:0]             m1_awburst,
    input  wire                   m1_awlock,
    input  wire [3:0]             m1_awcache,
    input  wire [2:0]             m1_awprot,
    input  wire [3:0]             m1_awqos,
    input  wire                   m1_awvalid,
    output reg                    m1_awready,
    input  wire [DATA_WIDTH-1:0]  m1_wdata,
    input  wire [DATA_WIDTH/8-1:0] m1_wstrb,
    input  wire                   m1_wlast,
    input  wire                   m1_wvalid,
    output reg                    m1_wready,
    output reg  [ID_WIDTH-1:0]    m1_bid,
    output reg  [1:0]             m1_bresp,
    output reg                    m1_bvalid,
    input  wire                   m1_bready,
    input  wire [ID_WIDTH-1:0]    m1_arid,
    input  wire [ADDR_WIDTH-1:0]  m1_araddr,
    input  wire [7:0]             m1_arlen,
    input  wire [2:0]             m1_arsize,
    input  wire [1:0]             m1_arburst,
    input  wire                   m1_arlock,
    input  wire [3:0]             m1_arcache,
    input  wire [2:0]             m1_arprot,
    input  wire [3:0]             m1_arqos,
    input  wire                   m1_arvalid,
    output reg                    m1_arready,
    output reg  [ID_WIDTH-1:0]    m1_rid,
    output reg  [DATA_WIDTH-1:0]  m1_rdata,
    output reg  [1:0]             m1_rresp,
    output reg                    m1_rlast,
    output reg                    m1_rvalid,
    input  wire                   m1_rready,
    
    // Master 2 interfaces
    input  wire [ID_WIDTH-1:0]    m2_awid,
    input  wire [ADDR_WIDTH-1:0]  m2_awaddr,
    input  wire [7:0]             m2_awlen,
    input  wire [2:0]             m2_awsize,
    input  wire [1:0]             m2_awburst,
    input  wire                   m2_awlock,
    input  wire [3:0]             m2_awcache,
    input  wire [2:0]             m2_awprot,
    input  wire [3:0]             m2_awqos,
    input  wire                   m2_awvalid,
    output reg                    m2_awready,
    input  wire [DATA_WIDTH-1:0]  m2_wdata,
    input  wire [DATA_WIDTH/8-1:0] m2_wstrb,
    input  wire                   m2_wlast,
    input  wire                   m2_wvalid,
    output reg                    m2_wready,
    output reg  [ID_WIDTH-1:0]    m2_bid,
    output reg  [1:0]             m2_bresp,
    output reg                    m2_bvalid,
    input  wire                   m2_bready,
    input  wire [ID_WIDTH-1:0]    m2_arid,
    input  wire [ADDR_WIDTH-1:0]  m2_araddr,
    input  wire [7:0]             m2_arlen,
    input  wire [2:0]             m2_arsize,
    input  wire [1:0]             m2_arburst,
    input  wire                   m2_arlock,
    input  wire [3:0]             m2_arcache,
    input  wire [2:0]             m2_arprot,
    input  wire [3:0]             m2_arqos,
    input  wire                   m2_arvalid,
    output reg                    m2_arready,
    output reg  [ID_WIDTH-1:0]    m2_rid,
    output reg  [DATA_WIDTH-1:0]  m2_rdata,
    output reg  [1:0]             m2_rresp,
    output reg                    m2_rlast,
    output reg                    m2_rvalid,
    input  wire                   m2_rready,
    
    // Declare remaining master ports m3-m14 (stub - not connected)
    input wire m3_awvalid, output reg m3_awready = 0,
    input wire m3_wvalid, output reg m3_wready = 0,
    output reg m3_bvalid = 0, input wire m3_bready,
    input wire m3_arvalid, output reg m3_arready = 0,
    output reg m3_rvalid = 0, input wire m3_rready,
    
    input wire m4_awvalid, output reg m4_awready = 0,
    input wire m4_wvalid, output reg m4_wready = 0,
    output reg m4_bvalid = 0, input wire m4_bready,
    input wire m4_arvalid, output reg m4_arready = 0,
    output reg m4_rvalid = 0, input wire m4_rready,
    
    input wire m5_awvalid, output reg m5_awready = 0,
    input wire m5_wvalid, output reg m5_wready = 0,
    output reg m5_bvalid = 0, input wire m5_bready,
    input wire m5_arvalid, output reg m5_arready = 0,
    output reg m5_rvalid = 0, input wire m5_rready,
    
    input wire m6_awvalid, output reg m6_awready = 0,
    input wire m6_wvalid, output reg m6_wready = 0,
    output reg m6_bvalid = 0, input wire m6_bready,
    input wire m6_arvalid, output reg m6_arready = 0,
    output reg m6_rvalid = 0, input wire m6_rready,
    
    input wire m7_awvalid, output reg m7_awready = 0,
    input wire m7_wvalid, output reg m7_wready = 0,
    output reg m7_bvalid = 0, input wire m7_bready,
    input wire m7_arvalid, output reg m7_arready = 0,
    output reg m7_rvalid = 0, input wire m7_rready,
    
    input wire m8_awvalid, output reg m8_awready = 0,
    input wire m8_wvalid, output reg m8_wready = 0,
    output reg m8_bvalid = 0, input wire m8_bready,
    input wire m8_arvalid, output reg m8_arready = 0,
    output reg m8_rvalid = 0, input wire m8_rready,
    
    input wire m9_awvalid, output reg m9_awready = 0,
    input wire m9_wvalid, output reg m9_wready = 0,
    output reg m9_bvalid = 0, input wire m9_bready,
    input wire m9_arvalid, output reg m9_arready = 0,
    output reg m9_rvalid = 0, input wire m9_rready,
    
    input wire m10_awvalid, output reg m10_awready = 0,
    input wire m10_wvalid, output reg m10_wready = 0,
    output reg m10_bvalid = 0, input wire m10_bready,
    input wire m10_arvalid, output reg m10_arready = 0,
    output reg m10_rvalid = 0, input wire m10_rready,
    
    input wire m11_awvalid, output reg m11_awready = 0,
    input wire m11_wvalid, output reg m11_wready = 0,
    output reg m11_bvalid = 0, input wire m11_bready,
    input wire m11_arvalid, output reg m11_arready = 0,
    output reg m11_rvalid = 0, input wire m11_rready,
    
    input wire m12_awvalid, output reg m12_awready = 0,
    input wire m12_wvalid, output reg m12_wready = 0,
    output reg m12_bvalid = 0, input wire m12_bready,
    input wire m12_arvalid, output reg m12_arready = 0,
    output reg m12_rvalid = 0, input wire m12_rready,
    
    input wire m13_awvalid, output reg m13_awready = 0,
    input wire m13_wvalid, output reg m13_wready = 0,
    output reg m13_bvalid = 0, input wire m13_bready,
    input wire m13_arvalid, output reg m13_arready = 0,
    output reg m13_rvalid = 0, input wire m13_rready,
    
    input wire m14_awvalid, output reg m14_awready = 0,
    input wire m14_wvalid, output reg m14_wready = 0,
    output reg m14_bvalid = 0, input wire m14_bready,
    input wire m14_arvalid, output reg m14_arready = 0,
    output reg m14_rvalid = 0, input wire m14_rready,
    
    // Slave 0 interfaces - connected to all masters
    output reg  [ID_WIDTH-1:0]    s0_awid,
    output reg  [ADDR_WIDTH-1:0]  s0_awaddr,
    output reg  [7:0]             s0_awlen,
    output reg  [2:0]             s0_awsize,
    output reg  [1:0]             s0_awburst,
    output reg                    s0_awlock,
    output reg  [3:0]             s0_awcache,
    output reg  [2:0]             s0_awprot,
    output reg  [3:0]             s0_awqos,
    output reg                    s0_awvalid,
    input  wire                   s0_awready,
    
    output reg  [DATA_WIDTH-1:0]  s0_wdata,
    output reg  [DATA_WIDTH/8-1:0] s0_wstrb,
    output reg                    s0_wlast,
    output reg                    s0_wvalid,
    input  wire                   s0_wready,
    
    input  wire [ID_WIDTH-1:0]    s0_bid,
    input  wire [1:0]             s0_bresp,
    input  wire                   s0_bvalid,
    output reg                    s0_bready,
    
    output reg  [ID_WIDTH-1:0]    s0_arid,
    output reg  [ADDR_WIDTH-1:0]  s0_araddr,
    output reg  [7:0]             s0_arlen,
    output reg  [2:0]             s0_arsize,
    output reg  [1:0]             s0_arburst,
    output reg                    s0_arlock,
    output reg  [3:0]             s0_arcache,
    output reg  [2:0]             s0_arprot,
    output reg  [3:0]             s0_arqos,
    output reg                    s0_arvalid,
    input  wire                   s0_arready,
    
    input  wire [ID_WIDTH-1:0]    s0_rid,
    input  wire [DATA_WIDTH-1:0]  s0_rdata,
    input  wire [1:0]             s0_rresp,
    input  wire                   s0_rlast,
    input  wire                   s0_rvalid,
    output reg                    s0_rready,
    
    // Declare slave ports s1-s14 (stub - not connected) 
    output reg s1_awvalid = 0, input wire s1_awready,
    output reg s1_wvalid = 0, input wire s1_wready,
    input wire s1_bvalid, output reg s1_bready = 1,
    output reg s1_arvalid = 0, input wire s1_arready,
    input wire s1_rvalid, output reg s1_rready = 1,
    
    output reg s2_awvalid = 0, input wire s2_awready,
    output reg s2_wvalid = 0, input wire s2_wready,
    input wire s2_bvalid, output reg s2_bready = 1,
    output reg s2_arvalid = 0, input wire s2_arready,
    input wire s2_rvalid, output reg s2_rready = 1,
    
    output reg s3_awvalid = 0, input wire s3_awready,
    output reg s3_wvalid = 0, input wire s3_wready,
    input wire s3_bvalid, output reg s3_bready = 1,
    output reg s3_arvalid = 0, input wire s3_arready,
    input wire s3_rvalid, output reg s3_rready = 1,
    
    output reg s4_awvalid = 0, input wire s4_awready,
    output reg s4_wvalid = 0, input wire s4_wready,
    input wire s4_bvalid, output reg s4_bready = 1,
    output reg s4_arvalid = 0, input wire s4_arready,
    input wire s4_rvalid, output reg s4_rready = 1,
    
    output reg s5_awvalid = 0, input wire s5_awready,
    output reg s5_wvalid = 0, input wire s5_wready,
    input wire s5_bvalid, output reg s5_bready = 1,
    output reg s5_arvalid = 0, input wire s5_arready,
    input wire s5_rvalid, output reg s5_rready = 1,
    
    output reg s6_awvalid = 0, input wire s6_awready,
    output reg s6_wvalid = 0, input wire s6_wready,
    input wire s6_bvalid, output reg s6_bready = 1,
    output reg s6_arvalid = 0, input wire s6_arready,
    input wire s6_rvalid, output reg s6_rready = 1,
    
    output reg s7_awvalid = 0, input wire s7_awready,
    output reg s7_wvalid = 0, input wire s7_wready,
    input wire s7_bvalid, output reg s7_bready = 1,
    output reg s7_arvalid = 0, input wire s7_arready,
    input wire s7_rvalid, output reg s7_rready = 1,
    
    output reg s8_awvalid = 0, input wire s8_awready,
    output reg s8_wvalid = 0, input wire s8_wready,
    input wire s8_bvalid, output reg s8_bready = 1,
    output reg s8_arvalid = 0, input wire s8_arready,
    input wire s8_rvalid, output reg s8_rready = 1,
    
    output reg s9_awvalid = 0, input wire s9_awready,
    output reg s9_wvalid = 0, input wire s9_wready,
    input wire s9_bvalid, output reg s9_bready = 1,
    output reg s9_arvalid = 0, input wire s9_arready,
    input wire s9_rvalid, output reg s9_rready = 1,
    
    output reg s10_awvalid = 0, input wire s10_awready,
    output reg s10_wvalid = 0, input wire s10_wready,
    input wire s10_bvalid, output reg s10_bready = 1,
    output reg s10_arvalid = 0, input wire s10_arready,
    input wire s10_rvalid, output reg s10_rready = 1,
    
    output reg s11_awvalid = 0, input wire s11_awready,
    output reg s11_wvalid = 0, input wire s11_wready,
    input wire s11_bvalid, output reg s11_bready = 1,
    output reg s11_arvalid = 0, input wire s11_arready,
    input wire s11_rvalid, output reg s11_rready = 1,
    
    output reg s12_awvalid = 0, input wire s12_awready,
    output reg s12_wvalid = 0, input wire s12_wready,
    input wire s12_bvalid, output reg s12_bready = 1,
    output reg s12_arvalid = 0, input wire s12_arready,
    input wire s12_rvalid, output reg s12_rready = 1,
    
    output reg s13_awvalid = 0, input wire s13_awready,
    output reg s13_wvalid = 0, input wire s13_wready,
    input wire s13_bvalid, output reg s13_bready = 1,
    output reg s13_arvalid = 0, input wire s13_arready,
    input wire s13_rvalid, output reg s13_rready = 1,
    
    output reg s14_awvalid = 0, input wire s14_awready,
    output reg s14_wvalid = 0, input wire s14_wready,
    input wire s14_bvalid, output reg s14_bready = 1,
    output reg s14_arvalid = 0, input wire s14_arready,
    input wire s14_rvalid, output reg s14_rready = 1
);

    // Simple round-robin arbitration between first 3 masters
    reg [1:0] current_master;
    reg [1:0] aw_grant, w_grant, b_grant, ar_grant, r_grant;
    
    always @(posedge aclk) begin
        if (!aresetn) begin
            current_master <= 0;
            aw_grant <= 0;
            w_grant <= 0;
            b_grant <= 0;
            ar_grant <= 0;
            r_grant <= 0;
        end else begin
            // Simple time-sliced arbitration
            current_master <= current_master + 1;
            if (current_master > 2) current_master <= 0;
        end
    end
    
    // Route first 3 masters to slave 0 with proper ID preservation
    always @(*) begin
        // Default values
        s0_awid = 0;
        s0_awaddr = 0;
        s0_awlen = 0;
        s0_awsize = 0;
        s0_awburst = 0;
        s0_awlock = 0;
        s0_awcache = 0;
        s0_awprot = 0;
        s0_awqos = 0;
        s0_awvalid = 0;
        
        s0_wdata = 0;
        s0_wstrb = 0;
        s0_wlast = 0;
        s0_wvalid = 0;
        
        s0_bready = 0;
        
        s0_arid = 0;
        s0_araddr = 0;
        s0_arlen = 0;
        s0_arsize = 0;
        s0_arburst = 0;
        s0_arlock = 0;
        s0_arcache = 0;
        s0_arprot = 0;
        s0_arqos = 0;
        s0_arvalid = 0;
        
        s0_rready = 0;
        
        m0_awready = 0;
        m0_wready = 0;
        m0_bid = 0;
        m0_bresp = 0;
        m0_bvalid = 0;
        m0_arready = 0;
        m0_rid = 0;
        m0_rdata = 0;
        m0_rresp = 0;
        m0_rlast = 0;
        m0_rvalid = 0;
        
        m1_awready = 0;
        m1_wready = 0;
        m1_bid = 0;
        m1_bresp = 0;
        m1_bvalid = 0;
        m1_arready = 0;
        m1_rid = 0;
        m1_rdata = 0;
        m1_rresp = 0;
        m1_rlast = 0;
        m1_rvalid = 0;
        
        m2_awready = 0;
        m2_wready = 0;
        m2_bid = 0;
        m2_bresp = 0;
        m2_bvalid = 0;
        m2_arready = 0;
        m2_rid = 0;
        m2_rdata = 0;
        m2_rresp = 0;
        m2_rlast = 0;
        m2_rvalid = 0;
        
        // Route based on current_master with PROPER ID PRESERVATION
        case (current_master)
            0: begin
                // Master 0 to Slave 0
                s0_awid    = m0_awid;    // PRESERVE MASTER ID
                s0_awaddr  = m0_awaddr;
                s0_awlen   = m0_awlen;
                s0_awsize  = m0_awsize;
                s0_awburst = m0_awburst;
                s0_awlock  = m0_awlock;
                s0_awcache = m0_awcache;
                s0_awprot  = m0_awprot;
                s0_awqos   = m0_awqos;
                s0_awvalid = m0_awvalid;
                m0_awready = s0_awready;
                
                s0_wdata   = m0_wdata;
                s0_wstrb   = m0_wstrb;
                s0_wlast   = m0_wlast;
                s0_wvalid  = m0_wvalid;
                m0_wready  = s0_wready;
                
                m0_bid     = s0_bid;     // PASS BACK SLAVE RESPONSE ID
                m0_bresp   = s0_bresp;
                m0_bvalid  = s0_bvalid;
                s0_bready  = m0_bready;
                
                s0_arid    = m0_arid;    // PRESERVE MASTER ID
                s0_araddr  = m0_araddr;
                s0_arlen   = m0_arlen;
                s0_arsize  = m0_arsize;
                s0_arburst = m0_arburst;
                s0_arlock  = m0_arlock;
                s0_arcache = m0_arcache;
                s0_arprot  = m0_arprot;
                s0_arqos   = m0_arqos;
                s0_arvalid = m0_arvalid;
                m0_arready = s0_arready;
                
                m0_rid     = s0_rid;     // PASS BACK SLAVE RESPONSE ID
                m0_rdata   = s0_rdata;
                m0_rresp   = s0_rresp;
                m0_rlast   = s0_rlast;
                m0_rvalid  = s0_rvalid;
                s0_rready  = m0_rready;
            end
            
            1: begin
                // Master 1 to Slave 0
                s0_awid    = m1_awid;    // PRESERVE MASTER ID
                s0_awaddr  = m1_awaddr;
                s0_awlen   = m1_awlen;
                s0_awsize  = m1_awsize;
                s0_awburst = m1_awburst;
                s0_awlock  = m1_awlock;
                s0_awcache = m1_awcache;
                s0_awprot  = m1_awprot;
                s0_awqos   = m1_awqos;
                s0_awvalid = m1_awvalid;
                m1_awready = s0_awready;
                
                s0_wdata   = m1_wdata;
                s0_wstrb   = m1_wstrb;
                s0_wlast   = m1_wlast;
                s0_wvalid  = m1_wvalid;
                m1_wready  = s0_wready;
                
                m1_bid     = s0_bid;     // PASS BACK SLAVE RESPONSE ID
                m1_bresp   = s0_bresp;
                m1_bvalid  = s0_bvalid;
                s0_bready  = m1_bready;
                
                s0_arid    = m1_arid;    // PRESERVE MASTER ID
                s0_araddr  = m1_araddr;
                s0_arlen   = m1_arlen;
                s0_arsize  = m1_arsize;
                s0_arburst = m1_arburst;
                s0_arlock  = m1_arlock;
                s0_arcache = m1_arcache;
                s0_arprot  = m1_arprot;
                s0_arqos   = m1_arqos;
                s0_arvalid = m1_arvalid;
                m1_arready = s0_arready;
                
                m1_rid     = s0_rid;     // PASS BACK SLAVE RESPONSE ID
                m1_rdata   = s0_rdata;
                m1_rresp   = s0_rresp;
                m1_rlast   = s0_rlast;
                m1_rvalid  = s0_rvalid;
                s0_rready  = m1_rready;
            end
            
            2: begin
                // Master 2 to Slave 0
                s0_awid    = m2_awid;    // PRESERVE MASTER ID
                s0_awaddr  = m2_awaddr;
                s0_awlen   = m2_awlen;
                s0_awsize  = m2_awsize;
                s0_awburst = m2_awburst;
                s0_awlock  = m2_awlock;
                s0_awcache = m2_awcache;
                s0_awprot  = m2_awprot;
                s0_awqos   = m2_awqos;
                s0_awvalid = m2_awvalid;
                m2_awready = s0_awready;
                
                s0_wdata   = m2_wdata;
                s0_wstrb   = m2_wstrb;
                s0_wlast   = m2_wlast;
                s0_wvalid  = m2_wvalid;
                m2_wready  = s0_wready;
                
                m2_bid     = s0_bid;     // PASS BACK SLAVE RESPONSE ID
                m2_bresp   = s0_bresp;
                m2_bvalid  = s0_bvalid;
                s0_bready  = m2_bready;
                
                s0_arid    = m2_arid;    // PRESERVE MASTER ID
                s0_araddr  = m2_araddr;
                s0_arlen   = m2_arlen;
                s0_arsize  = m2_arsize;
                s0_arburst = m2_arburst;
                s0_arlock  = m2_arlock;
                s0_arcache = m2_arcache;
                s0_arprot  = m2_arprot;
                s0_arqos   = m2_arqos;
                s0_arvalid = m2_arvalid;
                m2_arready = s0_arready;
                
                m2_rid     = s0_rid;     // PASS BACK SLAVE RESPONSE ID
                m2_rdata   = s0_rdata;
                m2_rresp   = s0_rresp;
                m2_rlast   = s0_rlast;
                m2_rvalid  = s0_rvalid;
                s0_rready  = m2_rready;
            end
        endcase
    end
    
    initial begin
        $display("[%0t] Simple Pass-through Interconnect: Initialized", $time);
        $display("[%0t] Routes M0/M1/M2 to S0 with proper ID preservation", $time);
    end

endmodule