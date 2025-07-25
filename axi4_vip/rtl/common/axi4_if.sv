//==============================================================================
// AXI4 Interface Definition
// 
// Description: SystemVerilog interface for AXI4 protocol
// Based on ARM IHI 0022D AMBA AXI Protocol Specification
//==============================================================================

`include "axi4_defines.sv"

interface axi4_if #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64,
    parameter int ID_WIDTH   = 4,
    parameter int AWUSER_WIDTH = 0,
    parameter int WUSER_WIDTH  = 0,
    parameter int BUSER_WIDTH  = 0,
    parameter int ARUSER_WIDTH = 0,
    parameter int RUSER_WIDTH  = 0
)(
    input logic aclk,
    input logic aresetn
);

    // Calculate derived parameters
    localparam int STRB_WIDTH = DATA_WIDTH / 8;
    
    // Write Address Channel
    logic [ID_WIDTH-1:0]      awid;
    logic [ADDR_WIDTH-1:0]    awaddr;
    logic [7:0]               awlen;
    logic [2:0]               awsize;
    logic [1:0]               awburst;
    logic                     awlock;
    logic [3:0]               awcache;
    logic [2:0]               awprot;
    logic [3:0]               awqos;
    logic [3:0]               awregion;
    logic [AWUSER_WIDTH-1:0]  awuser;
    logic                     awvalid;
    logic                     awready;
    
    // Write Data Channel
    logic [DATA_WIDTH-1:0]    wdata;
    logic [STRB_WIDTH-1:0]    wstrb;
    logic                     wlast;
    logic [WUSER_WIDTH-1:0]   wuser;
    logic                     wvalid;
    logic                     wready;
    
    // Write Response Channel
    logic [ID_WIDTH-1:0]      bid;
    logic [1:0]               bresp;
    logic [BUSER_WIDTH-1:0]   buser;
    logic                     bvalid;
    logic                     bready;
    
    // Read Address Channel
    logic [ID_WIDTH-1:0]      arid;
    logic [ADDR_WIDTH-1:0]    araddr;
    logic [7:0]               arlen;
    logic [2:0]               arsize;
    logic [1:0]               arburst;
    logic                     arlock;
    logic [3:0]               arcache;
    logic [2:0]               arprot;
    logic [3:0]               arqos;
    logic [3:0]               arregion;
    logic [ARUSER_WIDTH-1:0]  aruser;
    logic                     arvalid;
    logic                     arready;
    
    // Read Data Channel
    logic [ID_WIDTH-1:0]      rid;
    logic [DATA_WIDTH-1:0]    rdata;
    logic [1:0]               rresp;
    logic                     rlast;
    logic [RUSER_WIDTH-1:0]   ruser;
    logic                     rvalid;
    logic                     rready;
    
    // Modports for different component connections
    modport master (
        output awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid,
        input  awready,
        output wdata, wstrb, wlast, wuser, wvalid,
        input  wready,
        input  bid, bresp, buser, bvalid,
        output bready,
        output arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser, arvalid,
        input  arready,
        input  rid, rdata, rresp, rlast, ruser, rvalid,
        output rready,
        input  aclk, aresetn
    );
    
    modport slave (
        input  awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid,
        output awready,
        input  wdata, wstrb, wlast, wuser, wvalid,
        output wready,
        output bid, bresp, buser, bvalid,
        input  bready,
        input  arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser, arvalid,
        output arready,
        output rid, rdata, rresp, rlast, ruser, rvalid,
        input  rready,
        input  aclk, aresetn
    );
    
    modport monitor (
        input awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid, awready,
        input wdata, wstrb, wlast, wuser, wvalid, wready,
        input bid, bresp, buser, bvalid, bready,
        input arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser, arvalid, arready,
        input rid, rdata, rresp, rlast, ruser, rvalid, rready,
        input aclk, aresetn
    );
    
    // Assertions for protocol checking
    `ifdef AXI4_PROTOCOL_CHECK
    
    // Valid signal stability check
    property valid_stable(valid, ready);
        @(posedge aclk) disable iff (!aresetn)
        valid && !ready |=> valid;
    endproperty
    
    assert property (valid_stable(awvalid, awready)) 
        else $error("AXI4: AWVALID not stable");
    assert property (valid_stable(wvalid, wready)) 
        else $error("AXI4: WVALID not stable");
    assert property (valid_stable(arvalid, arready)) 
        else $error("AXI4: ARVALID not stable");
    assert property (valid_stable(bvalid, bready)) 
        else $error("AXI4: BVALID not stable");
    assert property (valid_stable(rvalid, rready)) 
        else $error("AXI4: RVALID not stable");
    
    // Exclusive access alignment check
    property exclusive_aligned;
        @(posedge aclk) disable iff (!aresetn)
        (awvalid && awlock == AXI4_LOCK_EXCLUSIVE) |->
        (awaddr[2:0] == 3'b000 && awsize == 3'b011) ||  // 8-byte aligned
        (awaddr[3:0] == 4'b0000 && awsize == 3'b100) || // 16-byte aligned
        (awaddr[4:0] == 5'b00000 && awsize == 3'b101) ||// 32-byte aligned
        (awaddr[5:0] == 6'b000000 && awsize == 3'b110) ||// 64-byte aligned
        (awaddr[6:0] == 7'b0000000 && awsize == 3'b111); // 128-byte aligned
    endproperty
    
    assert property (exclusive_aligned) 
        else $error("AXI4: Exclusive access not properly aligned");
    
    // 4KB boundary check
    property no_4kb_cross_aw;
        @(posedge aclk) disable iff (!aresetn)
        awvalid |-> !axi4_crosses_4kb(awaddr, awlen + 1, awsize);
    endproperty
    
    property no_4kb_cross_ar;
        @(posedge aclk) disable iff (!aresetn)
        arvalid |-> !axi4_crosses_4kb(araddr, arlen + 1, arsize);
    endproperty
    
    assert property (no_4kb_cross_aw) 
        else $error("AXI4: Write burst crosses 4KB boundary");
    assert property (no_4kb_cross_ar) 
        else $error("AXI4: Read burst crosses 4KB boundary");
    
    // WRAP burst length check
    property wrap_len_valid(logic [7:0] len, logic [1:0] burst);
        @(posedge aclk) disable iff (!aresetn)
        (burst == AXI4_BURST_WRAP) |-> 
        (len == 1 || len == 3 || len == 7 || len == 15);
    endproperty
    
    assert property (awvalid |-> wrap_len_valid(awlen, awburst))
        else $error("AXI4: Invalid WRAP burst length on write");
    assert property (arvalid |-> wrap_len_valid(arlen, arburst))
        else $error("AXI4: Invalid WRAP burst length on read");
    
    `endif // AXI4_PROTOCOL_CHECK
    
    // Debug tasks
    task display_write_addr();
        $display("[%t] AW: ID=%0h ADDR=%0h LEN=%0d SIZE=%0d BURST=%0s", 
            $time, awid, awaddr, awlen+1, awsize, 
            awburst == 0 ? "FIXED" : awburst == 1 ? "INCR" : "WRAP");
    endtask
    
    task display_read_addr();
        $display("[%t] AR: ID=%0h ADDR=%0h LEN=%0d SIZE=%0d BURST=%0s", 
            $time, arid, araddr, arlen+1, arsize,
            arburst == 0 ? "FIXED" : arburst == 1 ? "INCR" : "WRAP");
    endtask
    
endinterface : axi4_if