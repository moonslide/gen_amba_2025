//==============================================================================
// AXI4 Master BFM Connector
// Connects BFM signals to AXI interface
//==============================================================================

module axi4_master_bfm_connector #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH   = 4
)(
    // BFM interface
    axi4_master_agent_bfm bfm,
    // AXI interface
    axi4_if.master axi
);

    // Connect Write Address Channel
    assign axi.awid     = bfm.master_driver_bfm_h.awid;
    assign axi.awaddr   = bfm.master_driver_bfm_h.awaddr;
    assign axi.awlen    = bfm.master_driver_bfm_h.awlen;
    assign axi.awsize   = bfm.master_driver_bfm_h.awsize;
    assign axi.awburst  = bfm.master_driver_bfm_h.awburst;
    assign axi.awlock   = bfm.master_driver_bfm_h.awlock;
    assign axi.awcache  = bfm.master_driver_bfm_h.awcache;
    assign axi.awprot   = bfm.master_driver_bfm_h.awprot;
    assign axi.awqos    = bfm.master_driver_bfm_h.awqos;
    assign axi.awregion = bfm.master_driver_bfm_h.awregion;
    assign axi.awvalid  = bfm.master_driver_bfm_h.awvalid;
    assign bfm.master_driver_bfm_h.awready = axi.awready;
    
    // Connect Write Data Channel
    assign axi.wdata    = bfm.master_driver_bfm_h.wdata;
    assign axi.wstrb    = bfm.master_driver_bfm_h.wstrb;
    assign axi.wlast    = bfm.master_driver_bfm_h.wlast;
    assign axi.wvalid   = bfm.master_driver_bfm_h.wvalid;
    assign bfm.master_driver_bfm_h.wready = axi.wready;
    
    // Connect Write Response Channel
    assign bfm.master_driver_bfm_h.bid    = axi.bid;
    assign bfm.master_driver_bfm_h.bresp  = axi.bresp;
    assign bfm.master_driver_bfm_h.bvalid = axi.bvalid;
    assign axi.bready = bfm.master_driver_bfm_h.bready;
    
    // Connect Read Address Channel
    assign axi.arid     = bfm.master_driver_bfm_h.arid;
    assign axi.araddr   = bfm.master_driver_bfm_h.araddr;
    assign axi.arlen    = bfm.master_driver_bfm_h.arlen;
    assign axi.arsize   = bfm.master_driver_bfm_h.arsize;
    assign axi.arburst  = bfm.master_driver_bfm_h.arburst;
    assign axi.arlock   = bfm.master_driver_bfm_h.arlock;
    assign axi.arcache  = bfm.master_driver_bfm_h.arcache;
    assign axi.arprot   = bfm.master_driver_bfm_h.arprot;
    assign axi.arqos    = bfm.master_driver_bfm_h.arqos;
    assign axi.arregion = bfm.master_driver_bfm_h.arregion;
    assign axi.arvalid  = bfm.master_driver_bfm_h.arvalid;
    assign bfm.master_driver_bfm_h.arready = axi.arready;
    
    // Connect Read Data Channel
    assign bfm.master_driver_bfm_h.rid    = axi.rid;
    assign bfm.master_driver_bfm_h.rdata  = axi.rdata;
    assign bfm.master_driver_bfm_h.rresp  = axi.rresp;
    assign bfm.master_driver_bfm_h.rlast  = axi.rlast;
    assign bfm.master_driver_bfm_h.rvalid = axi.rvalid;
    assign axi.rready = bfm.master_driver_bfm_h.rready;
    
    // Connect monitor BFM to same signals
    assign bfm.master_monitor_bfm_h.awid     = axi.awid;
    assign bfm.master_monitor_bfm_h.awaddr   = axi.awaddr;
    assign bfm.master_monitor_bfm_h.awlen    = axi.awlen;
    assign bfm.master_monitor_bfm_h.awsize   = axi.awsize;
    assign bfm.master_monitor_bfm_h.awburst  = axi.awburst;
    assign bfm.master_monitor_bfm_h.awlock   = axi.awlock;
    assign bfm.master_monitor_bfm_h.awcache  = axi.awcache;
    assign bfm.master_monitor_bfm_h.awprot   = axi.awprot;
    assign bfm.master_monitor_bfm_h.awqos    = axi.awqos;
    assign bfm.master_monitor_bfm_h.awregion = axi.awregion;
    assign bfm.master_monitor_bfm_h.awvalid  = axi.awvalid;
    assign bfm.master_monitor_bfm_h.awready  = axi.awready;
    
    assign bfm.master_monitor_bfm_h.wdata    = axi.wdata;
    assign bfm.master_monitor_bfm_h.wstrb    = axi.wstrb;
    assign bfm.master_monitor_bfm_h.wlast    = axi.wlast;
    assign bfm.master_monitor_bfm_h.wvalid   = axi.wvalid;
    assign bfm.master_monitor_bfm_h.wready   = axi.wready;
    
    assign bfm.master_monitor_bfm_h.bid      = axi.bid;
    assign bfm.master_monitor_bfm_h.bresp    = axi.bresp;
    assign bfm.master_monitor_bfm_h.bvalid   = axi.bvalid;
    assign bfm.master_monitor_bfm_h.bready   = axi.bready;
    
    assign bfm.master_monitor_bfm_h.arid     = axi.arid;
    assign bfm.master_monitor_bfm_h.araddr   = axi.araddr;
    assign bfm.master_monitor_bfm_h.arlen    = axi.arlen;
    assign bfm.master_monitor_bfm_h.arsize   = axi.arsize;
    assign bfm.master_monitor_bfm_h.arburst  = axi.arburst;
    assign bfm.master_monitor_bfm_h.arlock   = axi.arlock;
    assign bfm.master_monitor_bfm_h.arcache  = axi.arcache;
    assign bfm.master_monitor_bfm_h.arprot   = axi.arprot;
    assign bfm.master_monitor_bfm_h.arqos    = axi.arqos;
    assign bfm.master_monitor_bfm_h.arregion = axi.arregion;
    assign bfm.master_monitor_bfm_h.arvalid  = axi.arvalid;
    assign bfm.master_monitor_bfm_h.arready  = axi.arready;
    
    assign bfm.master_monitor_bfm_h.rid      = axi.rid;
    assign bfm.master_monitor_bfm_h.rdata    = axi.rdata;
    assign bfm.master_monitor_bfm_h.rresp    = axi.rresp;
    assign bfm.master_monitor_bfm_h.rlast    = axi.rlast;
    assign bfm.master_monitor_bfm_h.rvalid   = axi.rvalid;
    assign bfm.master_monitor_bfm_h.rready   = axi.rready;
    
    // Debug logging
    always @(posedge axi.aclk) begin
        if (axi.awvalid && axi.awready) begin
            $display("[%0t] BFM_CONNECTOR: Write address handshake - addr=0x%0h", $time, axi.awaddr);
        end
        if (axi.wvalid && axi.wready) begin
            $display("[%0t] BFM_CONNECTOR: Write data handshake - data=0x%0h", $time, axi.wdata);
        end
        if (axi.arvalid && axi.arready) begin
            $display("[%0t] BFM_CONNECTOR: Read address handshake - addr=0x%0h", $time, axi.araddr);
        end
        if (axi.rvalid && axi.rready) begin
            $display("[%0t] BFM_CONNECTOR: Read data handshake - data=0x%0h", $time, axi.rdata);
        end
        
        // Monitor ready signals
        if (axi.awvalid && !axi.awready) begin
            $display("[%0t] BFM_CONNECTOR: Waiting for AWREADY (awvalid=%b, awready=%b)", $time, axi.awvalid, axi.awready);
        end
    end
    
    // Debug initial state
    initial begin
        #1;
        $display("[%0t] BFM_CONNECTOR: Initial state - aresetn=%b", $time, axi.aresetn);
    end

endmodule : axi4_master_bfm_connector