//==============================================================================
// AXI4 Master Monitor BFM - Enhanced with comprehensive logging
// Bus Functional Model for monitoring AXI4 master transactions
// Date: 2025-08-03 23:14:02
//==============================================================================

interface axi4_master_monitor_bfm #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH   = 4
)(
    input aclk,
    input aresetn
);

    import axi4_globals_pkg::*;
    
    // Write Address Channel (monitoring)
    logic [ID_WIDTH-1:0]    awid;
    logic [ADDR_WIDTH-1:0]  awaddr;
    logic [7:0]             awlen;
    logic [2:0]             awsize;
    logic [1:0]             awburst;
    logic                   awlock;
    logic [3:0]             awcache;
    logic [2:0]             awprot;
    logic [3:0]             awqos;
    logic [3:0]             awregion;
    logic                   awvalid;
    logic                   awready;
    
    // Write Data Channel (monitoring)
    logic [DATA_WIDTH-1:0]  wdata;
    logic [(DATA_WIDTH/8)-1:0] wstrb;
    logic                   wlast;
    logic                   wvalid;
    logic                   wready;
    
    // Write Response Channel (monitoring)
    logic [ID_WIDTH-1:0]    bid;
    logic [1:0]             bresp;
    logic                   bvalid;
    logic                   bready;
    
    // Read Address Channel (monitoring)
    logic [ID_WIDTH-1:0]    arid;
    logic [ADDR_WIDTH-1:0]  araddr;
    logic [7:0]             arlen;
    logic [2:0]             arsize;
    logic [1:0]             arburst;
    logic                   arlock;
    logic [3:0]             arcache;
    logic [2:0]             arprot;
    logic [3:0]             arqos;
    logic [3:0]             arregion;
    logic                   arvalid;
    logic                   arready;
    
    // Read Data Channel (monitoring)
    logic [ID_WIDTH-1:0]    rid;
    logic [DATA_WIDTH-1:0]  rdata;
    logic [1:0]             rresp;
    logic                   rlast;
    logic                   rvalid;
    logic                   rready;
    
    // Monitor tasks
    
    // Task to monitor write address channel
    task automatic monitor_write_addr();
        forever begin
            @(posedge aclk iff (awvalid && awready));
            $display("[%0t] MONITOR: Write Address - addr=0x%0h, id=%0d, len=%0d, size=%0d, burst=%0d, qos=%0d, region=%0d",
                     $time, awaddr, awid, awlen, awsize, awburst, awqos, awregion);
        end
    endtask
    
    // Task to monitor write data channel
    task automatic monitor_write_data();
        forever begin
            @(posedge aclk iff (wvalid && wready));
            $display("[%0t] MONITOR: Write Data - data=0x%0h, strb=0x%0h, last=%0b",
                     $time, wdata, wstrb, wlast);
        end
    endtask
    
    // Task to monitor write response channel
    task automatic monitor_write_resp();
        forever begin
            @(posedge aclk iff (bvalid && bready));
            $display("[%0t] MONITOR: Write Response - id=%0d, resp=%0d (%s)",
                     $time, bid, bresp, 
                     (bresp == 2'b00) ? "OKAY" :
                     (bresp == 2'b01) ? "EXOKAY" :
                     (bresp == 2'b10) ? "SLVERR" : "DECERR");
        end
    endtask
    
    // Task to monitor read address channel
    task automatic monitor_read_addr();
        forever begin
            @(posedge aclk iff (arvalid && arready));
            $display("[%0t] MONITOR: Read Address - addr=0x%0h, id=%0d, len=%0d, size=%0d, burst=%0d, qos=%0d, region=%0d",
                     $time, araddr, arid, arlen, arsize, arburst, arqos, arregion);
        end
    endtask
    
    // Task to monitor read data channel
    task automatic monitor_read_data();
        forever begin
            @(posedge aclk iff (rvalid && rready));
            $display("[%0t] MONITOR: Read Data - id=%0d, data=0x%0h, resp=%0d (%s), last=%0b",
                     $time, rid, rdata, rresp,
                     (rresp == 2'b00) ? "OKAY" :
                     (rresp == 2'b01) ? "EXOKAY" :
                     (rresp == 2'b10) ? "SLVERR" : "DECERR",
                     rlast);
        end
    endtask
    
    // Start all monitors after reset
    initial begin
        @(posedge aresetn);
        #10; // Small delay after reset
        $display("[%0t] MONITOR: Starting channel monitors after reset", $time);
        fork
            monitor_write_addr();
            monitor_write_data();
            monitor_write_resp();
            monitor_read_addr();
            monitor_read_data();
        join_none
    end
    
    // Protocol assertions
    property p_awvalid_stable;
        @(posedge aclk) disable iff (!aresetn)
        awvalid && !awready |=> awvalid;
    endproperty
    assert property(p_awvalid_stable) else
        $display("[%0t] MONITOR: ERROR - AWVALID deasserted before AWREADY", $time);
    
    property p_wvalid_stable;
        @(posedge aclk) disable iff (!aresetn)
        wvalid && !wready |=> wvalid;
    endproperty
    assert property(p_wvalid_stable) else
        $display("[%0t] MONITOR: ERROR - WVALID deasserted before WREADY", $time);
    
    property p_arvalid_stable;
        @(posedge aclk) disable iff (!aresetn)
        arvalid && !arready |=> arvalid;
    endproperty
    assert property(p_arvalid_stable) else
        $display("[%0t] MONITOR: ERROR - ARVALID deasserted before ARREADY", $time);
    
    property p_rready_stable;
        @(posedge aclk) disable iff (!aresetn)
        rvalid && !rready |=> rready;
    endproperty
    
    property p_bready_stable;
        @(posedge aclk) disable iff (!aresetn)
        bvalid && !bready |=> bready;
    endproperty
    
endinterface : axi4_master_monitor_bfm
