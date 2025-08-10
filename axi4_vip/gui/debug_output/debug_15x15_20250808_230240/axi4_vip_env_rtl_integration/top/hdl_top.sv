//==============================================================================
// HDL Top - VIP+RTL Integration for 15x15 AXI4 Matrix
// Generated with proper interface instantiation - Warning-free
// Date: 2025-08-08 23:02:40
//==============================================================================

module hdl_top;
    
    import axi4_globals_pkg::*;
    
    // Clock and reset
    logic aclk;
    logic aresetn;
    
    // Generate clock
    initial begin
        aclk = 0;
        forever #5 aclk = ~aclk; // 100MHz
    end
    
    // Generate reset
    initial begin
        aresetn = 0;
        #100 aresetn = 1;
        
        // Let UVM control simulation end
        // Removed automatic $finish to allow transactions to complete
    end
    
    // AXI4 interfaces for VIP+RTL integration
    axi4_if #(
        .ADDR_WIDTH(ADDRESS_WIDTH),
        .DATA_WIDTH(DATA_WIDTH), 
        .ID_WIDTH(ID_WIDTH),
        .USER_WIDTH(USER_WIDTH)
    ) master_if[15](aclk, aresetn);
    
    axi4_if #(
        .ADDR_WIDTH(ADDRESS_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH), 
        .USER_WIDTH(USER_WIDTH)
    ) slave_if[15](aclk, aresetn);
    
    // Master 0 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_0_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_0_monitor_bfm();
    
    // Master 1 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_1_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_1_monitor_bfm();
    
    // Master 2 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_2_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_2_monitor_bfm();
    
    // Master 3 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_3_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_3_monitor_bfm();
    
    // Master 4 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_4_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_4_monitor_bfm();
    
    // Master 5 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_5_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_5_monitor_bfm();
    
    // Master 6 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_6_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_6_monitor_bfm();
    
    // Master 7 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_7_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_7_monitor_bfm();
    
    // Master 8 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_8_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_8_monitor_bfm();
    
    // Master 9 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_9_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_9_monitor_bfm();
    
    // Master 10 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_10_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_10_monitor_bfm();
    
    // Master 11 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_11_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_11_monitor_bfm();
    
    // Master 12 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_12_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_12_monitor_bfm();
    
    // Master 13 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_13_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_13_monitor_bfm();
    
    // Master 14 BFM interfaces
    axi4_master_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) master_14_driver_bfm();
    
    axi4_master_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)  
    ) master_14_monitor_bfm();
    
    // Slave 0 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_0_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_0_monitor_bfm();
    
    // Slave 1 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_1_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_1_monitor_bfm();
    
    // Slave 2 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_2_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_2_monitor_bfm();
    
    // Slave 3 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_3_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_3_monitor_bfm();
    
    // Slave 4 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_4_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_4_monitor_bfm();
    
    // Slave 5 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_5_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_5_monitor_bfm();
    
    // Slave 6 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_6_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_6_monitor_bfm();
    
    // Slave 7 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_7_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_7_monitor_bfm();
    
    // Slave 8 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_8_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_8_monitor_bfm();
    
    // Slave 9 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_9_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_9_monitor_bfm();
    
    // Slave 10 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_10_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_10_monitor_bfm();
    
    // Slave 11 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_11_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_11_monitor_bfm();
    
    // Slave 12 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_12_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_12_monitor_bfm();
    
    // Slave 13 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_13_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_13_monitor_bfm();
    
    // Slave 14 BFM interfaces
    axi4_slave_driver_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_14_driver_bfm();
    
    axi4_slave_monitor_bfm #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH)
    ) slave_14_monitor_bfm();

    // RTL DUT instantiation - 15x15 interconnect with interface connections
    axi4_interconnect_m15s15 #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .USER_WIDTH(USER_WIDTH)
    ) dut (
        .aclk(aclk),
        .aresetn(aresetn),        
        // Master 0 interface connections
        .m0_awid(master_if[0].awid), .m0_awaddr(master_if[0].awaddr), .m0_awlen(master_if[0].awlen),
        .m0_awsize(master_if[0].awsize), .m0_awburst(master_if[0].awburst), .m0_awlock(master_if[0].awlock),
        .m0_awcache(master_if[0].awcache), .m0_awprot(master_if[0].awprot), .m0_awqos(master_if[0].awqos),
        .m0_awvalid(master_if[0].awvalid), .m0_awready(master_if[0].awready),
        .m0_wdata(master_if[0].wdata), .m0_wstrb(master_if[0].wstrb), .m0_wlast(master_if[0].wlast),
        .m0_wvalid(master_if[0].wvalid), .m0_wready(master_if[0].wready),
        .m0_bid(master_if[0].bid), .m0_bresp(master_if[0].bresp), .m0_bvalid(master_if[0].bvalid),
        .m0_bready(master_if[0].bready), .m0_arid(master_if[0].arid), .m0_araddr(master_if[0].araddr),
        .m0_arlen(master_if[0].arlen), .m0_arsize(master_if[0].arsize), .m0_arburst(master_if[0].arburst),
        .m0_arlock(master_if[0].arlock), .m0_arcache(master_if[0].arcache), .m0_arprot(master_if[0].arprot),
        .m0_arqos(master_if[0].arqos), .m0_arvalid(master_if[0].arvalid), .m0_arready(master_if[0].arready),
        .m0_rid(master_if[0].rid), .m0_rdata(master_if[0].rdata), .m0_rresp(master_if[0].rresp),
        .m0_rlast(master_if[0].rlast), .m0_rvalid(master_if[0].rvalid), .m0_rready(master_if[0].rready),        
        // Master 1 interface connections
        .m1_awid(master_if[1].awid), .m1_awaddr(master_if[1].awaddr), .m1_awlen(master_if[1].awlen),
        .m1_awsize(master_if[1].awsize), .m1_awburst(master_if[1].awburst), .m1_awlock(master_if[1].awlock),
        .m1_awcache(master_if[1].awcache), .m1_awprot(master_if[1].awprot), .m1_awqos(master_if[1].awqos),
        .m1_awvalid(master_if[1].awvalid), .m1_awready(master_if[1].awready),
        .m1_wdata(master_if[1].wdata), .m1_wstrb(master_if[1].wstrb), .m1_wlast(master_if[1].wlast),
        .m1_wvalid(master_if[1].wvalid), .m1_wready(master_if[1].wready),
        .m1_bid(master_if[1].bid), .m1_bresp(master_if[1].bresp), .m1_bvalid(master_if[1].bvalid),
        .m1_bready(master_if[1].bready), .m1_arid(master_if[1].arid), .m1_araddr(master_if[1].araddr),
        .m1_arlen(master_if[1].arlen), .m1_arsize(master_if[1].arsize), .m1_arburst(master_if[1].arburst),
        .m1_arlock(master_if[1].arlock), .m1_arcache(master_if[1].arcache), .m1_arprot(master_if[1].arprot),
        .m1_arqos(master_if[1].arqos), .m1_arvalid(master_if[1].arvalid), .m1_arready(master_if[1].arready),
        .m1_rid(master_if[1].rid), .m1_rdata(master_if[1].rdata), .m1_rresp(master_if[1].rresp),
        .m1_rlast(master_if[1].rlast), .m1_rvalid(master_if[1].rvalid), .m1_rready(master_if[1].rready),        
        // Master 2 interface connections
        .m2_awid(master_if[2].awid), .m2_awaddr(master_if[2].awaddr), .m2_awlen(master_if[2].awlen),
        .m2_awsize(master_if[2].awsize), .m2_awburst(master_if[2].awburst), .m2_awlock(master_if[2].awlock),
        .m2_awcache(master_if[2].awcache), .m2_awprot(master_if[2].awprot), .m2_awqos(master_if[2].awqos),
        .m2_awvalid(master_if[2].awvalid), .m2_awready(master_if[2].awready),
        .m2_wdata(master_if[2].wdata), .m2_wstrb(master_if[2].wstrb), .m2_wlast(master_if[2].wlast),
        .m2_wvalid(master_if[2].wvalid), .m2_wready(master_if[2].wready),
        .m2_bid(master_if[2].bid), .m2_bresp(master_if[2].bresp), .m2_bvalid(master_if[2].bvalid),
        .m2_bready(master_if[2].bready), .m2_arid(master_if[2].arid), .m2_araddr(master_if[2].araddr),
        .m2_arlen(master_if[2].arlen), .m2_arsize(master_if[2].arsize), .m2_arburst(master_if[2].arburst),
        .m2_arlock(master_if[2].arlock), .m2_arcache(master_if[2].arcache), .m2_arprot(master_if[2].arprot),
        .m2_arqos(master_if[2].arqos), .m2_arvalid(master_if[2].arvalid), .m2_arready(master_if[2].arready),
        .m2_rid(master_if[2].rid), .m2_rdata(master_if[2].rdata), .m2_rresp(master_if[2].rresp),
        .m2_rlast(master_if[2].rlast), .m2_rvalid(master_if[2].rvalid), .m2_rready(master_if[2].rready),        
        // Master 3 interface connections
        .m3_awid(master_if[3].awid), .m3_awaddr(master_if[3].awaddr), .m3_awlen(master_if[3].awlen),
        .m3_awsize(master_if[3].awsize), .m3_awburst(master_if[3].awburst), .m3_awlock(master_if[3].awlock),
        .m3_awcache(master_if[3].awcache), .m3_awprot(master_if[3].awprot), .m3_awqos(master_if[3].awqos),
        .m3_awvalid(master_if[3].awvalid), .m3_awready(master_if[3].awready),
        .m3_wdata(master_if[3].wdata), .m3_wstrb(master_if[3].wstrb), .m3_wlast(master_if[3].wlast),
        .m3_wvalid(master_if[3].wvalid), .m3_wready(master_if[3].wready),
        .m3_bid(master_if[3].bid), .m3_bresp(master_if[3].bresp), .m3_bvalid(master_if[3].bvalid),
        .m3_bready(master_if[3].bready), .m3_arid(master_if[3].arid), .m3_araddr(master_if[3].araddr),
        .m3_arlen(master_if[3].arlen), .m3_arsize(master_if[3].arsize), .m3_arburst(master_if[3].arburst),
        .m3_arlock(master_if[3].arlock), .m3_arcache(master_if[3].arcache), .m3_arprot(master_if[3].arprot),
        .m3_arqos(master_if[3].arqos), .m3_arvalid(master_if[3].arvalid), .m3_arready(master_if[3].arready),
        .m3_rid(master_if[3].rid), .m3_rdata(master_if[3].rdata), .m3_rresp(master_if[3].rresp),
        .m3_rlast(master_if[3].rlast), .m3_rvalid(master_if[3].rvalid), .m3_rready(master_if[3].rready),        
        // Master 4 interface connections
        .m4_awid(master_if[4].awid), .m4_awaddr(master_if[4].awaddr), .m4_awlen(master_if[4].awlen),
        .m4_awsize(master_if[4].awsize), .m4_awburst(master_if[4].awburst), .m4_awlock(master_if[4].awlock),
        .m4_awcache(master_if[4].awcache), .m4_awprot(master_if[4].awprot), .m4_awqos(master_if[4].awqos),
        .m4_awvalid(master_if[4].awvalid), .m4_awready(master_if[4].awready),
        .m4_wdata(master_if[4].wdata), .m4_wstrb(master_if[4].wstrb), .m4_wlast(master_if[4].wlast),
        .m4_wvalid(master_if[4].wvalid), .m4_wready(master_if[4].wready),
        .m4_bid(master_if[4].bid), .m4_bresp(master_if[4].bresp), .m4_bvalid(master_if[4].bvalid),
        .m4_bready(master_if[4].bready), .m4_arid(master_if[4].arid), .m4_araddr(master_if[4].araddr),
        .m4_arlen(master_if[4].arlen), .m4_arsize(master_if[4].arsize), .m4_arburst(master_if[4].arburst),
        .m4_arlock(master_if[4].arlock), .m4_arcache(master_if[4].arcache), .m4_arprot(master_if[4].arprot),
        .m4_arqos(master_if[4].arqos), .m4_arvalid(master_if[4].arvalid), .m4_arready(master_if[4].arready),
        .m4_rid(master_if[4].rid), .m4_rdata(master_if[4].rdata), .m4_rresp(master_if[4].rresp),
        .m4_rlast(master_if[4].rlast), .m4_rvalid(master_if[4].rvalid), .m4_rready(master_if[4].rready),        
        // Master 5 interface connections
        .m5_awid(master_if[5].awid), .m5_awaddr(master_if[5].awaddr), .m5_awlen(master_if[5].awlen),
        .m5_awsize(master_if[5].awsize), .m5_awburst(master_if[5].awburst), .m5_awlock(master_if[5].awlock),
        .m5_awcache(master_if[5].awcache), .m5_awprot(master_if[5].awprot), .m5_awqos(master_if[5].awqos),
        .m5_awvalid(master_if[5].awvalid), .m5_awready(master_if[5].awready),
        .m5_wdata(master_if[5].wdata), .m5_wstrb(master_if[5].wstrb), .m5_wlast(master_if[5].wlast),
        .m5_wvalid(master_if[5].wvalid), .m5_wready(master_if[5].wready),
        .m5_bid(master_if[5].bid), .m5_bresp(master_if[5].bresp), .m5_bvalid(master_if[5].bvalid),
        .m5_bready(master_if[5].bready), .m5_arid(master_if[5].arid), .m5_araddr(master_if[5].araddr),
        .m5_arlen(master_if[5].arlen), .m5_arsize(master_if[5].arsize), .m5_arburst(master_if[5].arburst),
        .m5_arlock(master_if[5].arlock), .m5_arcache(master_if[5].arcache), .m5_arprot(master_if[5].arprot),
        .m5_arqos(master_if[5].arqos), .m5_arvalid(master_if[5].arvalid), .m5_arready(master_if[5].arready),
        .m5_rid(master_if[5].rid), .m5_rdata(master_if[5].rdata), .m5_rresp(master_if[5].rresp),
        .m5_rlast(master_if[5].rlast), .m5_rvalid(master_if[5].rvalid), .m5_rready(master_if[5].rready),        
        // Master 6 interface connections
        .m6_awid(master_if[6].awid), .m6_awaddr(master_if[6].awaddr), .m6_awlen(master_if[6].awlen),
        .m6_awsize(master_if[6].awsize), .m6_awburst(master_if[6].awburst), .m6_awlock(master_if[6].awlock),
        .m6_awcache(master_if[6].awcache), .m6_awprot(master_if[6].awprot), .m6_awqos(master_if[6].awqos),
        .m6_awvalid(master_if[6].awvalid), .m6_awready(master_if[6].awready),
        .m6_wdata(master_if[6].wdata), .m6_wstrb(master_if[6].wstrb), .m6_wlast(master_if[6].wlast),
        .m6_wvalid(master_if[6].wvalid), .m6_wready(master_if[6].wready),
        .m6_bid(master_if[6].bid), .m6_bresp(master_if[6].bresp), .m6_bvalid(master_if[6].bvalid),
        .m6_bready(master_if[6].bready), .m6_arid(master_if[6].arid), .m6_araddr(master_if[6].araddr),
        .m6_arlen(master_if[6].arlen), .m6_arsize(master_if[6].arsize), .m6_arburst(master_if[6].arburst),
        .m6_arlock(master_if[6].arlock), .m6_arcache(master_if[6].arcache), .m6_arprot(master_if[6].arprot),
        .m6_arqos(master_if[6].arqos), .m6_arvalid(master_if[6].arvalid), .m6_arready(master_if[6].arready),
        .m6_rid(master_if[6].rid), .m6_rdata(master_if[6].rdata), .m6_rresp(master_if[6].rresp),
        .m6_rlast(master_if[6].rlast), .m6_rvalid(master_if[6].rvalid), .m6_rready(master_if[6].rready),        
        // Master 7 interface connections
        .m7_awid(master_if[7].awid), .m7_awaddr(master_if[7].awaddr), .m7_awlen(master_if[7].awlen),
        .m7_awsize(master_if[7].awsize), .m7_awburst(master_if[7].awburst), .m7_awlock(master_if[7].awlock),
        .m7_awcache(master_if[7].awcache), .m7_awprot(master_if[7].awprot), .m7_awqos(master_if[7].awqos),
        .m7_awvalid(master_if[7].awvalid), .m7_awready(master_if[7].awready),
        .m7_wdata(master_if[7].wdata), .m7_wstrb(master_if[7].wstrb), .m7_wlast(master_if[7].wlast),
        .m7_wvalid(master_if[7].wvalid), .m7_wready(master_if[7].wready),
        .m7_bid(master_if[7].bid), .m7_bresp(master_if[7].bresp), .m7_bvalid(master_if[7].bvalid),
        .m7_bready(master_if[7].bready), .m7_arid(master_if[7].arid), .m7_araddr(master_if[7].araddr),
        .m7_arlen(master_if[7].arlen), .m7_arsize(master_if[7].arsize), .m7_arburst(master_if[7].arburst),
        .m7_arlock(master_if[7].arlock), .m7_arcache(master_if[7].arcache), .m7_arprot(master_if[7].arprot),
        .m7_arqos(master_if[7].arqos), .m7_arvalid(master_if[7].arvalid), .m7_arready(master_if[7].arready),
        .m7_rid(master_if[7].rid), .m7_rdata(master_if[7].rdata), .m7_rresp(master_if[7].rresp),
        .m7_rlast(master_if[7].rlast), .m7_rvalid(master_if[7].rvalid), .m7_rready(master_if[7].rready),        
        // Master 8 interface connections
        .m8_awid(master_if[8].awid), .m8_awaddr(master_if[8].awaddr), .m8_awlen(master_if[8].awlen),
        .m8_awsize(master_if[8].awsize), .m8_awburst(master_if[8].awburst), .m8_awlock(master_if[8].awlock),
        .m8_awcache(master_if[8].awcache), .m8_awprot(master_if[8].awprot), .m8_awqos(master_if[8].awqos),
        .m8_awvalid(master_if[8].awvalid), .m8_awready(master_if[8].awready),
        .m8_wdata(master_if[8].wdata), .m8_wstrb(master_if[8].wstrb), .m8_wlast(master_if[8].wlast),
        .m8_wvalid(master_if[8].wvalid), .m8_wready(master_if[8].wready),
        .m8_bid(master_if[8].bid), .m8_bresp(master_if[8].bresp), .m8_bvalid(master_if[8].bvalid),
        .m8_bready(master_if[8].bready), .m8_arid(master_if[8].arid), .m8_araddr(master_if[8].araddr),
        .m8_arlen(master_if[8].arlen), .m8_arsize(master_if[8].arsize), .m8_arburst(master_if[8].arburst),
        .m8_arlock(master_if[8].arlock), .m8_arcache(master_if[8].arcache), .m8_arprot(master_if[8].arprot),
        .m8_arqos(master_if[8].arqos), .m8_arvalid(master_if[8].arvalid), .m8_arready(master_if[8].arready),
        .m8_rid(master_if[8].rid), .m8_rdata(master_if[8].rdata), .m8_rresp(master_if[8].rresp),
        .m8_rlast(master_if[8].rlast), .m8_rvalid(master_if[8].rvalid), .m8_rready(master_if[8].rready),        
        // Master 9 interface connections
        .m9_awid(master_if[9].awid), .m9_awaddr(master_if[9].awaddr), .m9_awlen(master_if[9].awlen),
        .m9_awsize(master_if[9].awsize), .m9_awburst(master_if[9].awburst), .m9_awlock(master_if[9].awlock),
        .m9_awcache(master_if[9].awcache), .m9_awprot(master_if[9].awprot), .m9_awqos(master_if[9].awqos),
        .m9_awvalid(master_if[9].awvalid), .m9_awready(master_if[9].awready),
        .m9_wdata(master_if[9].wdata), .m9_wstrb(master_if[9].wstrb), .m9_wlast(master_if[9].wlast),
        .m9_wvalid(master_if[9].wvalid), .m9_wready(master_if[9].wready),
        .m9_bid(master_if[9].bid), .m9_bresp(master_if[9].bresp), .m9_bvalid(master_if[9].bvalid),
        .m9_bready(master_if[9].bready), .m9_arid(master_if[9].arid), .m9_araddr(master_if[9].araddr),
        .m9_arlen(master_if[9].arlen), .m9_arsize(master_if[9].arsize), .m9_arburst(master_if[9].arburst),
        .m9_arlock(master_if[9].arlock), .m9_arcache(master_if[9].arcache), .m9_arprot(master_if[9].arprot),
        .m9_arqos(master_if[9].arqos), .m9_arvalid(master_if[9].arvalid), .m9_arready(master_if[9].arready),
        .m9_rid(master_if[9].rid), .m9_rdata(master_if[9].rdata), .m9_rresp(master_if[9].rresp),
        .m9_rlast(master_if[9].rlast), .m9_rvalid(master_if[9].rvalid), .m9_rready(master_if[9].rready),        
        // Master 10 interface connections
        .m10_awid(master_if[10].awid), .m10_awaddr(master_if[10].awaddr), .m10_awlen(master_if[10].awlen),
        .m10_awsize(master_if[10].awsize), .m10_awburst(master_if[10].awburst), .m10_awlock(master_if[10].awlock),
        .m10_awcache(master_if[10].awcache), .m10_awprot(master_if[10].awprot), .m10_awqos(master_if[10].awqos),
        .m10_awvalid(master_if[10].awvalid), .m10_awready(master_if[10].awready),
        .m10_wdata(master_if[10].wdata), .m10_wstrb(master_if[10].wstrb), .m10_wlast(master_if[10].wlast),
        .m10_wvalid(master_if[10].wvalid), .m10_wready(master_if[10].wready),
        .m10_bid(master_if[10].bid), .m10_bresp(master_if[10].bresp), .m10_bvalid(master_if[10].bvalid),
        .m10_bready(master_if[10].bready), .m10_arid(master_if[10].arid), .m10_araddr(master_if[10].araddr),
        .m10_arlen(master_if[10].arlen), .m10_arsize(master_if[10].arsize), .m10_arburst(master_if[10].arburst),
        .m10_arlock(master_if[10].arlock), .m10_arcache(master_if[10].arcache), .m10_arprot(master_if[10].arprot),
        .m10_arqos(master_if[10].arqos), .m10_arvalid(master_if[10].arvalid), .m10_arready(master_if[10].arready),
        .m10_rid(master_if[10].rid), .m10_rdata(master_if[10].rdata), .m10_rresp(master_if[10].rresp),
        .m10_rlast(master_if[10].rlast), .m10_rvalid(master_if[10].rvalid), .m10_rready(master_if[10].rready),        
        // Master 11 interface connections
        .m11_awid(master_if[11].awid), .m11_awaddr(master_if[11].awaddr), .m11_awlen(master_if[11].awlen),
        .m11_awsize(master_if[11].awsize), .m11_awburst(master_if[11].awburst), .m11_awlock(master_if[11].awlock),
        .m11_awcache(master_if[11].awcache), .m11_awprot(master_if[11].awprot), .m11_awqos(master_if[11].awqos),
        .m11_awvalid(master_if[11].awvalid), .m11_awready(master_if[11].awready),
        .m11_wdata(master_if[11].wdata), .m11_wstrb(master_if[11].wstrb), .m11_wlast(master_if[11].wlast),
        .m11_wvalid(master_if[11].wvalid), .m11_wready(master_if[11].wready),
        .m11_bid(master_if[11].bid), .m11_bresp(master_if[11].bresp), .m11_bvalid(master_if[11].bvalid),
        .m11_bready(master_if[11].bready), .m11_arid(master_if[11].arid), .m11_araddr(master_if[11].araddr),
        .m11_arlen(master_if[11].arlen), .m11_arsize(master_if[11].arsize), .m11_arburst(master_if[11].arburst),
        .m11_arlock(master_if[11].arlock), .m11_arcache(master_if[11].arcache), .m11_arprot(master_if[11].arprot),
        .m11_arqos(master_if[11].arqos), .m11_arvalid(master_if[11].arvalid), .m11_arready(master_if[11].arready),
        .m11_rid(master_if[11].rid), .m11_rdata(master_if[11].rdata), .m11_rresp(master_if[11].rresp),
        .m11_rlast(master_if[11].rlast), .m11_rvalid(master_if[11].rvalid), .m11_rready(master_if[11].rready),        
        // Master 12 interface connections
        .m12_awid(master_if[12].awid), .m12_awaddr(master_if[12].awaddr), .m12_awlen(master_if[12].awlen),
        .m12_awsize(master_if[12].awsize), .m12_awburst(master_if[12].awburst), .m12_awlock(master_if[12].awlock),
        .m12_awcache(master_if[12].awcache), .m12_awprot(master_if[12].awprot), .m12_awqos(master_if[12].awqos),
        .m12_awvalid(master_if[12].awvalid), .m12_awready(master_if[12].awready),
        .m12_wdata(master_if[12].wdata), .m12_wstrb(master_if[12].wstrb), .m12_wlast(master_if[12].wlast),
        .m12_wvalid(master_if[12].wvalid), .m12_wready(master_if[12].wready),
        .m12_bid(master_if[12].bid), .m12_bresp(master_if[12].bresp), .m12_bvalid(master_if[12].bvalid),
        .m12_bready(master_if[12].bready), .m12_arid(master_if[12].arid), .m12_araddr(master_if[12].araddr),
        .m12_arlen(master_if[12].arlen), .m12_arsize(master_if[12].arsize), .m12_arburst(master_if[12].arburst),
        .m12_arlock(master_if[12].arlock), .m12_arcache(master_if[12].arcache), .m12_arprot(master_if[12].arprot),
        .m12_arqos(master_if[12].arqos), .m12_arvalid(master_if[12].arvalid), .m12_arready(master_if[12].arready),
        .m12_rid(master_if[12].rid), .m12_rdata(master_if[12].rdata), .m12_rresp(master_if[12].rresp),
        .m12_rlast(master_if[12].rlast), .m12_rvalid(master_if[12].rvalid), .m12_rready(master_if[12].rready),        
        // Master 13 interface connections
        .m13_awid(master_if[13].awid), .m13_awaddr(master_if[13].awaddr), .m13_awlen(master_if[13].awlen),
        .m13_awsize(master_if[13].awsize), .m13_awburst(master_if[13].awburst), .m13_awlock(master_if[13].awlock),
        .m13_awcache(master_if[13].awcache), .m13_awprot(master_if[13].awprot), .m13_awqos(master_if[13].awqos),
        .m13_awvalid(master_if[13].awvalid), .m13_awready(master_if[13].awready),
        .m13_wdata(master_if[13].wdata), .m13_wstrb(master_if[13].wstrb), .m13_wlast(master_if[13].wlast),
        .m13_wvalid(master_if[13].wvalid), .m13_wready(master_if[13].wready),
        .m13_bid(master_if[13].bid), .m13_bresp(master_if[13].bresp), .m13_bvalid(master_if[13].bvalid),
        .m13_bready(master_if[13].bready), .m13_arid(master_if[13].arid), .m13_araddr(master_if[13].araddr),
        .m13_arlen(master_if[13].arlen), .m13_arsize(master_if[13].arsize), .m13_arburst(master_if[13].arburst),
        .m13_arlock(master_if[13].arlock), .m13_arcache(master_if[13].arcache), .m13_arprot(master_if[13].arprot),
        .m13_arqos(master_if[13].arqos), .m13_arvalid(master_if[13].arvalid), .m13_arready(master_if[13].arready),
        .m13_rid(master_if[13].rid), .m13_rdata(master_if[13].rdata), .m13_rresp(master_if[13].rresp),
        .m13_rlast(master_if[13].rlast), .m13_rvalid(master_if[13].rvalid), .m13_rready(master_if[13].rready),        
        // Master 14 interface connections
        .m14_awid(master_if[14].awid), .m14_awaddr(master_if[14].awaddr), .m14_awlen(master_if[14].awlen),
        .m14_awsize(master_if[14].awsize), .m14_awburst(master_if[14].awburst), .m14_awlock(master_if[14].awlock),
        .m14_awcache(master_if[14].awcache), .m14_awprot(master_if[14].awprot), .m14_awqos(master_if[14].awqos),
        .m14_awvalid(master_if[14].awvalid), .m14_awready(master_if[14].awready),
        .m14_wdata(master_if[14].wdata), .m14_wstrb(master_if[14].wstrb), .m14_wlast(master_if[14].wlast),
        .m14_wvalid(master_if[14].wvalid), .m14_wready(master_if[14].wready),
        .m14_bid(master_if[14].bid), .m14_bresp(master_if[14].bresp), .m14_bvalid(master_if[14].bvalid),
        .m14_bready(master_if[14].bready), .m14_arid(master_if[14].arid), .m14_araddr(master_if[14].araddr),
        .m14_arlen(master_if[14].arlen), .m14_arsize(master_if[14].arsize), .m14_arburst(master_if[14].arburst),
        .m14_arlock(master_if[14].arlock), .m14_arcache(master_if[14].arcache), .m14_arprot(master_if[14].arprot),
        .m14_arqos(master_if[14].arqos), .m14_arvalid(master_if[14].arvalid), .m14_arready(master_if[14].arready),
        .m14_rid(master_if[14].rid), .m14_rdata(master_if[14].rdata), .m14_rresp(master_if[14].rresp),
        .m14_rlast(master_if[14].rlast), .m14_rvalid(master_if[14].rvalid), .m14_rready(master_if[14].rready),,        
        // Slave 0 interface connections
        .s0_awid(slave_if[0].awid), .s0_awaddr(slave_if[0].awaddr), .s0_awlen(slave_if[0].awlen),
        .s0_awsize(slave_if[0].awsize), .s0_awburst(slave_if[0].awburst), .s0_awlock(slave_if[0].awlock),
        .s0_awcache(slave_if[0].awcache), .s0_awprot(slave_if[0].awprot), .s0_awqos(slave_if[0].awqos),
        .s0_awvalid(slave_if[0].awvalid), .s0_awready(slave_if[0].awready),
        .s0_wdata(slave_if[0].wdata), .s0_wstrb(slave_if[0].wstrb), .s0_wlast(slave_if[0].wlast),
        .s0_wvalid(slave_if[0].wvalid), .s0_wready(slave_if[0].wready),
        .s0_bid(slave_if[0].bid), .s0_bresp(slave_if[0].bresp), .s0_bvalid(slave_if[0].bvalid),
        .s0_bready(slave_if[0].bready), .s0_arid(slave_if[0].arid), .s0_araddr(slave_if[0].araddr),
        .s0_arlen(slave_if[0].arlen), .s0_arsize(slave_if[0].arsize), .s0_arburst(slave_if[0].arburst),
        .s0_arlock(slave_if[0].arlock), .s0_arcache(slave_if[0].arcache), .s0_arprot(slave_if[0].arprot),
        .s0_arqos(slave_if[0].arqos), .s0_arvalid(slave_if[0].arvalid), .s0_arready(slave_if[0].arready),
        .s0_rid(slave_if[0].rid), .s0_rdata(slave_if[0].rdata), .s0_rresp(slave_if[0].rresp),
        .s0_rlast(slave_if[0].rlast), .s0_rvalid(slave_if[0].rvalid), .s0_rready(slave_if[0].rready),        
        // Slave 1 interface connections
        .s1_awid(slave_if[1].awid), .s1_awaddr(slave_if[1].awaddr), .s1_awlen(slave_if[1].awlen),
        .s1_awsize(slave_if[1].awsize), .s1_awburst(slave_if[1].awburst), .s1_awlock(slave_if[1].awlock),
        .s1_awcache(slave_if[1].awcache), .s1_awprot(slave_if[1].awprot), .s1_awqos(slave_if[1].awqos),
        .s1_awvalid(slave_if[1].awvalid), .s1_awready(slave_if[1].awready),
        .s1_wdata(slave_if[1].wdata), .s1_wstrb(slave_if[1].wstrb), .s1_wlast(slave_if[1].wlast),
        .s1_wvalid(slave_if[1].wvalid), .s1_wready(slave_if[1].wready),
        .s1_bid(slave_if[1].bid), .s1_bresp(slave_if[1].bresp), .s1_bvalid(slave_if[1].bvalid),
        .s1_bready(slave_if[1].bready), .s1_arid(slave_if[1].arid), .s1_araddr(slave_if[1].araddr),
        .s1_arlen(slave_if[1].arlen), .s1_arsize(slave_if[1].arsize), .s1_arburst(slave_if[1].arburst),
        .s1_arlock(slave_if[1].arlock), .s1_arcache(slave_if[1].arcache), .s1_arprot(slave_if[1].arprot),
        .s1_arqos(slave_if[1].arqos), .s1_arvalid(slave_if[1].arvalid), .s1_arready(slave_if[1].arready),
        .s1_rid(slave_if[1].rid), .s1_rdata(slave_if[1].rdata), .s1_rresp(slave_if[1].rresp),
        .s1_rlast(slave_if[1].rlast), .s1_rvalid(slave_if[1].rvalid), .s1_rready(slave_if[1].rready),        
        // Slave 2 interface connections
        .s2_awid(slave_if[2].awid), .s2_awaddr(slave_if[2].awaddr), .s2_awlen(slave_if[2].awlen),
        .s2_awsize(slave_if[2].awsize), .s2_awburst(slave_if[2].awburst), .s2_awlock(slave_if[2].awlock),
        .s2_awcache(slave_if[2].awcache), .s2_awprot(slave_if[2].awprot), .s2_awqos(slave_if[2].awqos),
        .s2_awvalid(slave_if[2].awvalid), .s2_awready(slave_if[2].awready),
        .s2_wdata(slave_if[2].wdata), .s2_wstrb(slave_if[2].wstrb), .s2_wlast(slave_if[2].wlast),
        .s2_wvalid(slave_if[2].wvalid), .s2_wready(slave_if[2].wready),
        .s2_bid(slave_if[2].bid), .s2_bresp(slave_if[2].bresp), .s2_bvalid(slave_if[2].bvalid),
        .s2_bready(slave_if[2].bready), .s2_arid(slave_if[2].arid), .s2_araddr(slave_if[2].araddr),
        .s2_arlen(slave_if[2].arlen), .s2_arsize(slave_if[2].arsize), .s2_arburst(slave_if[2].arburst),
        .s2_arlock(slave_if[2].arlock), .s2_arcache(slave_if[2].arcache), .s2_arprot(slave_if[2].arprot),
        .s2_arqos(slave_if[2].arqos), .s2_arvalid(slave_if[2].arvalid), .s2_arready(slave_if[2].arready),
        .s2_rid(slave_if[2].rid), .s2_rdata(slave_if[2].rdata), .s2_rresp(slave_if[2].rresp),
        .s2_rlast(slave_if[2].rlast), .s2_rvalid(slave_if[2].rvalid), .s2_rready(slave_if[2].rready),        
        // Slave 3 interface connections
        .s3_awid(slave_if[3].awid), .s3_awaddr(slave_if[3].awaddr), .s3_awlen(slave_if[3].awlen),
        .s3_awsize(slave_if[3].awsize), .s3_awburst(slave_if[3].awburst), .s3_awlock(slave_if[3].awlock),
        .s3_awcache(slave_if[3].awcache), .s3_awprot(slave_if[3].awprot), .s3_awqos(slave_if[3].awqos),
        .s3_awvalid(slave_if[3].awvalid), .s3_awready(slave_if[3].awready),
        .s3_wdata(slave_if[3].wdata), .s3_wstrb(slave_if[3].wstrb), .s3_wlast(slave_if[3].wlast),
        .s3_wvalid(slave_if[3].wvalid), .s3_wready(slave_if[3].wready),
        .s3_bid(slave_if[3].bid), .s3_bresp(slave_if[3].bresp), .s3_bvalid(slave_if[3].bvalid),
        .s3_bready(slave_if[3].bready), .s3_arid(slave_if[3].arid), .s3_araddr(slave_if[3].araddr),
        .s3_arlen(slave_if[3].arlen), .s3_arsize(slave_if[3].arsize), .s3_arburst(slave_if[3].arburst),
        .s3_arlock(slave_if[3].arlock), .s3_arcache(slave_if[3].arcache), .s3_arprot(slave_if[3].arprot),
        .s3_arqos(slave_if[3].arqos), .s3_arvalid(slave_if[3].arvalid), .s3_arready(slave_if[3].arready),
        .s3_rid(slave_if[3].rid), .s3_rdata(slave_if[3].rdata), .s3_rresp(slave_if[3].rresp),
        .s3_rlast(slave_if[3].rlast), .s3_rvalid(slave_if[3].rvalid), .s3_rready(slave_if[3].rready),        
        // Slave 4 interface connections
        .s4_awid(slave_if[4].awid), .s4_awaddr(slave_if[4].awaddr), .s4_awlen(slave_if[4].awlen),
        .s4_awsize(slave_if[4].awsize), .s4_awburst(slave_if[4].awburst), .s4_awlock(slave_if[4].awlock),
        .s4_awcache(slave_if[4].awcache), .s4_awprot(slave_if[4].awprot), .s4_awqos(slave_if[4].awqos),
        .s4_awvalid(slave_if[4].awvalid), .s4_awready(slave_if[4].awready),
        .s4_wdata(slave_if[4].wdata), .s4_wstrb(slave_if[4].wstrb), .s4_wlast(slave_if[4].wlast),
        .s4_wvalid(slave_if[4].wvalid), .s4_wready(slave_if[4].wready),
        .s4_bid(slave_if[4].bid), .s4_bresp(slave_if[4].bresp), .s4_bvalid(slave_if[4].bvalid),
        .s4_bready(slave_if[4].bready), .s4_arid(slave_if[4].arid), .s4_araddr(slave_if[4].araddr),
        .s4_arlen(slave_if[4].arlen), .s4_arsize(slave_if[4].arsize), .s4_arburst(slave_if[4].arburst),
        .s4_arlock(slave_if[4].arlock), .s4_arcache(slave_if[4].arcache), .s4_arprot(slave_if[4].arprot),
        .s4_arqos(slave_if[4].arqos), .s4_arvalid(slave_if[4].arvalid), .s4_arready(slave_if[4].arready),
        .s4_rid(slave_if[4].rid), .s4_rdata(slave_if[4].rdata), .s4_rresp(slave_if[4].rresp),
        .s4_rlast(slave_if[4].rlast), .s4_rvalid(slave_if[4].rvalid), .s4_rready(slave_if[4].rready),        
        // Slave 5 interface connections
        .s5_awid(slave_if[5].awid), .s5_awaddr(slave_if[5].awaddr), .s5_awlen(slave_if[5].awlen),
        .s5_awsize(slave_if[5].awsize), .s5_awburst(slave_if[5].awburst), .s5_awlock(slave_if[5].awlock),
        .s5_awcache(slave_if[5].awcache), .s5_awprot(slave_if[5].awprot), .s5_awqos(slave_if[5].awqos),
        .s5_awvalid(slave_if[5].awvalid), .s5_awready(slave_if[5].awready),
        .s5_wdata(slave_if[5].wdata), .s5_wstrb(slave_if[5].wstrb), .s5_wlast(slave_if[5].wlast),
        .s5_wvalid(slave_if[5].wvalid), .s5_wready(slave_if[5].wready),
        .s5_bid(slave_if[5].bid), .s5_bresp(slave_if[5].bresp), .s5_bvalid(slave_if[5].bvalid),
        .s5_bready(slave_if[5].bready), .s5_arid(slave_if[5].arid), .s5_araddr(slave_if[5].araddr),
        .s5_arlen(slave_if[5].arlen), .s5_arsize(slave_if[5].arsize), .s5_arburst(slave_if[5].arburst),
        .s5_arlock(slave_if[5].arlock), .s5_arcache(slave_if[5].arcache), .s5_arprot(slave_if[5].arprot),
        .s5_arqos(slave_if[5].arqos), .s5_arvalid(slave_if[5].arvalid), .s5_arready(slave_if[5].arready),
        .s5_rid(slave_if[5].rid), .s5_rdata(slave_if[5].rdata), .s5_rresp(slave_if[5].rresp),
        .s5_rlast(slave_if[5].rlast), .s5_rvalid(slave_if[5].rvalid), .s5_rready(slave_if[5].rready),        
        // Slave 6 interface connections
        .s6_awid(slave_if[6].awid), .s6_awaddr(slave_if[6].awaddr), .s6_awlen(slave_if[6].awlen),
        .s6_awsize(slave_if[6].awsize), .s6_awburst(slave_if[6].awburst), .s6_awlock(slave_if[6].awlock),
        .s6_awcache(slave_if[6].awcache), .s6_awprot(slave_if[6].awprot), .s6_awqos(slave_if[6].awqos),
        .s6_awvalid(slave_if[6].awvalid), .s6_awready(slave_if[6].awready),
        .s6_wdata(slave_if[6].wdata), .s6_wstrb(slave_if[6].wstrb), .s6_wlast(slave_if[6].wlast),
        .s6_wvalid(slave_if[6].wvalid), .s6_wready(slave_if[6].wready),
        .s6_bid(slave_if[6].bid), .s6_bresp(slave_if[6].bresp), .s6_bvalid(slave_if[6].bvalid),
        .s6_bready(slave_if[6].bready), .s6_arid(slave_if[6].arid), .s6_araddr(slave_if[6].araddr),
        .s6_arlen(slave_if[6].arlen), .s6_arsize(slave_if[6].arsize), .s6_arburst(slave_if[6].arburst),
        .s6_arlock(slave_if[6].arlock), .s6_arcache(slave_if[6].arcache), .s6_arprot(slave_if[6].arprot),
        .s6_arqos(slave_if[6].arqos), .s6_arvalid(slave_if[6].arvalid), .s6_arready(slave_if[6].arready),
        .s6_rid(slave_if[6].rid), .s6_rdata(slave_if[6].rdata), .s6_rresp(slave_if[6].rresp),
        .s6_rlast(slave_if[6].rlast), .s6_rvalid(slave_if[6].rvalid), .s6_rready(slave_if[6].rready),        
        // Slave 7 interface connections
        .s7_awid(slave_if[7].awid), .s7_awaddr(slave_if[7].awaddr), .s7_awlen(slave_if[7].awlen),
        .s7_awsize(slave_if[7].awsize), .s7_awburst(slave_if[7].awburst), .s7_awlock(slave_if[7].awlock),
        .s7_awcache(slave_if[7].awcache), .s7_awprot(slave_if[7].awprot), .s7_awqos(slave_if[7].awqos),
        .s7_awvalid(slave_if[7].awvalid), .s7_awready(slave_if[7].awready),
        .s7_wdata(slave_if[7].wdata), .s7_wstrb(slave_if[7].wstrb), .s7_wlast(slave_if[7].wlast),
        .s7_wvalid(slave_if[7].wvalid), .s7_wready(slave_if[7].wready),
        .s7_bid(slave_if[7].bid), .s7_bresp(slave_if[7].bresp), .s7_bvalid(slave_if[7].bvalid),
        .s7_bready(slave_if[7].bready), .s7_arid(slave_if[7].arid), .s7_araddr(slave_if[7].araddr),
        .s7_arlen(slave_if[7].arlen), .s7_arsize(slave_if[7].arsize), .s7_arburst(slave_if[7].arburst),
        .s7_arlock(slave_if[7].arlock), .s7_arcache(slave_if[7].arcache), .s7_arprot(slave_if[7].arprot),
        .s7_arqos(slave_if[7].arqos), .s7_arvalid(slave_if[7].arvalid), .s7_arready(slave_if[7].arready),
        .s7_rid(slave_if[7].rid), .s7_rdata(slave_if[7].rdata), .s7_rresp(slave_if[7].rresp),
        .s7_rlast(slave_if[7].rlast), .s7_rvalid(slave_if[7].rvalid), .s7_rready(slave_if[7].rready),        
        // Slave 8 interface connections
        .s8_awid(slave_if[8].awid), .s8_awaddr(slave_if[8].awaddr), .s8_awlen(slave_if[8].awlen),
        .s8_awsize(slave_if[8].awsize), .s8_awburst(slave_if[8].awburst), .s8_awlock(slave_if[8].awlock),
        .s8_awcache(slave_if[8].awcache), .s8_awprot(slave_if[8].awprot), .s8_awqos(slave_if[8].awqos),
        .s8_awvalid(slave_if[8].awvalid), .s8_awready(slave_if[8].awready),
        .s8_wdata(slave_if[8].wdata), .s8_wstrb(slave_if[8].wstrb), .s8_wlast(slave_if[8].wlast),
        .s8_wvalid(slave_if[8].wvalid), .s8_wready(slave_if[8].wready),
        .s8_bid(slave_if[8].bid), .s8_bresp(slave_if[8].bresp), .s8_bvalid(slave_if[8].bvalid),
        .s8_bready(slave_if[8].bready), .s8_arid(slave_if[8].arid), .s8_araddr(slave_if[8].araddr),
        .s8_arlen(slave_if[8].arlen), .s8_arsize(slave_if[8].arsize), .s8_arburst(slave_if[8].arburst),
        .s8_arlock(slave_if[8].arlock), .s8_arcache(slave_if[8].arcache), .s8_arprot(slave_if[8].arprot),
        .s8_arqos(slave_if[8].arqos), .s8_arvalid(slave_if[8].arvalid), .s8_arready(slave_if[8].arready),
        .s8_rid(slave_if[8].rid), .s8_rdata(slave_if[8].rdata), .s8_rresp(slave_if[8].rresp),
        .s8_rlast(slave_if[8].rlast), .s8_rvalid(slave_if[8].rvalid), .s8_rready(slave_if[8].rready),        
        // Slave 9 interface connections
        .s9_awid(slave_if[9].awid), .s9_awaddr(slave_if[9].awaddr), .s9_awlen(slave_if[9].awlen),
        .s9_awsize(slave_if[9].awsize), .s9_awburst(slave_if[9].awburst), .s9_awlock(slave_if[9].awlock),
        .s9_awcache(slave_if[9].awcache), .s9_awprot(slave_if[9].awprot), .s9_awqos(slave_if[9].awqos),
        .s9_awvalid(slave_if[9].awvalid), .s9_awready(slave_if[9].awready),
        .s9_wdata(slave_if[9].wdata), .s9_wstrb(slave_if[9].wstrb), .s9_wlast(slave_if[9].wlast),
        .s9_wvalid(slave_if[9].wvalid), .s9_wready(slave_if[9].wready),
        .s9_bid(slave_if[9].bid), .s9_bresp(slave_if[9].bresp), .s9_bvalid(slave_if[9].bvalid),
        .s9_bready(slave_if[9].bready), .s9_arid(slave_if[9].arid), .s9_araddr(slave_if[9].araddr),
        .s9_arlen(slave_if[9].arlen), .s9_arsize(slave_if[9].arsize), .s9_arburst(slave_if[9].arburst),
        .s9_arlock(slave_if[9].arlock), .s9_arcache(slave_if[9].arcache), .s9_arprot(slave_if[9].arprot),
        .s9_arqos(slave_if[9].arqos), .s9_arvalid(slave_if[9].arvalid), .s9_arready(slave_if[9].arready),
        .s9_rid(slave_if[9].rid), .s9_rdata(slave_if[9].rdata), .s9_rresp(slave_if[9].rresp),
        .s9_rlast(slave_if[9].rlast), .s9_rvalid(slave_if[9].rvalid), .s9_rready(slave_if[9].rready),        
        // Slave 10 interface connections
        .s10_awid(slave_if[10].awid), .s10_awaddr(slave_if[10].awaddr), .s10_awlen(slave_if[10].awlen),
        .s10_awsize(slave_if[10].awsize), .s10_awburst(slave_if[10].awburst), .s10_awlock(slave_if[10].awlock),
        .s10_awcache(slave_if[10].awcache), .s10_awprot(slave_if[10].awprot), .s10_awqos(slave_if[10].awqos),
        .s10_awvalid(slave_if[10].awvalid), .s10_awready(slave_if[10].awready),
        .s10_wdata(slave_if[10].wdata), .s10_wstrb(slave_if[10].wstrb), .s10_wlast(slave_if[10].wlast),
        .s10_wvalid(slave_if[10].wvalid), .s10_wready(slave_if[10].wready),
        .s10_bid(slave_if[10].bid), .s10_bresp(slave_if[10].bresp), .s10_bvalid(slave_if[10].bvalid),
        .s10_bready(slave_if[10].bready), .s10_arid(slave_if[10].arid), .s10_araddr(slave_if[10].araddr),
        .s10_arlen(slave_if[10].arlen), .s10_arsize(slave_if[10].arsize), .s10_arburst(slave_if[10].arburst),
        .s10_arlock(slave_if[10].arlock), .s10_arcache(slave_if[10].arcache), .s10_arprot(slave_if[10].arprot),
        .s10_arqos(slave_if[10].arqos), .s10_arvalid(slave_if[10].arvalid), .s10_arready(slave_if[10].arready),
        .s10_rid(slave_if[10].rid), .s10_rdata(slave_if[10].rdata), .s10_rresp(slave_if[10].rresp),
        .s10_rlast(slave_if[10].rlast), .s10_rvalid(slave_if[10].rvalid), .s10_rready(slave_if[10].rready),        
        // Slave 11 interface connections
        .s11_awid(slave_if[11].awid), .s11_awaddr(slave_if[11].awaddr), .s11_awlen(slave_if[11].awlen),
        .s11_awsize(slave_if[11].awsize), .s11_awburst(slave_if[11].awburst), .s11_awlock(slave_if[11].awlock),
        .s11_awcache(slave_if[11].awcache), .s11_awprot(slave_if[11].awprot), .s11_awqos(slave_if[11].awqos),
        .s11_awvalid(slave_if[11].awvalid), .s11_awready(slave_if[11].awready),
        .s11_wdata(slave_if[11].wdata), .s11_wstrb(slave_if[11].wstrb), .s11_wlast(slave_if[11].wlast),
        .s11_wvalid(slave_if[11].wvalid), .s11_wready(slave_if[11].wready),
        .s11_bid(slave_if[11].bid), .s11_bresp(slave_if[11].bresp), .s11_bvalid(slave_if[11].bvalid),
        .s11_bready(slave_if[11].bready), .s11_arid(slave_if[11].arid), .s11_araddr(slave_if[11].araddr),
        .s11_arlen(slave_if[11].arlen), .s11_arsize(slave_if[11].arsize), .s11_arburst(slave_if[11].arburst),
        .s11_arlock(slave_if[11].arlock), .s11_arcache(slave_if[11].arcache), .s11_arprot(slave_if[11].arprot),
        .s11_arqos(slave_if[11].arqos), .s11_arvalid(slave_if[11].arvalid), .s11_arready(slave_if[11].arready),
        .s11_rid(slave_if[11].rid), .s11_rdata(slave_if[11].rdata), .s11_rresp(slave_if[11].rresp),
        .s11_rlast(slave_if[11].rlast), .s11_rvalid(slave_if[11].rvalid), .s11_rready(slave_if[11].rready),        
        // Slave 12 interface connections
        .s12_awid(slave_if[12].awid), .s12_awaddr(slave_if[12].awaddr), .s12_awlen(slave_if[12].awlen),
        .s12_awsize(slave_if[12].awsize), .s12_awburst(slave_if[12].awburst), .s12_awlock(slave_if[12].awlock),
        .s12_awcache(slave_if[12].awcache), .s12_awprot(slave_if[12].awprot), .s12_awqos(slave_if[12].awqos),
        .s12_awvalid(slave_if[12].awvalid), .s12_awready(slave_if[12].awready),
        .s12_wdata(slave_if[12].wdata), .s12_wstrb(slave_if[12].wstrb), .s12_wlast(slave_if[12].wlast),
        .s12_wvalid(slave_if[12].wvalid), .s12_wready(slave_if[12].wready),
        .s12_bid(slave_if[12].bid), .s12_bresp(slave_if[12].bresp), .s12_bvalid(slave_if[12].bvalid),
        .s12_bready(slave_if[12].bready), .s12_arid(slave_if[12].arid), .s12_araddr(slave_if[12].araddr),
        .s12_arlen(slave_if[12].arlen), .s12_arsize(slave_if[12].arsize), .s12_arburst(slave_if[12].arburst),
        .s12_arlock(slave_if[12].arlock), .s12_arcache(slave_if[12].arcache), .s12_arprot(slave_if[12].arprot),
        .s12_arqos(slave_if[12].arqos), .s12_arvalid(slave_if[12].arvalid), .s12_arready(slave_if[12].arready),
        .s12_rid(slave_if[12].rid), .s12_rdata(slave_if[12].rdata), .s12_rresp(slave_if[12].rresp),
        .s12_rlast(slave_if[12].rlast), .s12_rvalid(slave_if[12].rvalid), .s12_rready(slave_if[12].rready),        
        // Slave 13 interface connections
        .s13_awid(slave_if[13].awid), .s13_awaddr(slave_if[13].awaddr), .s13_awlen(slave_if[13].awlen),
        .s13_awsize(slave_if[13].awsize), .s13_awburst(slave_if[13].awburst), .s13_awlock(slave_if[13].awlock),
        .s13_awcache(slave_if[13].awcache), .s13_awprot(slave_if[13].awprot), .s13_awqos(slave_if[13].awqos),
        .s13_awvalid(slave_if[13].awvalid), .s13_awready(slave_if[13].awready),
        .s13_wdata(slave_if[13].wdata), .s13_wstrb(slave_if[13].wstrb), .s13_wlast(slave_if[13].wlast),
        .s13_wvalid(slave_if[13].wvalid), .s13_wready(slave_if[13].wready),
        .s13_bid(slave_if[13].bid), .s13_bresp(slave_if[13].bresp), .s13_bvalid(slave_if[13].bvalid),
        .s13_bready(slave_if[13].bready), .s13_arid(slave_if[13].arid), .s13_araddr(slave_if[13].araddr),
        .s13_arlen(slave_if[13].arlen), .s13_arsize(slave_if[13].arsize), .s13_arburst(slave_if[13].arburst),
        .s13_arlock(slave_if[13].arlock), .s13_arcache(slave_if[13].arcache), .s13_arprot(slave_if[13].arprot),
        .s13_arqos(slave_if[13].arqos), .s13_arvalid(slave_if[13].arvalid), .s13_arready(slave_if[13].arready),
        .s13_rid(slave_if[13].rid), .s13_rdata(slave_if[13].rdata), .s13_rresp(slave_if[13].rresp),
        .s13_rlast(slave_if[13].rlast), .s13_rvalid(slave_if[13].rvalid), .s13_rready(slave_if[13].rready),        
        // Slave 14 interface connections
        .s14_awid(slave_if[14].awid), .s14_awaddr(slave_if[14].awaddr), .s14_awlen(slave_if[14].awlen),
        .s14_awsize(slave_if[14].awsize), .s14_awburst(slave_if[14].awburst), .s14_awlock(slave_if[14].awlock),
        .s14_awcache(slave_if[14].awcache), .s14_awprot(slave_if[14].awprot), .s14_awqos(slave_if[14].awqos),
        .s14_awvalid(slave_if[14].awvalid), .s14_awready(slave_if[14].awready),
        .s14_wdata(slave_if[14].wdata), .s14_wstrb(slave_if[14].wstrb), .s14_wlast(slave_if[14].wlast),
        .s14_wvalid(slave_if[14].wvalid), .s14_wready(slave_if[14].wready),
        .s14_bid(slave_if[14].bid), .s14_bresp(slave_if[14].bresp), .s14_bvalid(slave_if[14].bvalid),
        .s14_bready(slave_if[14].bready), .s14_arid(slave_if[14].arid), .s14_araddr(slave_if[14].araddr),
        .s14_arlen(slave_if[14].arlen), .s14_arsize(slave_if[14].arsize), .s14_arburst(slave_if[14].arburst),
        .s14_arlock(slave_if[14].arlock), .s14_arcache(slave_if[14].arcache), .s14_arprot(slave_if[14].arprot),
        .s14_arqos(slave_if[14].arqos), .s14_arvalid(slave_if[14].arvalid), .s14_arready(slave_if[14].arready),
        .s14_rid(slave_if[14].rid), .s14_rdata(slave_if[14].rdata), .s14_rresp(slave_if[14].rresp),
        .s14_rlast(slave_if[14].rlast), .s14_rvalid(slave_if[14].rvalid), .s14_rready(slave_if[14].rready)
    );
    
    // Interface initialization for proper VIP+RTL integration
    initial begin
        // Initialize master interfaces to safe defaults (explicit unroll)

        master_if[0].awvalid <= 1'b0; master_if[0].wvalid <= 1'b0; master_if[0].bready <= 1'b1; master_if[0].arvalid <= 1'b0; master_if[0].rready <= 1'b1;
        master_if[1].awvalid <= 1'b0; master_if[1].wvalid <= 1'b0; master_if[1].bready <= 1'b1; master_if[1].arvalid <= 1'b0; master_if[1].rready <= 1'b1;
        master_if[2].awvalid <= 1'b0; master_if[2].wvalid <= 1'b0; master_if[2].bready <= 1'b1; master_if[2].arvalid <= 1'b0; master_if[2].rready <= 1'b1;
        master_if[3].awvalid <= 1'b0; master_if[3].wvalid <= 1'b0; master_if[3].bready <= 1'b1; master_if[3].arvalid <= 1'b0; master_if[3].rready <= 1'b1;
        master_if[4].awvalid <= 1'b0; master_if[4].wvalid <= 1'b0; master_if[4].bready <= 1'b1; master_if[4].arvalid <= 1'b0; master_if[4].rready <= 1'b1;
        master_if[5].awvalid <= 1'b0; master_if[5].wvalid <= 1'b0; master_if[5].bready <= 1'b1; master_if[5].arvalid <= 1'b0; master_if[5].rready <= 1'b1;
        master_if[6].awvalid <= 1'b0; master_if[6].wvalid <= 1'b0; master_if[6].bready <= 1'b1; master_if[6].arvalid <= 1'b0; master_if[6].rready <= 1'b1;
        master_if[7].awvalid <= 1'b0; master_if[7].wvalid <= 1'b0; master_if[7].bready <= 1'b1; master_if[7].arvalid <= 1'b0; master_if[7].rready <= 1'b1;
        master_if[8].awvalid <= 1'b0; master_if[8].wvalid <= 1'b0; master_if[8].bready <= 1'b1; master_if[8].arvalid <= 1'b0; master_if[8].rready <= 1'b1;
        master_if[9].awvalid <= 1'b0; master_if[9].wvalid <= 1'b0; master_if[9].bready <= 1'b1; master_if[9].arvalid <= 1'b0; master_if[9].rready <= 1'b1;
        master_if[10].awvalid <= 1'b0; master_if[10].wvalid <= 1'b0; master_if[10].bready <= 1'b1; master_if[10].arvalid <= 1'b0; master_if[10].rready <= 1'b1;
        master_if[11].awvalid <= 1'b0; master_if[11].wvalid <= 1'b0; master_if[11].bready <= 1'b1; master_if[11].arvalid <= 1'b0; master_if[11].rready <= 1'b1;
        master_if[12].awvalid <= 1'b0; master_if[12].wvalid <= 1'b0; master_if[12].bready <= 1'b1; master_if[12].arvalid <= 1'b0; master_if[12].rready <= 1'b1;
        master_if[13].awvalid <= 1'b0; master_if[13].wvalid <= 1'b0; master_if[13].bready <= 1'b1; master_if[13].arvalid <= 1'b0; master_if[13].rready <= 1'b1;
        master_if[14].awvalid <= 1'b0; master_if[14].wvalid <= 1'b0; master_if[14].bready <= 1'b1; master_if[14].arvalid <= 1'b0; master_if[14].rready <= 1'b1;
        
        // Initialize slave interfaces to safe defaults (explicit unroll)  

        slave_if[0].awready <= 1'b0; slave_if[0].wready <= 1'b0; slave_if[0].bvalid <= 1'b0; slave_if[0].arready <= 1'b0; slave_if[0].rvalid <= 1'b0;
        slave_if[1].awready <= 1'b0; slave_if[1].wready <= 1'b0; slave_if[1].bvalid <= 1'b0; slave_if[1].arready <= 1'b0; slave_if[1].rvalid <= 1'b0;
        slave_if[2].awready <= 1'b0; slave_if[2].wready <= 1'b0; slave_if[2].bvalid <= 1'b0; slave_if[2].arready <= 1'b0; slave_if[2].rvalid <= 1'b0;
        slave_if[3].awready <= 1'b0; slave_if[3].wready <= 1'b0; slave_if[3].bvalid <= 1'b0; slave_if[3].arready <= 1'b0; slave_if[3].rvalid <= 1'b0;
        slave_if[4].awready <= 1'b0; slave_if[4].wready <= 1'b0; slave_if[4].bvalid <= 1'b0; slave_if[4].arready <= 1'b0; slave_if[4].rvalid <= 1'b0;
        slave_if[5].awready <= 1'b0; slave_if[5].wready <= 1'b0; slave_if[5].bvalid <= 1'b0; slave_if[5].arready <= 1'b0; slave_if[5].rvalid <= 1'b0;
        slave_if[6].awready <= 1'b0; slave_if[6].wready <= 1'b0; slave_if[6].bvalid <= 1'b0; slave_if[6].arready <= 1'b0; slave_if[6].rvalid <= 1'b0;
        slave_if[7].awready <= 1'b0; slave_if[7].wready <= 1'b0; slave_if[7].bvalid <= 1'b0; slave_if[7].arready <= 1'b0; slave_if[7].rvalid <= 1'b0;
        slave_if[8].awready <= 1'b0; slave_if[8].wready <= 1'b0; slave_if[8].bvalid <= 1'b0; slave_if[8].arready <= 1'b0; slave_if[8].rvalid <= 1'b0;
        slave_if[9].awready <= 1'b0; slave_if[9].wready <= 1'b0; slave_if[9].bvalid <= 1'b0; slave_if[9].arready <= 1'b0; slave_if[9].rvalid <= 1'b0;
        slave_if[10].awready <= 1'b0; slave_if[10].wready <= 1'b0; slave_if[10].bvalid <= 1'b0; slave_if[10].arready <= 1'b0; slave_if[10].rvalid <= 1'b0;
        slave_if[11].awready <= 1'b0; slave_if[11].wready <= 1'b0; slave_if[11].bvalid <= 1'b0; slave_if[11].arready <= 1'b0; slave_if[11].rvalid <= 1'b0;
        slave_if[12].awready <= 1'b0; slave_if[12].wready <= 1'b0; slave_if[12].bvalid <= 1'b0; slave_if[12].arready <= 1'b0; slave_if[12].rvalid <= 1'b0;
        slave_if[13].awready <= 1'b0; slave_if[13].wready <= 1'b0; slave_if[13].bvalid <= 1'b0; slave_if[13].arready <= 1'b0; slave_if[13].rvalid <= 1'b0;
        slave_if[14].awready <= 1'b0; slave_if[14].wready <= 1'b0; slave_if[14].bvalid <= 1'b0; slave_if[14].arready <= 1'b0; slave_if[14].rvalid <= 1'b0;
        
        $display("[VIP+RTL] All interfaces properly instantiated and initialized");
        $display("[VIP+RTL] Master interfaces: %0d, Slave interfaces: %0d", 15, 15);
    end
    
    // Waveform dumping
    `ifdef DUMP_FSDB
        initial begin
            $fsdbDumpfile("waves/vip_rtl_integration.fsdb");
            $fsdbDumpvars(0, hdl_top);
            $display("[FSDB] Waveform dumping enabled for VIP+RTL integration");
        end
    `endif
    
    `ifdef DUMP_VCD
        initial begin
            $dumpfile("waves/vip_rtl_integration.vcd");
            $dumpvars(0, hdl_top);
            $display("[VCD] Waveform dumping enabled for VIP+RTL integration");
        end
    `endif
    
endmodule