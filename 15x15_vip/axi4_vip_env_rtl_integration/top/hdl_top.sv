//==============================================================================
// HDL Top - VIP+RTL Integration for 15x15 AXI4 Matrix
// Generated with proper interface instantiation - Warning-free
// Date: 2025-08-09 12:32:51
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
    // Master agent BFMs - connected to AXI interfaces
    genvar i;
    generate
        for (i = 0; i < 15; i++) begin : gen_master_bfms
            axi4_master_agent_bfm #(
                .ADDR_WIDTH(ADDRESS_WIDTH),
                .DATA_WIDTH(DATA_WIDTH),
                .ID_WIDTH(ID_WIDTH)
            ) master_bfm (
                .aclk(aclk),
                .aresetn(aresetn),
                .axi_intf(master_if[i])
            );
        end
    endgenerate
    
    // Slave agent BFMs - connected to slave interfaces
    generate
        for (i = 0; i < 15; i++) begin : gen_slave_bfms
            axi4_slave_agent_bfm #(
                .ADDR_WIDTH(ADDRESS_WIDTH),
                .DATA_WIDTH(DATA_WIDTH),
                .ID_WIDTH(ID_WIDTH)  // Base ID width to match DUT expectations
            ) slave_bfm (
                .aclk(aclk),
                .aresetn(aresetn),
                .axi_intf(slave_if[i])
            );
        end
    endgenerate

    // RTL DUT instantiation using proper dut_wrapper with correct signal directions
    dut_wrapper #(
        .ADDR_WIDTH(ADDRESS_WIDTH),
        .DATA_WIDTH(DATA_WIDTH), 
        .ID_WIDTH(ID_WIDTH),
        .NUM_MASTERS(15),
        .NUM_SLAVES(15)
    ) dut (
        .clk(aclk),
        .rst_n(aresetn),
        .master_if(master_if),  // Master BFMs connect to DUT as masters
        .slave_if(slave_if)     // Slave BFMs connect to DUT slave ports
    );
    
    // Comprehensive FSDB waveform dumping for VIP+RTL debugging
    initial begin
        `ifdef DUMP_VCD
            $dumpfile("axi4_sim.vcd");
            $dumpvars(0, hdl_top);
        `endif
        
        `ifdef DUMP_FSDB
            // Create waves directory if it doesn't exist and use correct FSDB filename
            $system("mkdir -p waves");
            $fsdbDumpfile("waves/axi4_vip.fsdb");
            
            // Use correct syntax for dumping all signals
            $fsdbDumpvars(0, "hdl_top", "+all");
            
            $display("[HDL_TOP] FSDB dumping enabled with +all option to waves/axi4_vip.fsdb");
            $display("[HDL_TOP] All signals will be dumped for comprehensive analysis");
        `endif
        
        // Also dump key signals for debugging
        $display("[HDL_TOP] Starting waveform capture at time %0t", $time);
        $display("[HDL_TOP] Clock period: 10ns (100MHz)");
        $display("[HDL_TOP] Reset released at: 100ns");
    end
    
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

        slave_if[0].awready <= 1'b1; slave_if[0].wready <= 1'b1; slave_if[0].bvalid <= 1'b0; slave_if[0].arready <= 1'b1; slave_if[0].rvalid <= 1'b0;
        slave_if[1].awready <= 1'b1; slave_if[1].wready <= 1'b1; slave_if[1].bvalid <= 1'b0; slave_if[1].arready <= 1'b1; slave_if[1].rvalid <= 1'b0;
        slave_if[2].awready <= 1'b1; slave_if[2].wready <= 1'b1; slave_if[2].bvalid <= 1'b0; slave_if[2].arready <= 1'b1; slave_if[2].rvalid <= 1'b0;
        slave_if[3].awready <= 1'b1; slave_if[3].wready <= 1'b1; slave_if[3].bvalid <= 1'b0; slave_if[3].arready <= 1'b1; slave_if[3].rvalid <= 1'b0;
        slave_if[4].awready <= 1'b1; slave_if[4].wready <= 1'b1; slave_if[4].bvalid <= 1'b0; slave_if[4].arready <= 1'b1; slave_if[4].rvalid <= 1'b0;
        slave_if[5].awready <= 1'b1; slave_if[5].wready <= 1'b1; slave_if[5].bvalid <= 1'b0; slave_if[5].arready <= 1'b1; slave_if[5].rvalid <= 1'b0;
        slave_if[6].awready <= 1'b1; slave_if[6].wready <= 1'b1; slave_if[6].bvalid <= 1'b0; slave_if[6].arready <= 1'b1; slave_if[6].rvalid <= 1'b0;
        slave_if[7].awready <= 1'b1; slave_if[7].wready <= 1'b1; slave_if[7].bvalid <= 1'b0; slave_if[7].arready <= 1'b1; slave_if[7].rvalid <= 1'b0;
        slave_if[8].awready <= 1'b1; slave_if[8].wready <= 1'b1; slave_if[8].bvalid <= 1'b0; slave_if[8].arready <= 1'b1; slave_if[8].rvalid <= 1'b0;
        slave_if[9].awready <= 1'b1; slave_if[9].wready <= 1'b1; slave_if[9].bvalid <= 1'b0; slave_if[9].arready <= 1'b1; slave_if[9].rvalid <= 1'b0;
        slave_if[10].awready <= 1'b1; slave_if[10].wready <= 1'b1; slave_if[10].bvalid <= 1'b0; slave_if[10].arready <= 1'b1; slave_if[10].rvalid <= 1'b0;
        slave_if[11].awready <= 1'b1; slave_if[11].wready <= 1'b1; slave_if[11].bvalid <= 1'b0; slave_if[11].arready <= 1'b1; slave_if[11].rvalid <= 1'b0;
        slave_if[12].awready <= 1'b1; slave_if[12].wready <= 1'b1; slave_if[12].bvalid <= 1'b0; slave_if[12].arready <= 1'b1; slave_if[12].rvalid <= 1'b0;
        slave_if[13].awready <= 1'b1; slave_if[13].wready <= 1'b1; slave_if[13].bvalid <= 1'b0; slave_if[13].arready <= 1'b1; slave_if[13].rvalid <= 1'b0;
        slave_if[14].awready <= 1'b1; slave_if[14].wready <= 1'b1; slave_if[14].bvalid <= 1'b0; slave_if[14].arready <= 1'b1; slave_if[14].rvalid <= 1'b0;
    end

endmodule : hdl_top
