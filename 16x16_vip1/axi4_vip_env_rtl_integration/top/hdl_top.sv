//==============================================================================
// HDL Top - RTL Integration for 16x16 AXI4 Matrix
// Generated for VIP+RTL Integration
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
        
        // Basic simulation control
        // Let UVM control simulation end
        // Removed automatic $finish to allow transactions to complete
    end
    
    // RTL DUT instantiation - 16x16 interconnect
    axi4_interconnect_m16s16 #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .USER_WIDTH(USER_WIDTH)
    ) dut (
        .aclk(aclk),
        .aresetn(aresetn)
        
        // Master connections will be handled by UVM interface binding
        // in hvl_top, not direct port connections here
        
        // For basic RTL-only simulation, default values are used
    );
    
    // Enhanced waveform dumping with explicit clock signal visibility fix
    `ifdef DUMP_FSDB
        initial begin
            $fsdbDumpfile("waves/vip_rtl_integration.fsdb");
            
            // Dump top level including the main clock
            $fsdbDumpvars(0, hdl_top);
            $fsdbDumpvars(0, hdl_top.aclk);    // Explicit top-level clock dump
            $fsdbDumpvars(0, hdl_top.aresetn); // Explicit top-level reset dump
            
            // Dump all master interface signals individually WITH EXPLICIT CLOCKS
            for (int i = 0; i < 16; i++) begin
                $fsdbDumpvars(0, hdl_top.master_if[i]);
                $fsdbDumpvars(0, hdl_top.master_if[i].aclk);  // Explicit interface clock
            end
            
            // Dump all slave interface signals individually WITH EXPLICIT CLOCKS
            for (int i = 0; i < 16; i++) begin
                $fsdbDumpvars(0, hdl_top.slave_if[i]);
                $fsdbDumpvars(0, hdl_top.slave_if[i].aclk);  // Explicit interface clock
            end
            
            // Dump RTL DUT wrapper and all its internal signals WITH EXPLICIT CLOCKS
            $fsdbDumpvars(0, hdl_top.dut);
            $fsdbDumpvars(0, hdl_top.dut.clk);    // DUT wrapper clock input
            $fsdbDumpvars(0, hdl_top.dut.rst_n);  // DUT wrapper reset input
            
            // Try to dump the RTL interconnect module clock specifically (if it exists)
            $fsdbDumpvars(0, hdl_top.dut.rtl_interconnect_inst.aclk);
            
            $display("[FSDB] Enhanced waveform dumping enabled with explicit clock signals");
        end
    `endif
    
    `ifdef DUMP_VCD
        initial begin
            $dumpfile("waves/vip_rtl_integration.vcd");
            $dumpvars(0, hdl_top);
            $display("[VCD] Waveform dumping enabled");
        end
    `endif
    
endmodule
