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
        #10000 $display("RTL+VIP Integration Test Complete");
        $finish;
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
    
    // Waveform dumping
    `ifdef DUMP_FSDB
        initial begin
            $fsdbDumpfile("waves/vip_rtl_integration.fsdb");
            $fsdbDumpvars(0, hdl_top);
            $display("[FSDB] Waveform dumping enabled");
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
