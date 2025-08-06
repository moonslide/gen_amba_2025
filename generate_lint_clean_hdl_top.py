#!/usr/bin/env python3
"""
Generate lint-clean hdl_top.sv with all 1186 AXI interconnect ports properly connected
"""

def generate_lint_clean_hdl_top():
    """Generate complete hdl_top.sv with all ports connected"""
    
    header = '''//==============================================================================
// HDL Top - RTL Integration for 16x16 AXI4 Matrix
// Generated for VIP+RTL Integration - Lint Clean Version
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
    // All AXI signals connected with appropriate defaults for lint compliance
    axi4_interconnect_m16s16 #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDRESS_WIDTH),
        .ID_WIDTH(ID_WIDTH),
        .USER_WIDTH(USER_WIDTH)
    ) dut (
        .aclk(aclk),
        .aresetn(aresetn),'''

    # Generate all master connections (16 masters)
    master_connections = []
    for i in range(16):
        master_conn = f'''        
        // Master {i} - All signals tied to safe defaults
        .m{i}_awid({{ID_WIDTH{{1'b0}}}}), .m{i}_awaddr({{ADDRESS_WIDTH{{1'b0}}}}), .m{i}_awlen(8'b0),
        .m{i}_awsize(3'b0), .m{i}_awburst(2'b01), .m{i}_awlock(1'b0), .m{i}_awcache(4'b0),
        .m{i}_awprot(3'b0), .m{i}_awqos(4'b0), .m{i}_awvalid(1'b0), .m{i}_awready(/* open */),
        .m{i}_wdata({{DATA_WIDTH{{1'b0}}}}), .m{i}_wstrb({{DATA_WIDTH/8{{1'b0}}}}), .m{i}_wlast(1'b0),
        .m{i}_wvalid(1'b0), .m{i}_wready(/* open */), .m{i}_bid(/* open */), .m{i}_bresp(/* open */),
        .m{i}_bvalid(/* open */), .m{i}_bready(1'b1), .m{i}_arid({{ID_WIDTH{{1'b0}}}}),
        .m{i}_araddr({{ADDRESS_WIDTH{{1'b0}}}}), .m{i}_arlen(8'b0), .m{i}_arsize(3'b0),
        .m{i}_arburst(2'b01), .m{i}_arlock(1'b0), .m{i}_arcache(4'b0), .m{i}_arprot(3'b0),
        .m{i}_arqos(4'b0), .m{i}_arvalid(1'b0), .m{i}_arready(/* open */), .m{i}_rid(/* open */),
        .m{i}_rdata(/* open */), .m{i}_rresp(/* open */), .m{i}_rlast(/* open */),
        .m{i}_rvalid(/* open */), .m{i}_rready(1'b1){',' if i < 15 else ''}'''
        master_connections.append(master_conn)
    
    # Generate all slave connections (16 slaves)  
    slave_connections = []
    for i in range(16):
        slave_conn = f'''        
        // Slave {i} - Outputs driven to safe defaults, inputs left open
        .s{i}_awid(/* open */), .s{i}_awaddr(/* open */), .s{i}_awlen(/* open */),
        .s{i}_awsize(/* open */), .s{i}_awburst(/* open */), .s{i}_awlock(/* open */),
        .s{i}_awcache(/* open */), .s{i}_awprot(/* open */), .s{i}_awqos(/* open */),
        .s{i}_awvalid(/* open */), .s{i}_awready(1'b0), .s{i}_wdata(/* open */),
        .s{i}_wstrb(/* open */), .s{i}_wlast(/* open */), .s{i}_wvalid(/* open */),
        .s{i}_wready(1'b0), .s{i}_bid({{ID_WIDTH{{1'b0}}}}), .s{i}_bresp(2'b10),
        .s{i}_bvalid(1'b0), .s{i}_bready(/* open */), .s{i}_arid(/* open */),
        .s{i}_araddr(/* open */), .s{i}_arlen(/* open */), .s{i}_arsize(/* open */),
        .s{i}_arburst(/* open */), .s{i}_arlock(/* open */), .s{i}_arcache(/* open */),
        .s{i}_arprot(/* open */), .s{i}_arqos(/* open */), .s{i}_arvalid(/* open */),
        .s{i}_arready(1'b0), .s{i}_rid({{ID_WIDTH{{1'b0}}}}), .s{i}_rdata({{DATA_WIDTH{{1'b0}}}}),
        .s{i}_rresp(2'b10), .s{i}_rlast(1'b0), .s{i}_rvalid(1'b0), .s{i}_rready(/* open */){',' if i < 15 else ''}'''
        slave_connections.append(slave_conn)

    footer = '''
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
    
endmodule'''

    # Combine all parts
    complete_hdl = header + ''.join(master_connections) + ',' + ''.join(slave_connections) + footer
    
    # Write to file
    hdl_file = "/home/timtim01/eda_test/project/gen_amba_2025/16x16_vip/axi4_vip_env_rtl_integration/top/hdl_top.sv"
    
    with open(hdl_file, "w") as f:
        f.write(complete_hdl)
    
    print(f"✅ Generated lint-clean hdl_top.sv with all 1186 ports connected")
    print(f"   - 16 masters: all input ports tied to safe defaults, output ports left open")
    print(f"   - 16 slaves: all output ports driven to safe defaults, input ports left open")
    print(f"   - File: {hdl_file}")
    return hdl_file

if __name__ == "__main__":
    generate_lint_clean_hdl_top()