// Simple test to check slave BFM connectivity
// This test will monitor signals at the slave BFM interfaces

module test_slave_connectivity;
    initial begin
        #200000; // Wait for some time after reset
        
        $display("===== Checking Slave BFM Connectivity =====");
        
        // Check slave interfaces directly
        $display("\n--- Checking Slave Interface 0 ---");
        $display("slave_if[0].awvalid = %b", hdl_top.slave_if[0].awvalid);
        $display("slave_if[0].awready = %b", hdl_top.slave_if[0].awready);
        $display("slave_if[0].arvalid = %b", hdl_top.slave_if[0].arvalid);
        $display("slave_if[0].arready = %b", hdl_top.slave_if[0].arready);
        
        // Monitor slave 0 for a while
        repeat(100) @(posedge hdl_top.aclk) begin
            if (hdl_top.slave_if[0].awvalid) begin
                $display("Slave 0 received AWVALID at time %0t, addr=0x%08x, id=%0d", 
                         $time, hdl_top.slave_if[0].awaddr, hdl_top.slave_if[0].awid);
            end
            if (hdl_top.slave_if[0].arvalid) begin
                $display("Slave 0 received ARVALID at time %0t, addr=0x%08x, id=%0d", 
                         $time, hdl_top.slave_if[0].araddr, hdl_top.slave_if[0].arid);
            end
        end
        
        // Also check DUT interconnect outputs
        $display("\n===== Checking DUT Interconnect Outputs =====");
        $display("Interconnect S0_AWVALID = %b", hdl_top.dut.axi_interconnect.S0_AWVALID);
        $display("Interconnect S0_AWREADY = %b", hdl_top.dut.axi_interconnect.S0_AWREADY);
        $display("Interconnect S0_ARVALID = %b", hdl_top.dut.axi_interconnect.S0_ARVALID);
        $display("Interconnect S0_ARREADY = %b", hdl_top.dut.axi_interconnect.S0_ARREADY);
        
        // Check master outputs too
        $display("\n===== Checking Master Outputs =====");
        $display("Master 0 AWVALID = %b", hdl_top.axi_if[0].awvalid);
        $display("Master 0 AWADDR = 0x%08x", hdl_top.axi_if[0].awaddr);
        $display("Interconnect M0_AWVALID = %b", hdl_top.dut.axi_interconnect.M0_AWVALID);
        $display("Interconnect M0_AWADDR = 0x%08x", hdl_top.dut.axi_interconnect.M0_AWADDR);
        
        $display("\n===== End of Connectivity Check =====\n");
    end
endmodule