// Simple test to verify slave connectivity
module verify_slave_connectivity;
   initial begin
      $display("[%0t] Starting slave connectivity verification", $time);
      
      // Wait for reset
      wait(hdl_top.aresetn == 1'b1);
      repeat(10) @(posedge hdl_top.aclk);
      
      // Force master 0 to send a write to slave 0 (address 0x0000)
      force hdl_top.dut.axi_interconnect.M0_AWADDR = 32'h0000_0100;
      force hdl_top.dut.axi_interconnect.M0_AWVALID = 1'b1;
      force hdl_top.dut.axi_interconnect.M0_AWID = 4'h1;
      force hdl_top.dut.axi_interconnect.M0_AWLEN = 8'h0;
      force hdl_top.dut.axi_interconnect.M0_AWSIZE = 3'h2;
      force hdl_top.dut.axi_interconnect.M0_AWBURST = 2'h1;
      
      $display("[%0t] Forcing M0_AWADDR=0x%08x, M0_AWVALID=%0b", $time, 
               hdl_top.dut.axi_interconnect.M0_AWADDR, 
               hdl_top.dut.axi_interconnect.M0_AWVALID);
      
      // Wait and check if any slave responds
      repeat(20) @(posedge hdl_top.aclk);
      
      // Check slave 0 signals
      $display("[%0t] Slave 0 AWVALID=%0b, AWADDR=0x%08x", $time,
               hdl_top.dut.axi_interconnect.S0_AWVALID,
               hdl_top.dut.axi_interconnect.S0_AWADDR);
               
      // Try slave 1 (address 0x2000)
      release hdl_top.dut.axi_interconnect.M0_AWADDR;
      force hdl_top.dut.axi_interconnect.M0_AWADDR = 32'h0000_2100;
      
      repeat(20) @(posedge hdl_top.aclk);
      
      $display("[%0t] Slave 1 AWVALID=%0b, AWADDR=0x%08x", $time,
               hdl_top.dut.axi_interconnect.S1_AWVALID,
               hdl_top.dut.axi_interconnect.S1_AWADDR);
               
      // Release all forces
      release hdl_top.dut.axi_interconnect.M0_AWADDR;
      release hdl_top.dut.axi_interconnect.M0_AWVALID;
      release hdl_top.dut.axi_interconnect.M0_AWID;
      release hdl_top.dut.axi_interconnect.M0_AWLEN;
      release hdl_top.dut.axi_interconnect.M0_AWSIZE;
      release hdl_top.dut.axi_interconnect.M0_AWBURST;
      
      $display("[%0t] Connectivity test completed", $time);
   end
endmodule