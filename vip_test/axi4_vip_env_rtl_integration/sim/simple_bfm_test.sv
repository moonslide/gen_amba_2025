// Simple test program to debug BFM connectivity
program simple_bfm_test;
    
    initial begin
        $display("[%0t] Simple BFM test starting", $time);
        
        // Wait for reset
        @(posedge hdl_top.aresetn);
        $display("[%0t] Reset released", $time);
        
        // Wait a bit more
        repeat(10) @(posedge hdl_top.aclk);
        
        // Try to drive a simple write transaction through BFM
        $display("[%0t] Driving write address", $time);
        hdl_top.master_bfm[0].master_driver_bfm_h.drive_write_addr(
            .id(4'h1),
            .addr(32'h1000_0000),
            .len(8'h0),
            .size(3'h2),
            .burst(2'b01)
        );
        
        $display("[%0t] Write address completed", $time);
        
        // End simulation
        #1000;
        $display("[%0t] Test completed", $time);
        $finish;
    end
    
endprogram