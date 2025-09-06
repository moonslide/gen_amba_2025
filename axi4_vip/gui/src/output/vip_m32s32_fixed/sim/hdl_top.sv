// Simple top module for compilation test
`include "uvm_macros.svh"

module hdl_top;
    import uvm_pkg::*;
    import axi4_vip_pkg::*;
    
    // Clock and reset
    logic aclk;
    logic aresetn;
    
    // Clock generation
    initial begin
        aclk = 0;
        forever #5 aclk = ~aclk;
    end
    
    // Reset generation
    initial begin
        aresetn = 0;
        #100 aresetn = 1;
    end
    
    // Interface instances
    axi4_if master_if[32](aclk, aresetn);
    axi4_if slave_if[32](aclk, aresetn);
    
    // Run test
    initial begin
        // Set interfaces in config_db
        for(int i = 0; i < 32; i++) begin
            uvm_config_db#(virtual axi4_if)::set(null, $sformatf("uvm_test_top.env.master_agents[%0d].*", i), "vif", master_if[i]);
            uvm_config_db#(virtual axi4_if)::set(null, $sformatf("uvm_test_top.env.slave_agents[%0d].*", i), "vif", slave_if[i]);
        end
        
        // Start UVM test
        run_test();
    end
    
endmodule