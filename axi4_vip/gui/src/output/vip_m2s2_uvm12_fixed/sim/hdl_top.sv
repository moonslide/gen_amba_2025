// HDL top module for simulation
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
    axi4_if master_if[2](aclk, aresetn);
    axi4_if slave_if[2](aclk, aresetn);
    
    // Run test
    initial begin
        // Set interfaces in config_db (unrolled to avoid variable index issue)
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_0.*", "vif", master_if[0]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_1.*", "vif", master_if[1]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_0.*", "vif", slave_if[0]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_1.*", "vif", slave_if[1]);
        
        // Start UVM test
        run_test();
    end
    
endmodule
