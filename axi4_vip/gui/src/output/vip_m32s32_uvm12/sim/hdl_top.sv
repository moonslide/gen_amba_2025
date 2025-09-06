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
    axi4_if master_if[32](aclk, aresetn);
    axi4_if slave_if[32](aclk, aresetn);
    
    // Run test
    initial begin
        // Set interfaces in config_db (unrolled to avoid variable index issue)
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[0].*", "vif", master_if[0]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[1].*", "vif", master_if[1]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[2].*", "vif", master_if[2]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[3].*", "vif", master_if[3]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[4].*", "vif", master_if[4]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[5].*", "vif", master_if[5]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[6].*", "vif", master_if[6]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[7].*", "vif", master_if[7]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[8].*", "vif", master_if[8]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[9].*", "vif", master_if[9]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[10].*", "vif", master_if[10]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[11].*", "vif", master_if[11]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[12].*", "vif", master_if[12]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[13].*", "vif", master_if[13]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[14].*", "vif", master_if[14]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[15].*", "vif", master_if[15]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[16].*", "vif", master_if[16]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[17].*", "vif", master_if[17]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[18].*", "vif", master_if[18]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[19].*", "vif", master_if[19]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[20].*", "vif", master_if[20]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[21].*", "vif", master_if[21]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[22].*", "vif", master_if[22]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[23].*", "vif", master_if[23]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[24].*", "vif", master_if[24]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[25].*", "vif", master_if[25]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[26].*", "vif", master_if[26]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[27].*", "vif", master_if[27]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[28].*", "vif", master_if[28]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[29].*", "vif", master_if[29]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[30].*", "vif", master_if[30]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agents[31].*", "vif", master_if[31]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[0].*", "vif", slave_if[0]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[1].*", "vif", slave_if[1]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[2].*", "vif", slave_if[2]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[3].*", "vif", slave_if[3]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[4].*", "vif", slave_if[4]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[5].*", "vif", slave_if[5]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[6].*", "vif", slave_if[6]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[7].*", "vif", slave_if[7]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[8].*", "vif", slave_if[8]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[9].*", "vif", slave_if[9]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[10].*", "vif", slave_if[10]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[11].*", "vif", slave_if[11]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[12].*", "vif", slave_if[12]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[13].*", "vif", slave_if[13]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[14].*", "vif", slave_if[14]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[15].*", "vif", slave_if[15]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[16].*", "vif", slave_if[16]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[17].*", "vif", slave_if[17]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[18].*", "vif", slave_if[18]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[19].*", "vif", slave_if[19]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[20].*", "vif", slave_if[20]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[21].*", "vif", slave_if[21]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[22].*", "vif", slave_if[22]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[23].*", "vif", slave_if[23]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[24].*", "vif", slave_if[24]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[25].*", "vif", slave_if[25]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[26].*", "vif", slave_if[26]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[27].*", "vif", slave_if[27]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[28].*", "vif", slave_if[28]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[29].*", "vif", slave_if[29]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[30].*", "vif", slave_if[30]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agents[31].*", "vif", slave_if[31]);
        
        // Start UVM test
        run_test();
    end
    
endmodule
