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
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_0.*", "vif", master_if[0]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_1.*", "vif", master_if[1]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_2.*", "vif", master_if[2]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_3.*", "vif", master_if[3]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_4.*", "vif", master_if[4]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_5.*", "vif", master_if[5]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_6.*", "vif", master_if[6]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_7.*", "vif", master_if[7]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_8.*", "vif", master_if[8]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_9.*", "vif", master_if[9]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_10.*", "vif", master_if[10]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_11.*", "vif", master_if[11]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_12.*", "vif", master_if[12]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_13.*", "vif", master_if[13]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_14.*", "vif", master_if[14]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_15.*", "vif", master_if[15]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_16.*", "vif", master_if[16]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_17.*", "vif", master_if[17]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_18.*", "vif", master_if[18]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_19.*", "vif", master_if[19]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_20.*", "vif", master_if[20]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_21.*", "vif", master_if[21]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_22.*", "vif", master_if[22]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_23.*", "vif", master_if[23]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_24.*", "vif", master_if[24]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_25.*", "vif", master_if[25]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_26.*", "vif", master_if[26]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_27.*", "vif", master_if[27]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_28.*", "vif", master_if[28]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_29.*", "vif", master_if[29]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_30.*", "vif", master_if[30]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.master_agent_31.*", "vif", master_if[31]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_0.*", "vif", slave_if[0]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_1.*", "vif", slave_if[1]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_2.*", "vif", slave_if[2]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_3.*", "vif", slave_if[3]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_4.*", "vif", slave_if[4]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_5.*", "vif", slave_if[5]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_6.*", "vif", slave_if[6]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_7.*", "vif", slave_if[7]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_8.*", "vif", slave_if[8]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_9.*", "vif", slave_if[9]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_10.*", "vif", slave_if[10]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_11.*", "vif", slave_if[11]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_12.*", "vif", slave_if[12]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_13.*", "vif", slave_if[13]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_14.*", "vif", slave_if[14]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_15.*", "vif", slave_if[15]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_16.*", "vif", slave_if[16]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_17.*", "vif", slave_if[17]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_18.*", "vif", slave_if[18]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_19.*", "vif", slave_if[19]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_20.*", "vif", slave_if[20]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_21.*", "vif", slave_if[21]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_22.*", "vif", slave_if[22]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_23.*", "vif", slave_if[23]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_24.*", "vif", slave_if[24]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_25.*", "vif", slave_if[25]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_26.*", "vif", slave_if[26]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_27.*", "vif", slave_if[27]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_28.*", "vif", slave_if[28]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_29.*", "vif", slave_if[29]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_30.*", "vif", slave_if[30]);
        uvm_config_db#(virtual axi4_if)::set(null, "uvm_test_top.env.slave_agent_31.*", "vif", slave_if[31]);
        
        // Start UVM test
        run_test();
    end
    
endmodule
