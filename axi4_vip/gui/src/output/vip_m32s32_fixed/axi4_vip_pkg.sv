// AXI4 VIP Package
// Auto-generated from bus configuration

package axi4_vip_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Parameters
    parameter ADDR_WIDTH = 48;
    parameter DATA_WIDTH = 256;
    parameter ID_WIDTH = 8;
    parameter USER_WIDTH = 8;
    parameter NUM_MASTERS = 32;
    parameter NUM_SLAVES = 32;
    
    // QoS configuration
    parameter QOS_ENABLE = 1;
    parameter DEFAULT_AWQOS = 2;
    parameter DEFAULT_ARQOS = 2;
    
    // Include all VIP components
    `include "axi4_transaction.sv"
    `include "axi4_master_driver.sv"
    `include "axi4_master_monitor.sv"
    `include "axi4_master_agent.sv"
    `include "axi4_slave_driver.sv"
    `include "axi4_slave_monitor.sv"
    `include "axi4_slave_agent.sv"
    `include "axi4_env.sv"
    
endpackage
