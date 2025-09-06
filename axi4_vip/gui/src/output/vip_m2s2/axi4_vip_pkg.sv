// AXI4 VIP Package
// Auto-generated from bus configuration

package axi4_vip_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Parameters
    parameter ADDR_WIDTH = 32;
    parameter DATA_WIDTH = 64;
    parameter ID_WIDTH = 4;
    parameter USER_WIDTH = 4;
    parameter NUM_MASTERS = 2;
    parameter NUM_SLAVES = 2;
    
    // QoS configuration
    parameter QOS_ENABLE = 1;
    parameter DEFAULT_AWQOS = 1;
    parameter DEFAULT_ARQOS = 1;
    
    // Utility functions (none needed for basic package)
    
endpackage
