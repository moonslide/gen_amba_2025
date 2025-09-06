// AXI4 VIP Package - UVM-1.2 Compatible
// Auto-generated from bus configuration

package axi4_vip_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // UVM-1.2 version check
    `ifndef UVM_VERSION_1_2
        `ifdef UVM_VERSION_1_1
            $display("Warning: Using UVM-1.1 library. UVM-1.2 is recommended for this VIP.");
        `else
            $display("Warning: UVM version not detected. This VIP is optimized for UVM-1.2.");
        `endif
    `endif
    
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
