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
    
    // Utility functions (none needed for basic package)
    
endpackage
