//==============================================================================
// axi4_slave_seq_pkg.sv
// Generated for 16x16 VIP RTL Integration
// Date: 2025-08-06 22:49:41
//==============================================================================

package axi4_slave_seq_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    import axi4_slave_pkg::*;
    
    // Include all sequence files
    `include "axi4_slave_base_seq.sv"
    `include "axi4_slave_mem_seq.sv"
    `include "axi4_slave_simple_resp_seq.sv"
    
endpackage : axi4_slave_seq_pkg
