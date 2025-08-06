//==============================================================================
// axi4_virtual_seqr_pkg.sv
// Generated for 16x16 VIP RTL Integration
// Date: 2025-08-06 17:12:43
//==============================================================================

package axi4_virtual_seqr_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    
    // Virtual sequencer
    class axi4_virtual_sequencer extends uvm_sequencer;
        `uvm_component_utils(axi4_virtual_sequencer)
        
        function new(string name = "axi4_virtual_sequencer", uvm_component parent = null);
            super.new(name, parent);
        endfunction
    endclass
    
endpackage : axi4_virtual_seqr_pkg
