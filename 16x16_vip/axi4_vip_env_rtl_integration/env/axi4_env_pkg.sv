//==============================================================================
// axi4_env_pkg.sv
// Generated for 16x16 VIP RTL Integration
// Date: 2025-08-06 17:12:43
//==============================================================================

package axi4_env_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    import axi4_master_pkg::*;
    import axi4_slave_pkg::*;
    import axi4_virtual_seqr_pkg::*;
    
    // Environment configuration
    class axi4_env_config extends uvm_object;
        `uvm_object_utils(axi4_env_config)
        
        int no_of_masters = 16;
        int no_of_slaves = 16;
        
        function new(string name = "axi4_env_config");
            super.new(name);
        endfunction
    endclass
    
    // Environment
    class axi4_env extends uvm_env;
        `uvm_component_utils(axi4_env)
        
        axi4_env_config env_cfg;
        axi4_virtual_sequencer virtual_seqr;
        
        function new(string name = "axi4_env", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            
            if (!uvm_config_db#(axi4_env_config)::get(this, "", "env_cfg", env_cfg)) begin
                `uvm_fatal(get_type_name(), "Unable to get env_cfg from config_db")
            end
            
            virtual_seqr = axi4_virtual_sequencer::type_id::create("virtual_seqr", this);
        endfunction
    endclass
    
endpackage : axi4_env_pkg
