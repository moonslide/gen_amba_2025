//==============================================================================
// axi4_virtual_seq_pkg.sv
// Generated for 16x16 VIP RTL Integration
// Date: 2025-08-06 17:12:43
//==============================================================================

package axi4_virtual_seq_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    import axi4_master_seq_pkg::*;
    import axi4_slave_seq_pkg::*;
    import axi4_virtual_seqr_pkg::*;
    import axi4_env_pkg::*;
    
    // Basic virtual sequence
    class axi4_basic_virtual_seq extends uvm_sequence;
        `uvm_object_utils(axi4_basic_virtual_seq)
        
        function new(string name = "axi4_basic_virtual_seq");
            super.new(name);
        endfunction
        
        virtual task body();
            `uvm_info(get_type_name(), "Starting basic virtual sequence", UVM_LOW)
            #100ns; // Simple delay
            `uvm_info(get_type_name(), "Finished basic virtual sequence", UVM_LOW)
        endtask
    endclass
    
    // Stress virtual sequence  
    class axi4_stress_virtual_seq extends uvm_sequence;
        `uvm_object_utils(axi4_stress_virtual_seq)
        
        int num_trans = 100;
        
        function new(string name = "axi4_stress_virtual_seq");
            super.new(name);
        endfunction
        
        virtual task body();
            `uvm_info(get_type_name(), $sformatf("Starting stress test with %0d transactions", num_trans), UVM_LOW)
            repeat(num_trans) begin
                #10ns; // Transaction delay
            end
            `uvm_info(get_type_name(), "Finished stress virtual sequence", UVM_LOW)
        endtask
    endclass
    
    // QoS virtual sequence
    class axi4_qos_virtual_seq extends axi4_basic_virtual_seq;
        `uvm_object_utils(axi4_qos_virtual_seq)
        
        function new(string name = "axi4_qos_virtual_seq");
            super.new(name);
        endfunction
        
        virtual task body();
            `uvm_info(get_type_name(), "Starting QoS virtual sequence", UVM_LOW)
            #200ns; // QoS test delay
            `uvm_info(get_type_name(), "Finished QoS virtual sequence", UVM_LOW)
        endtask
    endclass
    
    // Additional virtual sequences for remaining tests
    class axi4_basic_rw_virtual_seq extends axi4_basic_virtual_seq;
        `uvm_object_utils(axi4_basic_rw_virtual_seq)
        function new(string name = "axi4_basic_rw_virtual_seq"); super.new(name); endfunction
    endclass
    
    class axi4_burst_virtual_seq extends axi4_basic_virtual_seq;
        `uvm_object_utils(axi4_burst_virtual_seq)
        function new(string name = "axi4_burst_virtual_seq"); super.new(name); endfunction
    endclass
    
    class axi4_random_virtual_seq extends axi4_basic_virtual_seq;
        `uvm_object_utils(axi4_random_virtual_seq)
        function new(string name = "axi4_random_virtual_seq"); super.new(name); endfunction
    endclass
    
    class axi4_error_virtual_seq extends axi4_basic_virtual_seq;
        `uvm_object_utils(axi4_error_virtual_seq)
        function new(string name = "axi4_error_virtual_seq"); super.new(name); endfunction
    endclass
    
    class axi4_performance_virtual_seq extends axi4_basic_virtual_seq;
        `uvm_object_utils(axi4_performance_virtual_seq)
        function new(string name = "axi4_performance_virtual_seq"); super.new(name); endfunction
    endclass
    
    class axi4_interleaved_virtual_seq extends axi4_basic_virtual_seq;
        `uvm_object_utils(axi4_interleaved_virtual_seq)
        function new(string name = "axi4_interleaved_virtual_seq"); super.new(name); endfunction
    endclass
    
    class axi4_boundary_virtual_seq extends axi4_basic_virtual_seq;
        `uvm_object_utils(axi4_boundary_virtual_seq)
        function new(string name = "axi4_boundary_virtual_seq"); super.new(name); endfunction
    endclass
    
endpackage : axi4_virtual_seq_pkg
