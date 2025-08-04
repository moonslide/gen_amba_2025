//==============================================================================
// Demo Test - Shows Enhanced UVM_INFO Logging
//==============================================================================

class demo_logging_test extends axi4_base_test;
    
    `uvm_component_utils(demo_logging_test)
    
    function new(string name = "demo_logging_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_virtual_write_seq write_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "====================================", UVM_LOW)
        `uvm_info(get_type_name(), "Starting Enhanced Logging Demo Test", UVM_LOW)
        `uvm_info(get_type_name(), "====================================", UVM_LOW)
        
        `uvm_info(get_type_name(), "The following log messages will help you debug:", UVM_LOW)
        `uvm_info(get_type_name(), "1. Agent build/connect phases", UVM_LOW)
        `uvm_info(get_type_name(), "2. Driver transaction details", UVM_LOW)
        `uvm_info(get_type_name(), "3. Monitor activity status", UVM_LOW)
        `uvm_info(get_type_name(), "4. Sequence execution flow", UVM_LOW)
        
        // Run a simple write sequence
        write_seq = axi4_virtual_write_seq::type_id::create("write_seq");
        write_seq.start(env.virtual_seqr);
        
        #1000ns;
        
        `uvm_info(get_type_name(), "Test completed - check log for enhanced debug messages", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : demo_logging_test
