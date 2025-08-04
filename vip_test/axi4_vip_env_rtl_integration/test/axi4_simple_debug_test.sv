//==============================================================================
// Simple Debug Test - Minimal test to check BFM connectivity
//==============================================================================

class axi4_simple_debug_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_simple_debug_test)
    
    function new(string name = "axi4_simple_debug_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Starting simple debug test", UVM_LOW)
        
        // Just wait and observe
        #1us;
        
        `uvm_info(get_type_name(), "Simple debug test completed", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
endclass : axi4_simple_debug_test