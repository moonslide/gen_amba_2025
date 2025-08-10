//==============================================================================
// AXI4 Simple Crossbar Test - Quick test to verify crossbar functionality
//==============================================================================

class axi4_simple_crossbar_test extends axi4_base_test;
    `uvm_component_utils(axi4_simple_crossbar_test)
    
    function new(string name = "axi4_simple_crossbar_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axi4_virtual_simple_crossbar_seq vseq;
        
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Starting Simple Crossbar Test", UVM_LOW)
        
        // Create and start the virtual sequence
        vseq = axi4_virtual_simple_crossbar_seq::type_id::create("vseq");
        vseq.start(env.v_seqr);
        
        // Wait for completion
        #5000;
        
        `uvm_info(get_type_name(), "Simple Crossbar Test Completed", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
endclass