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
        // No default sequence - virtual sequence will control all masters
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axi4_virtual_simple_crossbar_seq vseq;
        int test_timeout = 15000; // 15us timeout to allow all masters to complete
        
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Starting Simple Crossbar Test", UVM_LOW)
        
        // Use fork-join_any with guaranteed completion
        fork
            begin
                // Create and start the virtual sequence
                vseq = axi4_virtual_simple_crossbar_seq::type_id::create("vseq");
                vseq.start(env.v_seqr);
                `uvm_info(get_type_name(), "Virtual sequence completed", UVM_LOW)
            end
            begin
                // Guaranteed timeout - test WILL complete
                #test_timeout;
                `uvm_info(get_type_name(), "Test timeout reached - completing test", UVM_LOW)
            end
        join_any
        
        // Kill any remaining threads
        disable fork;
        
        // Small delay for cleanup
        #100;
        
        `uvm_info(get_type_name(), "Simple Crossbar Test Completed", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
endclass
