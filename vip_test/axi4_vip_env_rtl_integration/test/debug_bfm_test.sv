//==============================================================================
// Debug BFM Test - Simple test to verify BFM connectivity
//==============================================================================

class debug_bfm_test extends axi4_base_test;
    
    `uvm_component_utils(debug_bfm_test)
    
    function new(string name = "debug_bfm_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axi4_master_write_seq write_seq;
        
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Starting debug BFM test", UVM_LOW)
        
        // Wait for reset
        #200ns;
        `uvm_info(get_type_name(), "After reset delay", UVM_LOW)
        
        // Configure and start a simple write sequence
        write_seq = axi4_master_write_seq::type_id::create("write_seq");
        write_seq.start_address = 32'h1000_0000;
        write_seq.burst_length = 1;
        write_seq.burst_size = 4;
        write_seq.num_trans = 1;
        
        `uvm_info(get_type_name(), "Starting write sequence on master 0", UVM_LOW)
        write_seq.start(env.master_agent[0].sequencer);
        
        `uvm_info(get_type_name(), "Write sequence completed", UVM_LOW)
        
        // Add some delay to see if response comes
        #500ns;
        
        `uvm_info(get_type_name(), "Debug BFM test completed", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
endclass : debug_bfm_test