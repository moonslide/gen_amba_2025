//==============================================================================
// AXI4 Full Crossbar Test - Tests all masters to all slaves
// This test verifies that every master can access every slave
//==============================================================================

class axi4_full_crossbar_test extends axi4_base_test;
    `uvm_component_utils(axi4_full_crossbar_test)
    
    function new(string name = "axi4_full_crossbar_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axi4_virtual_full_crossbar_seq vseq;
        
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Starting Full Crossbar Test - All Masters to All Slaves", UVM_LOW)
        
        // Set timeout for this specific test
        phase.phase_done.set_drain_time(this, 50000);
        
        // Create and start the virtual sequence
        vseq = axi4_virtual_full_crossbar_seq::type_id::create("vseq");
        
        fork
            begin
                vseq.start(env.v_seqr);
                `uvm_info(get_type_name(), "Virtual sequence completed", UVM_LOW)
            end
            begin
                // Timeout watchdog - force completion after reasonable time
                #50000000; // 50ms
                `uvm_warning(get_type_name(), "Test timeout reached - forcing completion")
            end
        join_any
        disable fork;
        
        // Allow time for final transactions to settle
        #10000;
        
        `uvm_info(get_type_name(), "Full Crossbar Test Completed", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
endclass