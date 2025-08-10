//==============================================================================
// AXI4 Virtual Full Crossbar Sequence
// Generates transactions from all masters to all slaves
//==============================================================================

class axi4_virtual_full_crossbar_seq extends axi4_virtual_base_seq;
    `uvm_object_utils(axi4_virtual_full_crossbar_seq)
    
    function new(string name = "axi4_virtual_full_crossbar_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        axi4_master_full_crossbar_seq master_seq;
        
        `uvm_info(get_type_name(), "Starting Full Crossbar Virtual Sequence (Sequential Mode)", UVM_LOW)
        
        // Run masters sequentially to ensure completion and reduce simulation load
        for (int m = 0; m < 15; m++) begin
            `uvm_info(get_type_name(), $sformatf("Starting sequence on Master %0d", m), UVM_LOW)
            
            master_seq = axi4_master_full_crossbar_seq::type_id::create($sformatf("master_seq_%0d", m));
            master_seq.master_id = m;
            master_seq.start(p_sequencer.master_seqr[m]);
            
            `uvm_info(get_type_name(), $sformatf("Completed sequence on Master %0d (%0d/15)", m, m+1), UVM_LOW)
            
            // Small delay between masters
            #1000;
        end
        
        `uvm_info(get_type_name(), "All 15 master sequences completed", UVM_LOW)
        
        // Add delay to let all transactions complete
        #10000;
        
        `uvm_info(get_type_name(), "Full Crossbar Virtual Sequence Completed Successfully", UVM_LOW)
    endtask
    
endclass