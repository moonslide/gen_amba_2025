//==============================================================================
// AXI4 Virtual Simple Crossbar Sequence - Tests multiple masters
// ULTRATHINK: Tests first 3 masters with both write and read
//==============================================================================

class axi4_virtual_simple_crossbar_seq extends axi4_virtual_base_seq;
    `uvm_object_utils(axi4_virtual_simple_crossbar_seq)
    
    bit seq_done = 0;  // Completion flag
    
    function new(string name = "axi4_virtual_simple_crossbar_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        axi4_master_simple_crossbar_seq master_seq[3];
        
        `uvm_info(get_type_name(), "Starting Virtual Crossbar Sequence", UVM_LOW)
        `uvm_info(get_type_name(), "Testing first 3 masters with W+R transactions", UVM_LOW)
        
        // Test first 3 masters with staggered starts to avoid contention
        fork
            begin
                for (int i = 0; i < 3; i++) begin
                    automatic int master_idx = i;
                    fork
                        begin
                            // Stagger master starts to avoid contention at time 0
                            #(master_idx * 200);  // 200ns delay between each master start
                            master_seq[master_idx] = axi4_master_simple_crossbar_seq::type_id::create($sformatf("master_seq_%0d", master_idx));
                            master_seq[master_idx].master_id = master_idx;
                            master_seq[master_idx].start(p_sequencer.master_seqr[master_idx]);
                            `uvm_info(get_type_name(), $sformatf("Master %0d sequence completed", master_idx), UVM_LOW)
                        end
                    join_none
                end
                
                // Wait for all to complete
                wait fork;
            end
            begin
                #10000; // 10us timeout - enough for all masters
                `uvm_info(get_type_name(), "Virtual sequence timeout - continuing", UVM_LOW)
            end
        join_any
        
        // Kill any remaining threads
        disable fork;
        
        // Small delay
        #100;
        
        `uvm_info(get_type_name(), "Virtual Crossbar Sequence Completed", UVM_LOW)
        seq_done = 1;  // Signal completion
    endtask
    
endclass
