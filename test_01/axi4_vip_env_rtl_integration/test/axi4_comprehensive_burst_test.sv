//==============================================================================
// AXI4 Comprehensive Burst Test
// Tests all burst types (FIXED, INCR, WRAP) with various lengths and sizes
// Covers AXI4 burst requirements from IHI0022D specification
//==============================================================================

class axi4_comprehensive_burst_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_comprehensive_burst_test)
    
    // Constructor
    function new(string name = "axi4_comprehensive_burst_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_master_burst_seq burst_seq;
        int burst_lengths[] = {1, 2, 4, 8, 16, 32, 64, 128, 256}; // AXI4 supports up to 256
        int wrap_lengths[] = {2, 4, 8, 16}; // Valid WRAP lengths only
        int burst_sizes[] = {1, 2, 4, 8, 16, 32, 64, 128}; // 1 to 128 bytes
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting comprehensive burst test", UVM_LOW)
        
        // Test FIXED bursts with different lengths and sizes
        `uvm_info(get_type_name(), "Testing FIXED burst type", UVM_MEDIUM)
        foreach(burst_lengths[i]) begin
            foreach(burst_sizes[j]) begin
                if (burst_sizes[j] <= 128) begin // Max 128 bytes per transfer
                    burst_seq = axi4_master_burst_seq::type_id::create($sformatf("fixed_burst_%0d_%0d", burst_lengths[i], burst_sizes[j]));
                    burst_seq.burst_type = axi4_globals_pkg::FIXED;
                    burst_seq.burst_length = burst_lengths[i];
                    burst_seq.burst_size = burst_sizes[j];
                    burst_seq.start(env.master_agent[0].sequencer);
                    #50ns;
                end
            end
        end
        
        // Test INCR bursts with different lengths (AXI4 supports up to 256)
        `uvm_info(get_type_name(), "Testing INCR burst type", UVM_MEDIUM)
        foreach(burst_lengths[i]) begin
            burst_seq = axi4_master_burst_seq::type_id::create($sformatf("incr_burst_%0d", burst_lengths[i]));
            burst_seq.burst_type = axi4_globals_pkg::INCR;
            burst_seq.burst_length = burst_lengths[i];
            burst_seq.burst_size = 8; // 64-bit transfers
            burst_seq.start(env.master_agent[1].sequencer);
            #50ns;
        end
        
        // Test WRAP bursts (only valid lengths: 2, 4, 8, 16)
        `uvm_info(get_type_name(), "Testing WRAP burst type", UVM_MEDIUM)
        foreach(wrap_lengths[i]) begin
            foreach(burst_sizes[j]) begin
                if (burst_sizes[j] <= 128) begin
                    burst_seq = axi4_master_burst_seq::type_id::create($sformatf("wrap_burst_%0d_%0d", wrap_lengths[i], burst_sizes[j]));
                    burst_seq.burst_type = axi4_globals_pkg::WRAP;
                    burst_seq.burst_length = wrap_lengths[i];
                    burst_seq.burst_size = burst_sizes[j];
                    // Ensure address is aligned for WRAP
                    burst_seq.align_address_for_wrap = 1;
                    burst_seq.start(env.master_agent[2].sequencer);
                    #50ns;
                end
            end
        end
        
        // Test concurrent bursts from multiple masters
        `uvm_info(get_type_name(), "Testing concurrent burst operations", UVM_MEDIUM)
        fork
            begin
                burst_seq = axi4_master_burst_seq::type_id::create("concurrent_burst_0");
                burst_seq.burst_type = axi4_globals_pkg::INCR;
                burst_seq.burst_length = 64;
                burst_seq.start(env.master_agent[0].sequencer);
            end
            begin
                burst_seq = axi4_master_burst_seq::type_id::create("concurrent_burst_1");
                burst_seq.burst_type = axi4_globals_pkg::WRAP;
                burst_seq.burst_length = 8;
                burst_seq.align_address_for_wrap = 1;
                burst_seq.start(env.master_agent[1].sequencer);
            end
            begin
                burst_seq = axi4_master_burst_seq::type_id::create("concurrent_burst_2");
                burst_seq.burst_type = axi4_globals_pkg::FIXED;
                burst_seq.burst_length = 32;
                burst_seq.start(env.master_agent[2].sequencer);
            end
        join
        
        `uvm_info(get_type_name(), "Completed comprehensive burst test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_comprehensive_burst_test