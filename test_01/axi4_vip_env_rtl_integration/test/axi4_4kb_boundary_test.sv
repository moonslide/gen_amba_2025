//==============================================================================
// AXI4 4KB Boundary Test
// Tests critical AXI4 requirement: No transaction can cross 4KB boundary
// Validates address calculation and boundary detection logic
//==============================================================================

class axi4_4kb_boundary_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_4kb_boundary_test)
    
    // Constructor
    function new(string name = "axi4_4kb_boundary_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        bit [63:0] test_addresses[];
        int burst_lengths[] = {1, 4, 8, 16, 32, 64, 128, 256};
        int burst_sizes[] = {1, 2, 4, 8, 16, 32, 64, 128};
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting 4KB boundary test", UVM_LOW)
        
        // Define test addresses near 4KB boundaries
        test_addresses = new[8];
        test_addresses[0] = 64'h0000_0FFF; // Just before 4KB boundary
        test_addresses[1] = 64'h0000_1000; // Exactly at 4KB boundary  
        test_addresses[2] = 64'h0000_1FFF; // Just before next 4KB boundary
        test_addresses[3] = 64'h0000_2000; // Next 4KB boundary
        test_addresses[4] = 64'h0001_0FFE; // Near boundary with unaligned address
        test_addresses[5] = 64'h0001_1000; // Aligned at boundary
        test_addresses[6] = 64'h00FF_FFFF; // Large address near boundary
        test_addresses[7] = 64'h0100_0000; // Large address at boundary
        
        // Test 1: Single transfers at boundaries (should always pass)
        `uvm_info(get_type_name(), "Test 1: Single transfers at 4KB boundaries", UVM_MEDIUM)
        foreach(test_addresses[i]) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("boundary_write_%0d", i));
            write_seq.start_address = test_addresses[i];
            write_seq.burst_length = 1;
            write_seq.burst_size = 8; // 64-bit
            write_seq.burst_type = axi4_globals_pkg::INCR;
            write_seq.start(env.master_agent[0].sequencer);
            #25ns;
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("boundary_read_%0d", i));
            read_seq.start_address = test_addresses[i];
            read_seq.burst_length = 1;
            read_seq.burst_size = 8;
            read_seq.burst_type = axi4_globals_pkg::INCR;
            read_seq.start(env.master_agent[1].sequencer);
            #25ns;
        end
        
        // Test 2: INCR bursts that approach but don't cross 4KB boundary
        `uvm_info(get_type_name(), "Test 2: INCR bursts approaching 4KB boundary", UVM_MEDIUM)
        foreach(burst_lengths[i]) begin
            foreach(burst_sizes[j]) begin
                bit [63:0] addr;
                int total_size;
                
                // Calculate address that allows burst to fit within 4KB
                total_size = burst_lengths[i] * burst_sizes[j];
                if (total_size <= 4096) begin
                    addr = 64'h1000 + (4096 - total_size); // Position so burst ends at boundary
                    
                    write_seq = axi4_master_write_seq::type_id::create($sformatf("approach_write_%0d_%0d", burst_lengths[i], burst_sizes[j]));
                    write_seq.start_address = addr;
                    write_seq.burst_length = burst_lengths[i];
                    write_seq.burst_size = burst_sizes[j];
                    write_seq.burst_type = axi4_globals_pkg::INCR;
                    write_seq.start(env.master_agent[i % 8].sequencer);
                    #30ns;
                end
            end
        end
        
        // Test 3: WRAP bursts at different boundaries
        `uvm_info(get_type_name(), "Test 3: WRAP bursts at 4KB boundaries", UVM_MEDIUM)
        int wrap_lengths[] = {2, 4, 8, 16};
        foreach(wrap_lengths[i]) begin
            foreach(burst_sizes[j]) begin
                bit [63:0] wrap_boundary;
                int wrap_size = wrap_lengths[i] * burst_sizes[j];
                
                // Test WRAP at different 4KB boundaries
                for (int k = 0; k < 4; k++) begin
                    wrap_boundary = (k * 4096) + (wrap_size * (k + 1)); // Align within 4KB page
                    if (wrap_boundary % wrap_size == 0) begin // Ensure proper alignment
                        write_seq = axi4_master_write_seq::type_id::create($sformatf("wrap_write_%0d_%0d_%0d", wrap_lengths[i], burst_sizes[j], k));
                        write_seq.start_address = wrap_boundary;
                        write_seq.burst_length = wrap_lengths[i];
                        write_seq.burst_size = burst_sizes[j];
                        write_seq.burst_type = axi4_globals_pkg::WRAP;
                        write_seq.start(env.master_agent[(i+j+k) % 8].sequencer);
                        #40ns;
                    end
                end
            end
        end
        
        // Test 4: FIXED bursts at boundaries (address doesn't change)
        `uvm_info(get_type_name(), "Test 4: FIXED bursts at 4KB boundaries", UVM_MEDIUM)
        foreach(test_addresses[i]) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("fixed_boundary_%0d", i));
            write_seq.start_address = test_addresses[i];
            write_seq.burst_length = 64; // Large burst but FIXED address
            write_seq.burst_size = 8;
            write_seq.burst_type = axi4_globals_pkg::FIXED;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #50ns;
        end
        
        // Test 5: Unaligned transfers near boundaries
        `uvm_info(get_type_name(), "Test 5: Unaligned transfers near 4KB boundaries", UVM_MEDIUM)
        bit [63:0] unaligned_addrs[] = {
            64'h0FFF, 64'h1001, 64'h1FFE, 64'h2003,
            64'h3FFA, 64'h4005, 64'h7FFD, 64'h8007
        };
        
        foreach(unaligned_addrs[i]) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("unaligned_write_%0d", i));
            write_seq.start_address = unaligned_addrs[i];
            write_seq.burst_length = 4;
            write_seq.burst_size = 4; // 32-bit transfers
            write_seq.burst_type = axi4_globals_pkg::INCR;
            write_seq.enable_unaligned = 1;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #35ns;
        end
        
        // Test 6: Maximum size transfers at boundaries
        `uvm_info(get_type_name(), "Test 6: Maximum size transfers at boundaries", UVM_MEDIUM)
        foreach(test_addresses[i]) begin
            if (i < 4) begin // Limit to first few addresses
                write_seq = axi4_master_write_seq::type_id::create($sformatf("max_size_write_%0d", i));
                write_seq.start_address = test_addresses[i] & 64'hFFFF_FF80; // Align to 128 bytes
                write_seq.burst_length = 32; // 32 * 128 = 4096 bytes exactly
                write_seq.burst_size = 128; // Maximum transfer size
                write_seq.burst_type = axi4_globals_pkg::INCR;
                write_seq.start(env.master_agent[i].sequencer);
                #100ns;
            end
        end
        
        `uvm_info(get_type_name(), "Completed 4KB boundary test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_4kb_boundary_test