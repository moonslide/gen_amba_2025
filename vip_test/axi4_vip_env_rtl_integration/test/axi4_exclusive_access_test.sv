//==============================================================================
// AXI4 Exclusive Access Test
// Tests exclusive read/write pairs and atomic operations
// Validates EXOKAY/OKAY response handling per AXI4 specification
//==============================================================================

class axi4_exclusive_access_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_exclusive_access_test)
    
    // Constructor
    function new(string name = "axi4_exclusive_access_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_master_read_seq read_seq;
        axi4_master_write_seq write_seq;
        bit [63:0] exclusive_addresses[];
        begin

        int exclusive_sizes[] = '{1, 2, 4, 8, 16, 32, 64, 128}; // Up to 128 bytes
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting exclusive access test", UVM_LOW)
        
        // Setup test addresses - must be aligned to transfer size
        exclusive_addresses = new[8];
        exclusive_addresses[0] = 64'h0000_1000; // 4KB aligned
        exclusive_addresses[1] = 64'h0000_2000; // 4KB aligned
        exclusive_addresses[2] = 64'h0000_4000; // 4KB aligned
        exclusive_addresses[3] = 64'h0000_8000; // 4KB aligned
        exclusive_addresses[4] = 64'h0001_0000; // 64KB aligned
        exclusive_addresses[5] = 64'h0002_0000; // 128KB aligned
        exclusive_addresses[6] = 64'h0004_0000; // 256KB aligned
        exclusive_addresses[7] = 64'h0008_0000; // 512KB aligned
        
        // Test 1: Basic exclusive read-write pairs (should get EXOKAY)
        `uvm_info(get_type_name(), "Test 1: Basic exclusive read-write pairs", UVM_MEDIUM)
        foreach(exclusive_addresses[i]) begin
            foreach(exclusive_sizes[j]) begin
                if (exclusive_sizes[j] <= 128) begin // Max 128 bytes for exclusive
                    bit [63:0] aligned_addr = exclusive_addresses[i] & ~(exclusive_sizes[j] - 1);
                    
                    // Exclusive read
                    read_seq = axi4_master_read_seq::type_id::create($sformatf("excl_read_%0d_%0d", i, j));
                    read_seq.start_address = aligned_addr;
                    read_seq.burst_length = 1;
                    read_seq.burst_size = exclusive_sizes[j];
                    read_seq.burst_type = axi4_globals_pkg::INCR;
                    read_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
                    read_seq.axi_id = i; // Use different IDs
                    read_seq.start(env.master_agent[i % 8].sequencer);
                    #50ns;
                    
                    // Matching exclusive write (should get EXOKAY)
                    write_seq = axi4_master_write_seq::type_id::create($sformatf("excl_write_%0d_%0d", i, j));
                    write_seq.start_address = aligned_addr;
                    write_seq.burst_length = 1;
                    write_seq.burst_size = exclusive_sizes[j];
                    write_seq.burst_type = axi4_globals_pkg::INCR;
                    write_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
                    write_seq.axi_id = i; // Same ID as read
                    write_seq.expect_response = axi4_globals_pkg::EXOKAY;
                    write_seq.start(env.master_agent[i % 8].sequencer);
                    #50ns;
                end
            end
        end


        end
        
        // Test 2: Exclusive access failures (intervening writes)
        `uvm_info(get_type_name(), "Test 2: Exclusive access failures", UVM_MEDIUM)
        for (int i = 0; i < 4; i++) begin
            bit [63:0] addr = exclusive_addresses[i];
            
            // Exclusive read from master 0
            read_seq = axi4_master_read_seq::type_id::create($sformatf("fail_excl_read_%0d", i));
            read_seq.start_address = addr;
            read_seq.burst_length = 1;
            read_seq.burst_size = 8;
            read_seq.burst_type = axi4_globals_pkg::INCR;
            read_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
            read_seq.axi_id = 0;
            read_seq.start(env.master_agent[0].sequencer);
            #30ns;
            
            // Intervening normal write from master 1 (clears exclusive state)
            write_seq = axi4_master_write_seq::type_id::create($sformatf("intervening_write_%0d", i));
            write_seq.start_address = addr;
            write_seq.burst_length = 1;
            write_seq.burst_size = 8;
            write_seq.burst_type = axi4_globals_pkg::INCR;
            write_seq.lock_type = axi4_globals_pkg::NORMAL;
            write_seq.axi_id = 1;
            write_seq.start(env.master_agent[1].sequencer);
            #30ns;
            
            // Exclusive write from master 0 (should get OKAY, not EXOKAY)
            write_seq = axi4_master_write_seq::type_id::create($sformatf("fail_excl_write_%0d", i));
            write_seq.start_address = addr;
            write_seq.burst_length = 1;
            write_seq.burst_size = 8;
            write_seq.burst_type = axi4_globals_pkg::INCR;
            write_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
            write_seq.axi_id = 0;
            write_seq.expect_response = axi4_globals_pkg::OKAY; // Failure case
            write_seq.start(env.master_agent[0].sequencer);
            #30ns;
        end
        
        // Test 3: Multiple masters exclusive access contention
        `uvm_info(get_type_name(), "Test 3: Multi-master exclusive contention", UVM_MEDIUM)
        fork
            // Master 0 exclusive sequence
            begin
                read_seq = axi4_master_read_seq::type_id::create("contention_read_0");
                read_seq.start_address = 64'h0001_0000;
                read_seq.burst_length = 1;
                read_seq.burst_size = 8;
                read_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
                read_seq.axi_id = 10;
                read_seq.start(env.master_agent[0].sequencer);
                #40ns;
                
                write_seq = axi4_master_write_seq::type_id::create("contention_write_0");
                write_seq.start_address = 64'h0001_0000;
                write_seq.burst_length = 1;
                write_seq.burst_size = 8;
                write_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
                write_seq.axi_id = 10;
                write_seq.start(env.master_agent[0].sequencer);
            end
            // Master 1 exclusive sequence (different address)
            begin
                #10ns; // Slight delay
                read_seq = axi4_master_read_seq::type_id::create("contention_read_1");
                read_seq.start_address = 64'h0001_0008;
                read_seq.burst_length = 1;
                read_seq.burst_size = 8;
                read_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
                read_seq.axi_id = 11;
                read_seq.start(env.master_agent[1].sequencer);
                #40ns;
                
                write_seq = axi4_master_write_seq::type_id::create("contention_write_1");
                write_seq.start_address = 64'h0001_0008;
                write_seq.burst_length = 1;
                write_seq.burst_size = 8;
                write_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
                write_seq.axi_id = 11;
                write_seq.start(env.master_agent[1].sequencer);
            end
            // Master 2 competing for same address as Master 0
            begin
                #20ns; // Delay to interfere
                read_seq = axi4_master_read_seq::type_id::create("contention_read_2");
                read_seq.start_address = 64'h0001_0000; // Same as Master 0
                read_seq.burst_length = 1;
                read_seq.burst_size = 8;
                read_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
                read_seq.axi_id = 12;
                read_seq.start(env.master_agent[1].sequencer);
                #30ns;
                
                write_seq = axi4_master_write_seq::type_id::create("contention_write_2");
                write_seq.start_address = 64'h0001_0000;
                write_seq.burst_length = 1;
                write_seq.burst_size = 8;
                write_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
                write_seq.axi_id = 12;
                write_seq.start(env.master_agent[1].sequencer);
            end
        join
        
        // Test 4: Exclusive access with different AXI IDs from same master
        `uvm_info(get_type_name(), "Test 4: Different AXI IDs from same master", UVM_MEDIUM)
        for (int id = 0; id < 16; id++) begin
            bit [63:0] addr = 64'h0002_0000 + (id * 64); // Separate addresses
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("multi_id_read_%0d", id));
            read_seq.start_address = addr;
            read_seq.burst_length = 1;
            read_seq.burst_size = 8;
            read_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
            read_seq.axi_id = id;
            read_seq.start(env.master_agent[0].sequencer);
            #20ns;
            
            write_seq = axi4_master_write_seq::type_id::create($sformatf("multi_id_write_%0d", id));
            write_seq.start_address = addr;
            write_seq.burst_length = 1;
            write_seq.burst_size = 8;
            write_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
            write_seq.axi_id = id;
            write_seq.expect_response = axi4_globals_pkg::EXOKAY;
            write_seq.start(env.master_agent[0].sequencer);
            #20ns;
        end
        
        // Test 5: Exclusive access size and alignment validation
        `uvm_info(get_type_name(), "Test 5: Size and alignment validation", UVM_MEDIUM)
        begin

        int power_of_2_sizes[] = '{1, 2, 4, 8, 16, 32, 64, 128};
        foreach(power_of_2_sizes[i]) begin
            bit [63:0] addr = 64'h0003_0000;
            addr = addr & ~(power_of_2_sizes[i] - 1); // Ensure proper alignment
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("align_excl_read_%0d", i));
            read_seq.start_address = addr;
            read_seq.burst_length = 1;
            read_seq.burst_size = power_of_2_sizes[i];
            read_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
            read_seq.axi_id = i;
            read_seq.start(env.master_agent[i % 8].sequencer);
            #25ns;
            
            write_seq = axi4_master_write_seq::type_id::create($sformatf("align_excl_write_%0d", i));
            write_seq.start_address = addr;
            write_seq.burst_length = 1;
            write_seq.burst_size = power_of_2_sizes[i];
            write_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
            write_seq.axi_id = i;
            write_seq.expect_response = axi4_globals_pkg::EXOKAY;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #25ns;
        end


        end
        
        `uvm_info(get_type_name(), "Completed exclusive access test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_exclusive_access_test