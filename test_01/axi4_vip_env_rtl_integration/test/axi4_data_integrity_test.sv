//==============================================================================
// AXI4 Data Integrity Test
// Comprehensive data validation including unaligned transfers, WSTRB patterns,
// and end-to-end data integrity checking
//==============================================================================

class axi4_data_integrity_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_data_integrity_test)
    
    // Constructor
    function new(string name = "axi4_data_integrity_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase - enable data checking
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Enable comprehensive data integrity checking
        env_cfg.enable_data_integrity_check = 1;
        env_cfg.enable_memory_model = 1;
        env_cfg.enable_wstrb_checking = 1;
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting data integrity test", UVM_LOW)
        
        // Test 1: Basic write-read data integrity
        `uvm_info(get_type_name(), "Test 1: Basic write-read integrity", UVM_MEDIUM)
        test_basic_data_integrity();
        
        // Test 2: Unaligned transfer testing
        `uvm_info(get_type_name(), "Test 2: Unaligned transfer testing", UVM_MEDIUM)
        test_unaligned_transfers();
        
        // Test 3: WSTRB pattern validation
        `uvm_info(get_type_name(), "Test 3: WSTRB pattern validation", UVM_MEDIUM)
        test_wstrb_patterns();
        
        // Test 4: Data width variations
        `uvm_info(get_type_name(), "Test 4: Data width variations", UVM_MEDIUM)
        test_data_width_variations();
        
        // Test 5: Burst data consistency
        `uvm_info(get_type_name(), "Test 5: Burst data consistency", UVM_MEDIUM)
        test_burst_data_consistency();
        
        // Test 6: Overlapping address testing
        `uvm_info(get_type_name(), "Test 6: Overlapping address testing", UVM_MEDIUM)
        test_overlapping_addresses();
        
        // Test 7: Data pattern stress test
        `uvm_info(get_type_name(), "Test 7: Data pattern stress test", UVM_MEDIUM)
        test_data_pattern_stress();
        
        // Test 8: Multi-master data coherency
        `uvm_info(get_type_name(), "Test 8: Multi-master data coherency", UVM_MEDIUM)
        test_multi_master_coherency();
        
        `uvm_info(get_type_name(), "Completed data integrity test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    // Test basic write-read data integrity
    task test_basic_data_integrity();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test different data patterns
        bit [127:0] test_patterns[] = {
            128'h00000000_00000000_00000000_00000000, // All zeros
            128'hFFFFFFFF_FFFFFFFF_FFFFFFFF_FFFFFFFF, // All ones
            128'hAAAAAAAA_AAAAAAAA_AAAAAAAA_AAAAAAAA, // Alternating 1010
            128'h55555555_55555555_55555555_55555555, // Alternating 0101
            128'h12345678_9ABCDEF0_FEDCBA09_87654321, // Sequential pattern
            128'hDEADBEEF_CAFEBABE_FEEDFACE_BAADF00D, // Known patterns
            128'h01234567_89ABCDEF_FEDCBA98_76543210, // Incremental
            128'hF0F0F0F0_0F0F0F0F_F0F0F0F0_0F0F0F0F  // Nibble alternating
        };
        
        foreach(test_patterns[i]) begin
            bit [63:0] test_addr = 64'h0001_0000 + (i * 256);
            
            // Write test pattern
            write_seq = axi4_master_write_seq::type_id::create($sformatf("pattern_write_%0d", i));
            write_seq.start_address = test_addr;
            write_seq.burst_length = 1;
            write_seq.burst_size = 16; // 128-bit transfer
            write_seq.test_data_pattern = test_patterns[i];
            write_seq.enable_data_check = 1;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #50ns;
            
            // Read back and verify
            read_seq = axi4_master_read_seq::type_id::create($sformatf("pattern_read_%0d", i));
            read_seq.start_address = test_addr;
            read_seq.burst_length = 1;
            read_seq.burst_size = 16;
            read_seq.expected_data_pattern = test_patterns[i];
            read_seq.enable_data_check = 1;
            read_seq.start(env.master_agent[i % 8].sequencer);
            #50ns;
        end
        
        // Test incremental data pattern
        for (int addr_offset = 0; addr_offset < 64; addr_offset++) begin
            bit [63:0] addr = 64'h0001_2000 + (addr_offset * 64);
            bit [63:0] expected_data = addr ^ 64'hA5A5A5A5_5A5A5A5A;
            
            write_seq = axi4_master_write_seq::type_id::create($sformatf("incr_write_%0d", addr_offset));
            write_seq.start_address = addr;
            write_seq.burst_length = 1;
            write_seq.burst_size = 8;
            write_seq.test_data_pattern = expected_data;
            write_seq.start(env.master_agent[addr_offset % 8].sequencer);
            #25ns;
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("incr_read_%0d", addr_offset));
            read_seq.start_address = addr;
            read_seq.burst_length = 1;
            read_seq.burst_size = 8;
            read_seq.expected_data_pattern = expected_data;
            read_seq.start(env.master_agent[addr_offset % 8].sequencer);
            #25ns;
        end
    endtask
    
    // Test unaligned transfer scenarios
    task test_unaligned_transfers();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test unaligned addresses with different sizes
        int transfer_sizes[] = {1, 2, 4, 8, 16, 32, 64, 128};
        
        foreach(transfer_sizes[i]) begin
            int size = transfer_sizes[i];
            
            // Test various unaligned offsets
            for (int offset = 1; offset < size && offset < 16; offset++) begin
                bit [63:0] unaligned_addr = (64'h0002_0000 + (i * 1024)) | offset;
                bit [127:0] test_data = {4{$random}};
                
                // Write unaligned data
                write_seq = axi4_master_write_seq::type_id::create($sformatf("unaligned_write_%0d_%0d", size, offset));
                write_seq.start_address = unaligned_addr;
                write_seq.burst_length = 1;
                write_seq.burst_size = size;
                write_seq.test_data_pattern = test_data;
                write_seq.enable_unaligned = 1;
                write_seq.calculate_wstrb_from_address = 1;
                write_seq.start(env.master_agent[i % 8].sequencer);
                #40ns;
                
                // Read back unaligned data
                read_seq = axi4_master_read_seq::type_id::create($sformatf("unaligned_read_%0d_%0d", size, offset));
                read_seq.start_address = unaligned_addr;
                read_seq.burst_length = 1;
                read_seq.burst_size = size;
                read_seq.expected_data_pattern = test_data;
                read_seq.enable_unaligned = 1;
                read_seq.start(env.master_agent[i % 8].sequencer);
                #40ns;
            end
        end
        
        // Test unaligned bursts
        for (int burst_len = 2; burst_len <= 8; burst_len *= 2) begin
            bit [63:0] base_addr = 64'h0002_4000 + (burst_len * 512);
            
            write_seq = axi4_master_write_seq::type_id::create($sformatf("unaligned_burst_write_%0d", burst_len));
            write_seq.start_address = base_addr | 3; // Unaligned start
            write_seq.burst_length = burst_len;
            write_seq.burst_size = 8;
            write_seq.burst_type = axi4_globals_pkg::INCR;
            write_seq.enable_unaligned = 1;
            write_seq.generate_incremental_data = 1;
            write_seq.start(env.master_agent[0].sequencer);
            #(burst_len * 30);
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("unaligned_burst_read_%0d", burst_len));
            read_seq.start_address = base_addr | 3;
            read_seq.burst_length = burst_len;
            read_seq.burst_size = 8;
            read_seq.burst_type = axi4_globals_pkg::INCR;
            read_seq.enable_unaligned = 1;
            read_seq.verify_incremental_data = 1;
            read_seq.start(env.master_agent[1].sequencer);
            #(burst_len * 30);
        end
    endtask
    
    // Test WSTRB pattern validation
    task test_wstrb_patterns();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test all possible WSTRB patterns for 64-bit transfers
        for (int wstrb = 1; wstrb < 256; wstrb++) begin
            if ($countones(wstrb) > 0) begin // At least one byte enabled
                bit [63:0] addr = 64'h0003_0000 + (wstrb * 64);
                bit [63:0] test_data = {2{$random}};
                
                write_seq = axi4_master_write_seq::type_id::create($sformatf("wstrb_write_%02x", wstrb));
                write_seq.start_address = addr;
                write_seq.burst_length = 1;
                write_seq.burst_size = 8; // 64-bit
                write_seq.custom_wstrb = wstrb;
                write_seq.test_data_pattern = test_data;
                write_seq.enable_wstrb_check = 1;
                write_seq.start(env.master_agent[wstrb % 8].sequencer);
                #30ns;
                
                // Read back and verify only enabled bytes
                read_seq = axi4_master_read_seq::type_id::create($sformatf("wstrb_read_%02x", wstrb));
                read_seq.start_address = addr;
                read_seq.burst_length = 1;
                read_seq.burst_size = 8;
                read_seq.expected_wstrb_pattern = wstrb;
                read_seq.expected_data_pattern = test_data;
                read_seq.enable_wstrb_check = 1;
                read_seq.start(env.master_agent[wstrb % 8].sequencer);
                #30ns;
            end
        end
        
        // Test partial write patterns
        typedef struct {
            bit [7:0] wstrb;
            string description;
        } wstrb_test_t;
        
        wstrb_test_t wstrb_tests[] = {
            '{8'b00000001, "byte_0_only"},
            '{8'b10000000, "byte_7_only"}, 
            '{8'b00000011, "bytes_0_1"},
            '{8'b11000000, "bytes_6_7"},
            '{8'b00001111, "lower_nibble"},
            '{8'b11110000, "upper_nibble"},
            '{8'b01010101, "odd_bytes"},
            '{8'b10101010, "even_bytes"},
            '{8'b00110011, "byte_pairs_0"},
            '{8'b11001100, "byte_pairs_1"},
            '{8'b01111110, "middle_bytes"},
            '{8'b10000001, "edge_bytes"}
        };
        
        foreach(wstrb_tests[i]) begin
            bit [63:0] addr = 64'h0003_8000 + (i * 128);
            bit [63:0] test_data = 64'h0123456789ABCDEF;
            
            write_seq = axi4_master_write_seq::type_id::create($sformatf("pattern_%s_write", wstrb_tests[i].description));
            write_seq.start_address = addr;
            write_seq.burst_length = 1;
            write_seq.burst_size = 8;
            write_seq.custom_wstrb = wstrb_tests[i].wstrb;
            write_seq.test_data_pattern = test_data;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #40ns;
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("pattern_%s_read", wstrb_tests[i].description));
            read_seq.start_address = addr;
            read_seq.burst_length = 1;
            read_seq.burst_size = 8;
            read_seq.verify_partial_write = 1;
            read_seq.expected_wstrb_pattern = wstrb_tests[i].wstrb;
            read_seq.start(env.master_agent[i % 8].sequencer);
            #40ns;
        end
    endtask
    
    // Test different data widths
    task test_data_width_variations();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test all valid transfer sizes (1, 2, 4, 8, 16, 32, 64, 128 bytes)
        for (int size_exp = 0; size_exp <= 7; size_exp++) begin
            int transfer_size = 1 << size_exp; // 2^size_exp
            int data_bits = transfer_size * 8;
            bit [1023:0] test_data; // Large enough for 128 bytes
            
            // Generate test data pattern based on transfer size
            for (int byte_idx = 0; byte_idx < transfer_size; byte_idx++) begin
                test_data[byte_idx*8 +: 8] = byte_idx ^ 8'hA5; // XOR pattern
            end
            
            bit [63:0] addr = 64'h0004_0000 + (size_exp * 2048);
            
            write_seq = axi4_master_write_seq::type_id::create($sformatf("width_write_%0d_bytes", transfer_size));
            write_seq.start_address = addr & ~(transfer_size - 1); // Align address
            write_seq.burst_length = 1;
            write_seq.burst_size = transfer_size;
            write_seq.test_data_pattern = test_data;
            write_seq.verify_data_width = data_bits;
            write_seq.start(env.master_agent[size_exp % 8].sequencer);
            #50ns;
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("width_read_%0d_bytes", transfer_size));
            read_seq.start_address = addr & ~(transfer_size - 1);
            read_seq.burst_length = 1;
            read_seq.burst_size = transfer_size;
            read_seq.expected_data_pattern = test_data;
            read_seq.verify_data_width = data_bits;
            read_seq.start(env.master_agent[size_exp % 8].sequencer);
            #50ns;
        end
        
        // Test mixed width transfers
        int mixed_sizes[] = {1, 8, 4, 16, 2, 32, 8, 64};
        bit [63:0] base_addr = 64'h0004_8000;
        
        foreach(mixed_sizes[i]) begin
            bit [1023:0] mixed_data = {32{$random}}; // Random data
            
            write_seq = axi4_master_write_seq::type_id::create($sformatf("mixed_write_%0d", i));
            write_seq.start_address = base_addr + (i * 128);
            write_seq.burst_length = 1;
            write_seq.burst_size = mixed_sizes[i];
            write_seq.test_data_pattern = mixed_data;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #40ns;
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("mixed_read_%0d", i));
            read_seq.start_address = base_addr + (i * 128);
            read_seq.burst_length = 1;
            read_seq.burst_size = mixed_sizes[i];
            read_seq.expected_data_pattern = mixed_data;
            read_seq.start(env.master_agent[i % 8].sequencer);
            #40ns;
        end
    endtask
    
    // Test burst data consistency
    task test_burst_data_consistency();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test different burst types with data patterns
        int burst_types[] = {0, 1, 2}; // FIXED, INCR, WRAP
        int burst_lengths[] = {1, 2, 4, 8, 16, 32, 64, 128};
        
        foreach(burst_types[i]) begin
            foreach(burst_lengths[j]) begin
                if (burst_types[i] == 2 && !(burst_lengths[j] inside {2, 4, 8, 16})) continue; // WRAP constraint
                
                bit [63:0] addr = 64'h0005_0000 + (i * 64'h1_0000) + (j * 2048);
                if (burst_types[i] == 2) addr = addr & ~((burst_lengths[j] * 8) - 1); // WRAP alignment
                
                write_seq = axi4_master_write_seq::type_id::create($sformatf("burst_write_t%0d_l%0d", burst_types[i], burst_lengths[j]));
                write_seq.start_address = addr;
                write_seq.burst_length = burst_lengths[j];
                write_seq.burst_size = 8;
                write_seq.burst_type = burst_types[i];
                write_seq.generate_burst_data_pattern = 1;
                write_seq.data_increment = burst_lengths[j]; // Data changes per beat
                write_seq.start(env.master_agent[(i+j) % 8].sequencer);
                #(burst_lengths[j] * 20);
                
                read_seq = axi4_master_read_seq::type_id::create($sformatf("burst_read_t%0d_l%0d", burst_types[i], burst_lengths[j]));
                read_seq.start_address = addr;
                read_seq.burst_length = burst_lengths[j];
                read_seq.burst_size = 8;
                read_seq.burst_type = burst_types[i];
                read_seq.verify_burst_data_pattern = 1;
                read_seq.expected_data_increment = burst_lengths[j];
                read_seq.start(env.master_agent[(i+j) % 8].sequencer);
                #(burst_lengths[j] * 20);
            end
        end
        
        // Test data continuity across burst boundaries
        for (int burst_id = 0; burst_id < 4; burst_id++) begin
            bit [63:0] addr = 64'h0005_8000 + (burst_id * 1024);
            
            write_seq = axi4_master_write_seq::type_id::create($sformatf("continuous_write_%0d", burst_id));
            write_seq.start_address = addr;
            write_seq.burst_length = 32;
            write_seq.burst_size = 8;
            write_seq.burst_type = axi4_globals_pkg::INCR;
            write_seq.continuous_data_pattern = 1;
            write_seq.pattern_seed = burst_id;
            write_seq.start(env.master_agent[burst_id].sequencer);
            #200ns;
            
            // Read back in smaller chunks to verify continuity
            for (int chunk = 0; chunk < 4; chunk++) begin
                read_seq = axi4_master_read_seq::type_id::create($sformatf("continuous_read_%0d_%0d", burst_id, chunk));
                read_seq.start_address = addr + (chunk * 64);
                read_seq.burst_length = 8;
                read_seq.burst_size = 8;
                read_seq.verify_continuous_pattern = 1;
                read_seq.pattern_offset = chunk * 8;
                read_seq.pattern_seed = burst_id;
                read_seq.start(env.master_agent[burst_id].sequencer);
                #80ns;
            end
        end
    endtask
    
    // Test overlapping address scenarios
    task test_overlapping_addresses();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test write-write conflicts at same address
        bit [63:0] conflict_addr = 64'h0006_0000;
        
        fork
            begin
                write_seq = axi4_master_write_seq::type_id::create("conflict_write_0");
                write_seq.start_address = conflict_addr;
                write_seq.burst_length = 1;
                write_seq.burst_size = 8;
                write_seq.test_data_pattern = 64'hAAAAAAAA_AAAAAAAA;
                write_seq.axi_id = 0;
                write_seq.start(env.master_agent[0].sequencer);
            end
            begin
                #25ns; // Slight delay
                write_seq = axi4_master_write_seq::type_id::create("conflict_write_1");
                write_seq.start_address = conflict_addr;
                write_seq.burst_length = 1;
                write_seq.burst_size = 8;
                write_seq.test_data_pattern = 64'h55555555_55555555;
                write_seq.axi_id = 1;
                write_seq.start(env.master_agent[1].sequencer);
            end
        join
        
        #100ns;
        
        // Read back to see which write won
        read_seq = axi4_master_read_seq::type_id::create("conflict_read");
        read_seq.start_address = conflict_addr;
        read_seq.burst_length = 1;
        read_seq.burst_size = 8;
        read_seq.check_write_ordering = 1;
        read_seq.start(env.master_agent[2].sequencer);
        #50ns;
        
        // Test overlapping bursts
        for (int overlap_test = 0; overlap_test < 4; overlap_test++) begin
            bit [63:0] base_addr = 64'h0006_1000 + (overlap_test * 512);
            
            fork
                begin
                    write_seq = axi4_master_write_seq::type_id::create($sformatf("overlap_write_a_%0d", overlap_test));
                    write_seq.start_address = base_addr;
                    write_seq.burst_length = 16;
                    write_seq.burst_size = 8;
                    write_seq.test_data_pattern = 64'hDEADBEEF_CAFEBABE;
                    write_seq.start(env.master_agent[0].sequencer);
                end
                begin
                    #50ns;
                    write_seq = axi4_master_write_seq::type_id::create($sformatf("overlap_write_b_%0d", overlap_test));
                    write_seq.start_address = base_addr + 64; // Overlapping region
                    write_seq.burst_length = 16;
                    write_seq.burst_size = 8;
                    write_seq.test_data_pattern = 64'h12345678_9ABCDEF0;
                    write_seq.start(env.master_agent[1].sequencer);
                end
            join
            
            // Verify overlap handling
            read_seq = axi4_master_read_seq::type_id::create($sformatf("overlap_verify_%0d", overlap_test));
            read_seq.start_address = base_addr;
            read_seq.burst_length = 32; // Read entire overlapping region
            read_seq.burst_size = 8;
            read_seq.verify_overlap_handling = 1;
            read_seq.start(env.master_agent[2].sequencer);
            #300ns;
        end
    endtask
    
    // Test data pattern stress scenarios
    task test_data_pattern_stress();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test walking 1s and 0s patterns
        for (int bit_pos = 0; bit_pos < 64; bit_pos++) begin
            bit [63:0] walking_1 = 64'h1 << bit_pos;
            bit [63:0] walking_0 = ~walking_1;
            bit [63:0] addr = 64'h0007_0000 + (bit_pos * 128);
            
            // Walking 1s test
            write_seq = axi4_master_write_seq::type_id::create($sformatf("walk1_write_%0d", bit_pos));
            write_seq.start_address = addr;
            write_seq.burst_length = 1;
            write_seq.burst_size = 8;
            write_seq.test_data_pattern = walking_1;
            write_seq.start(env.master_agent[bit_pos % 8].sequencer);
            #30ns;
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("walk1_read_%0d", bit_pos));
            read_seq.start_address = addr;
            read_seq.expected_data_pattern = walking_1;
            read_seq.start(env.master_agent[bit_pos % 8].sequencer);
            #30ns;
            
            // Walking 0s test
            write_seq = axi4_master_write_seq::type_id::create($sformatf("walk0_write_%0d", bit_pos));
            write_seq.start_address = addr + 64;
            write_seq.test_data_pattern = walking_0;
            write_seq.start(env.master_agent[bit_pos % 8].sequencer);
            #30ns;
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("walk0_read_%0d", bit_pos));
            read_seq.start_address = addr + 64;
            read_seq.expected_data_pattern = walking_0;
            read_seq.start(env.master_agent[bit_pos % 8].sequencer);
            #30ns;
        end
        
        // Test pseudo-random patterns with known seeds
        for (int seed = 1; seed <= 16; seed++) begin
            bit [63:0] addr = 64'h0007_8000 + (seed * 256);
            
            write_seq = axi4_master_write_seq::type_id::create($sformatf("prng_write_%0d", seed));
            write_seq.start_address = addr;
            write_seq.burst_length = 32;
            write_seq.burst_size = 8;
            write_seq.use_prng_data = 1;
            write_seq.prng_seed = seed;
            write_seq.start(env.master_agent[seed % 8].sequencer);
            #400ns;
            
            read_seq = axi4_master_read_seq::type_id::create($sformatf("prng_read_%0d", seed));
            read_seq.start_address = addr;
            read_seq.burst_length = 32;
            read_seq.burst_size = 8;
            read_seq.use_prng_verify = 1;
            read_seq.prng_seed = seed;
            read_seq.start(env.master_agent[seed % 8].sequencer);
            #400ns;
        end
    endtask
    
    // Test multi-master data coherency
    task test_multi_master_coherency();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Shared memory region for coherency testing
        bit [63:0] shared_base = 64'h0008_0000;
        
        // Test 1: Write from one master, read from all others
        write_seq = axi4_master_write_seq::type_id::create("coherency_master_write");
        write_seq.start_address = shared_base;
        write_seq.burst_length = 16;
        write_seq.burst_size = 8;
        write_seq.test_data_pattern = 64'hC0HERENT_DEADBEEF;
        write_seq.start(env.master_agent[0].sequencer);
        #200ns;
        
        // All other masters read the same data
        fork
            for (int i = 1; i < 8; i++) begin
                automatic int master_id = i;
                fork
                    begin
                        read_seq = axi4_master_read_seq::type_id::create($sformatf("coherency_read_%0d", master_id));
                        read_seq.start_address = shared_base;
                        read_seq.burst_length = 16;
                        read_seq.burst_size = 8;
                        read_seq.expected_data_pattern = 64'hC0HERENT_DEADBEEF;
                        read_seq.verify_coherency = 1;
                        read_seq.start(env.master_agent[master_id].sequencer);
                    end
                join_none
            end
        join
        
        #300ns;
        
        // Test 2: Multiple masters updating shared counters
        fork
            for (int i = 0; i < 8; i++) begin
                automatic int master_id = i;
                fork
                    begin
                        repeat(10) begin
                            // Read-modify-write pattern
                            read_seq = axi4_master_read_seq::type_id::create($sformatf("rmw_read_%0d", master_id));
                            read_seq.start_address = shared_base + (master_id * 64);
                            read_seq.burst_length = 1;
                            read_seq.burst_size = 8;
                            read_seq.save_read_data = 1;
                            read_seq.start(env.master_agent[master_id].sequencer);
                            #50ns;
                            
                            // Increment and write back
                            write_seq = axi4_master_write_seq::type_id::create($sformatf("rmw_write_%0d", master_id));
                            write_seq.start_address = shared_base + (master_id * 64);
                            write_seq.burst_length = 1;
                            write_seq.burst_size = 8;
                            write_seq.use_read_modify_write = 1;
                            write_seq.increment_value = master_id + 1;
                            write_seq.start(env.master_agent[master_id].sequencer);
                            #50ns;
                        end
                    end
                join_none
            end
        join
        
        // Final verification of all counters
        for (int i = 0; i < 8; i++) begin
            read_seq = axi4_master_read_seq::type_id::create($sformatf("final_verify_%0d", i));
            read_seq.start_address = shared_base + (i * 64);
            read_seq.burst_length = 1;
            read_seq.burst_size = 8;
            read_seq.verify_counter_value = 1;
            read_seq.expected_increments = 10;
            read_seq.increment_size = i + 1;
            read_seq.start(env.master_agent[i].sequencer);
            #50ns;
        end
    endtask
    
endclass : axi4_data_integrity_test