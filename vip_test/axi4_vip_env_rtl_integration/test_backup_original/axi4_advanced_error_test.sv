//==============================================================================
// AXI4 Advanced Error Injection Test
// Comprehensive error scenarios including SLVERR, DECERR, and protocol violations
// Tests error recovery and system robustness
//==============================================================================

class axi4_advanced_error_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_advanced_error_test)
    
    // Constructor
    function new(string name = "axi4_advanced_error_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase - configure error injection
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Enable comprehensive error injection
        env_cfg.enable_error_injection = 1;
        env_cfg.enable_protocol_violations = 1;
        env_cfg.enable_timeout_detection = 1;
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting advanced error injection test", UVM_LOW)
        
        // Test 1: SLVERR response injection
        `uvm_info(get_type_name(), "Test 1: SLVERR response injection", UVM_MEDIUM)
        test_slverr_injection();
        
        // Test 2: DECERR response injection  
        `uvm_info(get_type_name(), "Test 2: DECERR response injection", UVM_MEDIUM)
        test_decerr_injection();
        
        // Test 3: Protocol violation detection
        `uvm_info(get_type_name(), "Test 3: Protocol violation detection", UVM_MEDIUM)
        test_protocol_violations();
        
        // Test 4: Timeout and deadlock scenarios
        `uvm_info(get_type_name(), "Test 4: Timeout and deadlock scenarios", UVM_MEDIUM)
        test_timeout_scenarios();
        
        // Test 5: Error recovery mechanisms
        `uvm_info(get_type_name(), "Test 5: Error recovery mechanisms", UVM_MEDIUM)
        test_error_recovery();
        
        // Test 6: Burst error scenarios
        `uvm_info(get_type_name(), "Test 6: Burst error scenarios", UVM_MEDIUM)
        test_burst_errors();
        
        // Test 7: Multi-master error handling
        `uvm_info(get_type_name(), "Test 7: Multi-master error handling", UVM_MEDIUM)
        test_multi_master_errors();
        
        `uvm_info(get_type_name(), "Completed advanced error injection test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    // Test SLVERR response injection
    task test_slverr_injection();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Configure slave to generate SLVERR for specific address ranges
        bit [63:0] error_addresses[] = '{
            64'h0000_F000, // Reserved address space
            64'h0001_E000, // Protected register space  
            64'h0002_D000, // Read-only memory
            64'h0003_C000  // Access-denied region
        };
        
        foreach(error_addresses[i]) begin
            // Write to error-prone address
            write_seq = axi4_master_write_seq::type_id::create($sformatf("slverr_write_%0d", i));
            write_seq.start_address = error_addresses[i];
            write_seq.burst_length = 4;
            write_seq.expect_response = axi4_globals_pkg::SLVERR;
            write_seq.enable_error_checking = 1;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #100ns;
            
            // Read from error-prone address
            read_seq = axi4_master_read_seq::type_id::create($sformatf("slverr_read_%0d", i));
            read_seq.start_address = error_addresses[i];
            read_seq.burst_length = 2;
            read_seq.expect_response = axi4_globals_pkg::SLVERR;
            read_seq.enable_error_checking = 1;
            read_seq.start(env.master_agent[i % 8].sequencer);
            #100ns;
        end
        
        // Test SLVERR with different burst lengths
        begin
            int burst_lengths[] = '{1, 4, 8, 16, 32};
            foreach(burst_lengths[i]) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("slverr_burst_%0d", burst_lengths[i]));
            write_seq.start_address = 64'h0000_F800;
            write_seq.burst_length = burst_lengths[i];
            write_seq.expect_response = axi4_globals_pkg::SLVERR;
            write_seq.test_error_propagation = 1;
            write_seq.start(env.master_agent[0].sequencer);
            #150ns;
        end
        end // End burst_lengths begin block
        
        // Test SLVERR with exclusive access
        read_seq = axi4_master_read_seq::type_id::create("slverr_exclusive_read");
        read_seq.start_address = 64'h0000_F400;
        read_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
        read_seq.expect_response = axi4_globals_pkg::SLVERR;
        read_seq.start(env.master_agent[1].sequencer);
        #80ns;
        
        write_seq = axi4_master_write_seq::type_id::create("slverr_exclusive_write");
        write_seq.start_address = 64'h0000_F400;
        write_seq.lock_type = axi4_globals_pkg::EXCLUSIVE;
        write_seq.expect_response = axi4_globals_pkg::SLVERR;
        write_seq.start(env.master_agent[1].sequencer);
        #80ns;
    endtask
    
    // Test DECERR response injection
    task test_decerr_injection();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test unmapped address spaces (should generate DECERR)
        bit [63:0] unmapped_addresses[] = '{
            64'hDEAD_BEEF, // Completely unmapped
            64'hFFFF_FFFF, // High unmapped address
            64'h8000_0000, // Gap in memory map
            64'hAAAA_AAAA  // Random unmapped address
        };
        
        foreach(unmapped_addresses[i]) begin
            // Write to unmapped address
            write_seq = axi4_master_write_seq::type_id::create($sformatf("decerr_write_%0d", i));
            write_seq.start_address = unmapped_addresses[i];
            write_seq.burst_length = 1;
            write_seq.expect_response = axi4_globals_pkg::DECERR;
            write_seq.enable_error_checking = 1;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #80ns;
            
            // Read from unmapped address
            read_seq = axi4_master_read_seq::type_id::create($sformatf("decerr_read_%0d", i));
            read_seq.start_address = unmapped_addresses[i];
            read_seq.burst_length = 1;
            read_seq.expect_response = axi4_globals_pkg::DECERR;
            read_seq.enable_error_checking = 1;
            read_seq.start(env.master_agent[i % 8].sequencer);
            #80ns;
        end
        
        // Test DECERR with bursts spanning mapped/unmapped regions
        write_seq = axi4_master_write_seq::type_id::create("decerr_span_write");
        write_seq.start_address = 64'h7FFF_FFE0; // Near boundary
        write_seq.burst_length = 16; // Spans into unmapped region
        write_seq.expect_response = axi4_globals_pkg::DECERR;
        write_seq.test_boundary_crossing = 1;
        write_seq.start(env.master_agent[0].sequencer);
        #120ns;
        
        // Test concurrent DECERR from multiple masters
        fork
            begin
                write_seq = axi4_master_write_seq::type_id::create("concurrent_decerr_0");
                write_seq.start_address = 64'hFEED_FACE;
                write_seq.expect_response = axi4_globals_pkg::DECERR;
                write_seq.start(env.master_agent[0].sequencer);
            end
            begin
                write_seq = axi4_master_write_seq::type_id::create("concurrent_decerr_1");
                write_seq.start_address = 64'hCAFE_BABE;
                write_seq.expect_response = axi4_globals_pkg::DECERR;
                write_seq.start(env.master_agent[1].sequencer);
            end
            begin
                write_seq = axi4_master_write_seq::type_id::create("concurrent_decerr_2");
                write_seq.start_address = 64'hBEEF_DEAD;
                write_seq.expect_response = axi4_globals_pkg::DECERR;
                write_seq.start(env.master_agent[0].sequencer);
            end
        join
    endtask
    
    // Test protocol violation detection
    task test_protocol_violations();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test invalid burst type combinations
        write_seq = axi4_master_write_seq::type_id::create("invalid_wrap_length");
        write_seq.start_address = 64'h0001_0000;
        write_seq.burst_type = axi4_globals_pkg::WRAP;
        write_seq.burst_length = 3; // Invalid for WRAP (must be 2,4,8,16)
        write_seq.expect_protocol_error = 1;
        write_seq.start(env.master_agent[0].sequencer);
        #100ns;
        
        // Test 4KB boundary violation
        write_seq = axi4_master_write_seq::type_id::create("4kb_boundary_violation");
        write_seq.start_address = 64'h0000_0FF0; // Near 4KB boundary
        write_seq.burst_type = axi4_globals_pkg::INCR;
        write_seq.burst_length = 32; // Will cross 4KB boundary
        write_seq.burst_size = 8;
        write_seq.expect_protocol_error = 1;
        write_seq.force_boundary_crossing = 1;
        write_seq.start(env.master_agent[1].sequencer);
        #150ns;
        
        // Test invalid burst size
        write_seq = axi4_master_write_seq::type_id::create("invalid_burst_size");
        write_seq.start_address = 64'h0002_0000;
        write_seq.burst_size = 256; // Invalid (max is 128)
        write_seq.expect_protocol_error = 1;
        write_seq.start(env.master_agent[0].sequencer);
        #80ns;
        
        // Test unaligned WRAP burst
        write_seq = axi4_master_write_seq::type_id::create("unaligned_wrap");
        write_seq.start_address = 64'h0003_0001; // Unaligned
        write_seq.burst_type = axi4_globals_pkg::WRAP;
        write_seq.burst_length = 4;
        write_seq.burst_size = 8;
        write_seq.expect_protocol_error = 1;
        write_seq.force_unaligned_wrap = 1;
        write_seq.start(env.master_agent[1].sequencer);
        #100ns;
        
        // Test excessive burst length for AXI3 compatibility mode
        write_seq = axi4_master_write_seq::type_id::create("excessive_burst_axi3");
        write_seq.start_address = 64'h0004_0000;
        write_seq.burst_length = 32; // > 16 for AXI3
        write_seq.axi3_compatibility_mode = 1;
        write_seq.expect_protocol_error = 1;
        write_seq.start(env.master_agent[0].sequencer);
        #120ns;
    endtask
    
    // Test timeout and deadlock scenarios
    task test_timeout_scenarios();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test address channel timeout
        write_seq = axi4_master_write_seq::type_id::create("addr_timeout");
        write_seq.start_address = 64'h0005_0000;
        write_seq.simulate_addr_timeout = 1;
        write_seq.timeout_cycles = 1000;
        write_seq.start(env.master_agent[0].sequencer);
        #2000ns; // Wait for timeout
        
        // Test data channel timeout
        write_seq = axi4_master_write_seq::type_id::create("data_timeout");
        write_seq.start_address = 64'h0005_1000;
        write_seq.burst_length = 8;
        write_seq.simulate_data_timeout = 1;
        write_seq.timeout_cycles = 500;
        write_seq.start(env.master_agent[1].sequencer);
        #1500ns;
        
        // Test response channel timeout
        read_seq = axi4_master_read_seq::type_id::create("resp_timeout");
        read_seq.start_address = 64'h0005_2000;
        read_seq.burst_length = 4;
        read_seq.simulate_resp_timeout = 1;
        read_seq.timeout_cycles = 800;
        read_seq.start(env.master_agent[0].sequencer);
        #2000ns;
        
        // Test deadlock scenario (mutual waiting)
        fork
            begin
                write_seq = axi4_master_write_seq::type_id::create("deadlock_master_0");
                write_seq.start_address = 64'h0005_3000;
                write_seq.create_deadlock_scenario = 1;
                write_seq.deadlock_partner = 1;
                write_seq.start(env.master_agent[0].sequencer);
            end
            begin
                write_seq = axi4_master_write_seq::type_id::create("deadlock_master_1");
                write_seq.start_address = 64'h0005_4000;
                write_seq.create_deadlock_scenario = 1;
                write_seq.deadlock_partner = 0;
                write_seq.start(env.master_agent[1].sequencer);
            end
        join_any
        #1000ns; // Wait for deadlock detection
    endtask
    
    // Test error recovery mechanisms
    task test_error_recovery();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test recovery after SLVERR
        write_seq = axi4_master_write_seq::type_id::create("slverr_then_recover");
        write_seq.start_address = 64'h0000_F000; // Error address
        write_seq.expect_response = axi4_globals_pkg::SLVERR;
        write_seq.start(env.master_agent[0].sequencer);
        #100ns;
        
        // Follow up with successful transaction
        write_seq = axi4_master_write_seq::type_id::create("recovery_write");
        write_seq.start_address = 64'h0006_0000; // Good address
        write_seq.expect_response = axi4_globals_pkg::OKAY;
        write_seq.test_recovery = 1;
        write_seq.start(env.master_agent[0].sequencer);
        #100ns;
        
        // Test recovery after DECERR
        read_seq = axi4_master_read_seq::type_id::create("decerr_then_recover");
        read_seq.start_address = 64'hDEAD_BEEF; // Unmapped
        read_seq.expect_response = axi4_globals_pkg::DECERR;
        read_seq.start(env.master_agent[1].sequencer);
        #100ns;
        
        // Follow up with successful transaction
        read_seq = axi4_master_read_seq::type_id::create("recovery_read");
        read_seq.start_address = 64'h0006_1000; // Good address
        read_seq.expect_response = axi4_globals_pkg::OKAY;
        read_seq.test_recovery = 1;
        read_seq.start(env.master_agent[1].sequencer);
        #100ns;
        
        // Test system-wide error recovery
        fork
            begin
                // Multiple masters hitting errors simultaneously
                for (int i = 0; i < 4; i++) begin
                    write_seq = axi4_master_write_seq::type_id::create($sformatf("multi_error_%0d", i));
                    write_seq.start_address = 64'hBAD0_0000 + (i * 1024);
                    write_seq.expect_response = axi4_globals_pkg::DECERR;
                    write_seq.start(env.master_agent[i].sequencer);
                    #50ns;
                end
            end
            begin
                // System recovery sequence
                #300ns;
                for (int i = 0; i < 4; i++) begin
                    write_seq = axi4_master_write_seq::type_id::create($sformatf("system_recovery_%0d", i));
                    write_seq.start_address = 64'h0007_0000 + (i * 1024);
                    write_seq.expect_response = axi4_globals_pkg::OKAY;
                    write_seq.test_system_recovery = 1;
                    write_seq.start(env.master_agent[i].sequencer);
                    #80ns;
                end
            end
        join
    endtask
    
    // Test burst-specific error scenarios
    task test_burst_errors();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test error in middle of burst
        write_seq = axi4_master_write_seq::type_id::create("burst_mid_error");
        write_seq.start_address = 64'h0008_0000;
        write_seq.burst_length = 16;
        write_seq.inject_error_at_beat = 8;
        write_seq.error_type = "SLVERR";
        write_seq.start(env.master_agent[0].sequencer);
        #200ns;
        
        // Test error on first beat of burst
        read_seq = axi4_master_read_seq::type_id::create("burst_first_error");
        read_seq.start_address = 64'h0008_1000;
        read_seq.burst_length = 8;
        read_seq.inject_error_at_beat = 1;
        read_seq.error_type = "SLVERR";
        read_seq.start(env.master_agent[1].sequencer);
        #150ns;
        
        // Test error on last beat of burst
        write_seq = axi4_master_write_seq::type_id::create("burst_last_error");
        write_seq.start_address = 64'h0008_2000;
        write_seq.burst_length = 32;
        write_seq.inject_error_at_beat = 32;
        write_seq.error_type = "DECERR";
        write_seq.start(env.master_agent[0].sequencer);
        #300ns;
        
        // Test random errors throughout burst
        read_seq = axi4_master_read_seq::type_id::create("burst_random_errors");
        read_seq.start_address = 64'h0008_3000;
        read_seq.burst_length = 64;
        read_seq.random_error_injection = 1;
        read_seq.error_probability = 10; // 10% chance per beat
        read_seq.start(env.master_agent[1].sequencer);
        #500ns;
    endtask
    
    // Test multi-master error handling
    task test_multi_master_errors();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test error isolation between masters
        fork
            begin
                // Master 0 - normal operation
                write_seq = axi4_master_write_seq::type_id::create("normal_master_0");
                write_seq.start_address = 64'h0009_0000;
                write_seq.burst_length = 8;
                write_seq.expect_response = axi4_globals_pkg::OKAY;
                write_seq.start(env.master_agent[0].sequencer);
            end
            begin
                // Master 1 - encounters errors
                write_seq = axi4_master_write_seq::type_id::create("error_master_1");
                write_seq.start_address = 64'hBAD1_0000;
                write_seq.burst_length = 4;
                write_seq.expect_response = axi4_globals_pkg::DECERR;
                write_seq.start(env.master_agent[1].sequencer);
            end
            begin
                // Master 2 - normal operation (should not be affected)
                read_seq = axi4_master_read_seq::type_id::create("normal_master_2");
                read_seq.start_address = 64'h0009_1000;
                read_seq.burst_length = 16;
                read_seq.expect_response = axi4_globals_pkg::OKAY;
                read_seq.start(env.master_agent[0].sequencer);
            end
        join
        
        // Test error propagation limits
        for (int i = 0; i < 8; i++) begin
            fork
                begin
                    if (i % 2 == 0) begin
                        // Even masters get errors
                        write_seq = axi4_master_write_seq::type_id::create($sformatf("error_master_%0d", i));
                        write_seq.start_address = 64'hE000_0000 + (i * 1024);
                        write_seq.expect_response = axi4_globals_pkg::SLVERR;
                        write_seq.start(env.master_agent[i].sequencer);
                    end else begin
                        // Odd masters remain functional
                        write_seq = axi4_master_write_seq::type_id::create($sformatf("good_master_%0d", i));
                        write_seq.start_address = 64'h0009_2000 + (i * 512);
                        write_seq.expect_response = axi4_globals_pkg::OKAY;
                        write_seq.start(env.master_agent[i].sequencer);
                    end
                end
            join_none
        end
        
        wait fork; // Wait for all masters to complete
        #200ns;
    endtask
    
endclass : axi4_advanced_error_test