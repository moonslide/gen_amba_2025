//==============================================================================
// AXI4 Protocol Compliance Test
// Comprehensive test for AXI4 protocol compliance per IHI0022D specification
// Tests handshake rules, signal timing, and protocol constraints
//==============================================================================

class axi4_protocol_compliance_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_protocol_compliance_test)
    
    // Constructor
    function new(string name = "axi4_protocol_compliance_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase - enable protocol checking
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Enable comprehensive protocol checking
        env_cfg.enable_protocol_checking = 1;
        env_cfg.enable_timing_checks = 1;
        env_cfg.enable_signal_checks = 1;
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting protocol compliance test", UVM_LOW)
        
        // Test 1: Channel handshake compliance
        `uvm_info(get_type_name(), "Test 1: Channel handshake compliance", UVM_MEDIUM)
        test_handshake_compliance();
        
        // Test 2: VALID/READY signal timing
        `uvm_info(get_type_name(), "Test 2: VALID/READY signal timing", UVM_MEDIUM)
        test_valid_ready_timing();
        
        // Test 3: Address channel compliance
        `uvm_info(get_type_name(), "Test 3: Address channel compliance", UVM_MEDIUM)
        test_address_channel_compliance();
        
        // Test 4: Data channel compliance  
        `uvm_info(get_type_name(), "Test 4: Data channel compliance", UVM_MEDIUM)
        test_data_channel_compliance();
        
        // Test 5: Response channel compliance
        `uvm_info(get_type_name(), "Test 5: Response channel compliance", UVM_MEDIUM)
        test_response_channel_compliance();
        
        // Test 6: Write strobe (WSTRB) compliance
        `uvm_info(get_type_name(), "Test 6: Write strobe compliance", UVM_MEDIUM)
        test_write_strobe_compliance();
        
        // Test 7: AXI ID consistency and ordering
        `uvm_info(get_type_name(), "Test 7: AXI ID ordering compliance", UVM_MEDIUM)
        test_axi_id_ordering();
        
        // Test 8: AxCACHE, AxPROT, AxQOS, AxREGION compliance
        `uvm_info(get_type_name(), "Test 8: AXI4 signal compliance", UVM_MEDIUM)
        test_axi4_signals();
        
        `uvm_info(get_type_name(), "Completed protocol compliance test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    // Test handshake compliance: VALID before/after READY
    task test_handshake_compliance();
        axi4_master_write_seq write_seq;
        
        // Test VALID asserted before READY
        write_seq = axi4_master_write_seq::type_id::create("handshake_valid_first");
        write_seq.start_address = 64'h0000_1000;
        write_seq.burst_length = 4;
        write_seq.valid_before_ready = 1;
        write_seq.ready_delay = 10; // READY delayed
        write_seq.start(env.master_agent[0].sequencer);
        #100ns;
        
        // Test READY asserted before VALID
        write_seq = axi4_master_write_seq::type_id::create("handshake_ready_first");
        write_seq.start_address = 64'h0000_2000;
        write_seq.burst_length = 4;
        write_seq.ready_before_valid = 1;
        write_seq.valid_delay = 15; // VALID delayed
        write_seq.start(env.master_agent[1].sequencer);
        #100ns;
        
        // Test simultaneous VALID/READY
        write_seq = axi4_master_write_seq::type_id::create("handshake_simultaneous");
        write_seq.start_address = 64'h0000_3000;
        write_seq.burst_length = 4;
        write_seq.simultaneous_valid_ready = 1;
        write_seq.start(env.master_agent[1].sequencer);
        #100ns;
    endtask
    
    // Test VALID/READY timing rules
    task test_valid_ready_timing();
        axi4_master_read_seq read_seq;
        
        // Test VALID stability (must remain high until handshake)
        read_seq = axi4_master_read_seq::type_id::create("timing_valid_stable");
        read_seq.start_address = 64'h0000_4000;
        read_seq.burst_length = 8;
        read_seq.test_valid_stability = 1;
        read_seq.ready_delay = 20; // Force VALID to stay high
        read_seq.start(env.master_agent[0].sequencer);
        #150ns;
        
        // Test READY can change freely
        read_seq = axi4_master_read_seq::type_id::create("timing_ready_toggle");
        read_seq.start_address = 64'h0000_5000;
        read_seq.burst_length = 4;
        read_seq.test_ready_toggling = 1;
        read_seq.start(env.master_agent[1].sequencer);
        #100ns;
        
        // Test no combinatorial READY->VALID dependency
        read_seq = axi4_master_read_seq::type_id::create("timing_no_combinatorial");
        read_seq.start_address = 64'h0000_6000;
        read_seq.burst_length = 4;
        read_seq.test_combinatorial_path = 1;
        read_seq.start(env.master_agent[1].sequencer);
        #100ns;
    endtask
    
    // Test address channel compliance
    task test_address_channel_compliance();
        axi4_master_write_seq write_seq;
        begin

        int burst_types[] = '{0, 1, 2}; // FIXED, INCR, WRAP
        
        foreach(burst_types[i]) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("addr_compliance_%0d", i));
            write_seq.start_address = 64'h0001_0000 + (i * 4096);
            write_seq.burst_type = burst_types[i];
            write_seq.burst_length = (burst_types[i] == 2) ? 4 : 16; // WRAP needs valid length
            write_seq.burst_size = 8;
            write_seq.test_address_compliance = 1;
            write_seq.start(env.master_agent[i].sequencer);
            #80ns;
        end


        end
        
        // Test address alignment
        begin

        int sizes[] = '{1, 2, 4, 8, 16, 32, 64, 128};
        foreach(sizes[i]) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("addr_align_%0d", i));
            write_seq.start_address = (64'h0002_0000 + (i * 256)) & ~(sizes[i] - 1);
            write_seq.burst_size = sizes[i];
            write_seq.burst_length = 1;
            write_seq.test_address_alignment = 1;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #50ns;
        end


        end
    endtask
    
    // Test data channel compliance
    task test_data_channel_compliance();
        axi4_master_write_seq write_seq;
        
        // Test write data ordering (must match address order for same ID)
        write_seq = axi4_master_write_seq::type_id::create("data_ordering");
        write_seq.start_address = 64'h0003_0000;
        write_seq.burst_length = 16;
        write_seq.axi_id = 5;
        write_seq.test_data_ordering = 1;
        write_seq.start(env.master_agent[0].sequencer);
        #200ns;
        
        // Test WLAST signal placement
        write_seq = axi4_master_write_seq::type_id::create("wlast_placement");
        write_seq.start_address = 64'h0003_1000;
        write_seq.burst_length = 32;
        write_seq.test_wlast_signal = 1;
        write_seq.start(env.master_agent[1].sequencer);
        #300ns;
        
        // Test write interleaving (AXI4 doesn't allow write interleaving)
        fork
            begin
                write_seq = axi4_master_write_seq::type_id::create("no_interleave_1");
                write_seq.start_address = 64'h0003_2000;
                write_seq.burst_length = 8;
                write_seq.axi_id = 10;
                write_seq.test_no_interleaving = 1;
                write_seq.start(env.master_agent[1].sequencer);
            end
            begin
                #25ns; // Slight delay
                write_seq = axi4_master_write_seq::type_id::create("no_interleave_2");
                write_seq.start_address = 64'h0003_3000;
                write_seq.burst_length = 8;
                write_seq.axi_id = 10; // Same ID - should not interleave
                write_seq.test_no_interleaving = 1;
                write_seq.start(env.master_agent[1].sequencer);
            end
        join
    endtask
    
    // Test response channel compliance
    task test_response_channel_compliance();
        axi4_master_read_seq read_seq;
        axi4_master_write_seq write_seq;
        
        // Test read response ordering for same ID
        read_seq = axi4_master_read_seq::type_id::create("read_response_order");
        read_seq.start_address = 64'h0004_0000;
        read_seq.burst_length = 16;
        read_seq.axi_id = 7;
        read_seq.test_response_ordering = 1;
        read_seq.start(env.master_agent[0].sequencer);
        #200ns;
        
        // Test write response for complete burst
        write_seq = axi4_master_write_seq::type_id::create("write_response_complete");
        write_seq.start_address = 64'h0004_1000;
        write_seq.burst_length = 32;
        write_seq.test_response_timing = 1;
        write_seq.start(env.master_agent[1].sequencer);
        #300ns;
        
        // Test different response types
        begin

        int response_types[] = '{0, 1}; // OKAY, EXOKAY (SLVERR/DECERR tested separately)
        foreach(response_types[i]) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("response_type_%0d", i));
            write_seq.start_address = 64'h0004_2000 + (i * 1024);
            write_seq.burst_length = 4;
            write_seq.expected_response = axi4_response_type_e'(response_types[i]);
            write_seq.lock_type = (response_types[i] == 1) ? axi4_globals_pkg::EXCLUSIVE : axi4_globals_pkg::NORMAL;
            write_seq.start(env.master_agent[i].sequencer);
            #100ns;
        end


        end
    endtask
    
    // Test write strobe compliance
    task test_write_strobe_compliance();
        axi4_master_write_seq write_seq;
        
        // Test WSTRB for different data widths
        begin

        int data_widths[] = '{8, 16, 32, 64, 128}; // bits
        foreach(data_widths[i]) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("wstrb_width_%0d", data_widths[i]));
            write_seq.start_address = 64'h0005_0000 + (i * 256);
            write_seq.data_width = data_widths[i];
            write_seq.burst_length = 4;
            write_seq.test_wstrb_compliance = 1;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #80ns;
        end


        end
        
        // Test partial writes with WSTRB
        begin

        int strobe_patterns[] = '{8'h01, 8'h03, 8'h0F, 8'h33, 8'h55, 8'hAA, 8'hF0, 8'hFF};
        foreach(strobe_patterns[i]) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("wstrb_pattern_%02h", strobe_patterns[i]));
            write_seq.start_address = 64'h0005_1000 + (i * 64);
            write_seq.custom_wstrb = strobe_patterns[i];
            write_seq.burst_length = 1;
            write_seq.test_partial_writes = 1;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #50ns;
        end


        end
    endtask
    
    // Test AXI ID ordering rules
    task test_axi_id_ordering();
        axi4_master_read_seq read_seq;
        axi4_master_write_seq write_seq;
        
        // Test same ID ordering (must be in order)
        fork
            begin
                read_seq = axi4_master_read_seq::type_id::create("same_id_read_1");
                read_seq.start_address = 64'h0006_0000;
                read_seq.burst_length = 8;
                read_seq.axi_id = 15;
                read_seq.start(env.master_agent[0].sequencer);
            end
            begin
                #10ns;
                read_seq = axi4_master_read_seq::type_id::create("same_id_read_2");
                read_seq.start_address = 64'h0006_1000;
                read_seq.burst_length = 4;
                read_seq.axi_id = 15; // Same ID - must complete in order
                read_seq.start(env.master_agent[0].sequencer);
            end
        join
        
        // Test different ID out-of-order (allowed)
        fork
            begin
                read_seq = axi4_master_read_seq::type_id::create("diff_id_read_1");
                read_seq.start_address = 64'h0006_2000;
                read_seq.burst_length = 16; // Longer burst
                read_seq.axi_id = 8;
                read_seq.start(env.master_agent[1].sequencer);
            end
            begin
                #10ns;
                read_seq = axi4_master_read_seq::type_id::create("diff_id_read_2");
                read_seq.start_address = 64'h0006_3000;
                read_seq.burst_length = 2; // Shorter burst - may complete first
                read_seq.axi_id = 9; // Different ID - can complete out of order
                read_seq.start(env.master_agent[1].sequencer);
            end
        join
        
        // Test read/write channel independence
        fork
            begin
                read_seq = axi4_master_read_seq::type_id::create("independent_read");
                read_seq.start_address = 64'h0006_4000;
                read_seq.burst_length = 8;
                read_seq.axi_id = 12;
                read_seq.start(env.master_agent[1].sequencer);
            end
            begin
                write_seq = axi4_master_write_seq::type_id::create("independent_write");
                write_seq.start_address = 64'h0006_5000;
                write_seq.burst_length = 8;
                write_seq.axi_id = 12; // Same ID - but different channel
                write_seq.start(env.master_agent[1].sequencer);
            end
        join
    endtask
    
    // Test AXI4-specific signals
    task test_axi4_signals();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Test AxCACHE values
        begin

        int cache_values[] = '{4'b0000, 4'b0010, 4'b0110, 4'b1110, 4'b1111};
        foreach(cache_values[i]) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("cache_test_%0d", i));
            write_seq.start_address = 64'h0007_0000 + (i * 256);
            write_seq.cache_type = cache_values[i];
            write_seq.burst_length = 4;
            write_seq.start(env.master_agent[i % 8].sequencer);
            #60ns;
        end


        end
        
        // Test AxPROT values
        begin

        int prot_values[] = '{3'b000, 3'b001, 3'b010, 3'b011, 3'b100, 3'b101, 3'b110, 3'b111};
        foreach(prot_values[i]) begin
            read_seq = axi4_master_read_seq::type_id::create($sformatf("prot_test_%0d", i));
            read_seq.start_address = 64'h0007_1000 + (i * 128);
            read_seq.protection_type = prot_values[i];
            read_seq.burst_length = 2;
            read_seq.start(env.master_agent[i % 8].sequencer);
            #50ns;
        end


        end
        
        // Test AxQOS values
        for (int qos = 0; qos < 16; qos++) begin
            write_seq = axi4_master_write_seq::type_id::create($sformatf("qos_test_%0d", qos));
            write_seq.start_address = 64'h0007_2000 + (qos * 64);
            write_seq.qos_value = qos;
            write_seq.burst_length = 1;
            write_seq.start(env.master_agent[qos % 8].sequencer);
            #40ns;
        end
        
        // Test AxREGION values
        for (int region = 0; region < 16; region++) begin
            read_seq = axi4_master_read_seq::type_id::create($sformatf("region_test_%0d", region));
            read_seq.start_address = 64'h0007_3000 + (region * 64);
            read_seq.region_value = region;
            read_seq.burst_length = 1;
            read_seq.start(env.master_agent[region % 8].sequencer);
            #40ns;
        end
    endtask
    
endclass : axi4_protocol_compliance_test