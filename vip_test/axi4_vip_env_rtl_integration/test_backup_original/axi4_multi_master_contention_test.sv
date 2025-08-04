//==============================================================================
// AXI4 Multi-Master Contention Test
// Tests arbitration, QoS handling, and multi-master scenarios
// Validates interconnect behavior under high contention
//==============================================================================

class axi4_multi_master_contention_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_multi_master_contention_test)
    
    // Constructor
    function new(string name = "axi4_multi_master_contention_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase - configure for high contention
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Enable contention monitoring
        env_cfg.enable_contention_monitoring = 1;
        env_cfg.enable_qos_arbitration = 1;
        env_cfg.enable_bandwidth_monitoring = 1;
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting multi-master contention test", UVM_LOW)
        
        // Test 1: Basic multi-master access to same slave
        `uvm_info(get_type_name(), "Test 1: Multi-master same slave contention", UVM_MEDIUM)
        test_same_slave_contention();
        
        // Test 2: QoS-based arbitration
        `uvm_info(get_type_name(), "Test 2: QoS-based arbitration", UVM_MEDIUM)
        test_qos_arbitration();
        
        // Test 3: Different priority levels
        `uvm_info(get_type_name(), "Test 3: Priority level arbitration", UVM_MEDIUM)
        test_priority_arbitration();
        
        // Test 4: Bandwidth sharing and fairness
        `uvm_info(get_type_name(), "Test 4: Bandwidth sharing test", UVM_MEDIUM)
        test_bandwidth_sharing();
        
        // Test 5: Hot slave contention
        `uvm_info(get_type_name(), "Test 5: Hot slave contention", UVM_MEDIUM)
        test_hot_slave_contention();
        
        // Test 6: Distributed load testing
        `uvm_info(get_type_name(), "Test 6: Distributed load testing", UVM_MEDIUM)
        test_distributed_load();
        
        // Test 7: Burst interference testing
        `uvm_info(get_type_name(), "Test 7: Burst interference testing", UVM_MEDIUM)
        test_burst_interference();
        
        // Test 8: Maximum throughput stress test
        `uvm_info(get_type_name(), "Test 8: Maximum throughput stress", UVM_MEDIUM)
        test_maximum_throughput();
        
        `uvm_info(get_type_name(), "Completed multi-master contention test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    // Test basic multi-master access to same slave
    task test_same_slave_contention();
        axi4_master_write_seq write_seq[8];
        axi4_master_read_seq read_seq[8];
        
        // All masters target slave 0 simultaneously
        fork
            for (int i = 0; i < 8; i++) begin
                automatic int master_id = i;
                fork
                    begin
                        // Write sequence
                        write_seq[master_id] = axi4_master_write_seq::type_id::create($sformatf("contention_write_%0d", master_id));
                        write_seq[master_id].start_address = 64'h0000_1000 + (master_id * 256);
                        write_seq[master_id].burst_length = 8;
                        write_seq[master_id].axi_id = master_id;
                        write_seq[master_id].target_slave = 0; // All target slave 0
                        write_seq[master_id].start(env.master_agent[master_id].sequencer);
                        
                        // Read sequence
                        read_seq[master_id] = axi4_master_read_seq::type_id::create($sformatf("contention_read_%0d", master_id));
                        read_seq[master_id].start_address = 64'h0000_1000 + (master_id * 256);
                        read_seq[master_id].burst_length = 4;
                        read_seq[master_id].axi_id = master_id + 8;
                        read_seq[master_id].target_slave = 0;
                        read_seq[master_id].start(env.master_agent[master_id].sequencer);
                    end
                join_none
            end
        join
        
        #500ns; // Allow all transactions to complete
        
        // Repeat with different timing offsets
        for (int offset = 0; offset < 8; offset++) begin
            fork
                for (int i = 0; i < 8; i++) begin
                    automatic int master_id = i;
                    automatic int delay = (master_id * offset * 5);
                    fork
                        begin
                            #(delay * 1ns);
                            write_seq[master_id] = axi4_master_write_seq::type_id::create($sformatf("offset_write_%0d_%0d", offset, master_id));
                            write_seq[master_id].start_address = 64'h0000_2000 + (master_id * 128);
                            write_seq[master_id].burst_length = 16;
                            write_seq[master_id].axi_id = master_id;
                            write_seq[master_id].start(env.master_agent[master_id].sequencer);
                        end
                    join_none
                end
            join
            #300ns;
        end
    endtask
    
    // Test QoS-based arbitration
    task test_qos_arbitration();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Create transactions with different QoS levels
        int qos_levels[] = '{0, 4, 8, 12, 15}; // Low to high priority
        
        // Start all QoS transactions simultaneously
        fork
            for (int i = 0; i < 5; i++) begin
                automatic int qos_idx = i;
                automatic int qos_val = qos_levels[qos_idx];
                fork
                    begin
                        // High QoS write
                        write_seq = axi4_master_write_seq::type_id::create($sformatf("qos_write_%0d", qos_val));
                        write_seq.start_address = 64'h0001_0000 + (qos_idx * 512);
                        write_seq.burst_length = 32;
                        write_seq.qos_value = qos_val;
                        write_seq.axi_id = qos_idx;
                        write_seq.measure_completion_time = 1;
                        write_seq.start(env.master_agent[qos_idx].sequencer);
                        
                        // High QoS read
                        read_seq = axi4_master_read_seq::type_id::create($sformatf("qos_read_%0d", qos_val));
                        read_seq.start_address = 64'h0001_0000 + (qos_idx * 512);
                        read_seq.burst_length = 16;
                        read_seq.qos_value = qos_val;
                        read_seq.axi_id = qos_idx + 8;
                        read_seq.measure_completion_time = 1;
                        read_seq.start(env.master_agent[qos_idx].sequencer);
                    end
                join_none
            end
        join
        
        #800ns; // Wait for QoS arbitration to take effect
        
        // Test QoS preemption scenarios
        fork
            begin
                // Low QoS long burst
                write_seq = axi4_master_write_seq::type_id::create("low_qos_long");
                write_seq.start_address = 64'h0001_4000;
                write_seq.burst_length = 256;
                write_seq.qos_value = 0; // Lowest priority
                write_seq.axi_id = 10;
                write_seq.start(env.master_agent[0].sequencer);
            end
            begin
                #200ns; // Allow low QoS to start
                // High QoS preemption
                write_seq = axi4_master_write_seq::type_id::create("high_qos_preempt");
                write_seq.start_address = 64'h0001_5000;
                write_seq.burst_length = 4;
                write_seq.qos_value = 15; // Highest priority
                write_seq.axi_id = 11;
                write_seq.expect_preemption = 1;
                write_seq.start(env.master_agent[1].sequencer);
            end
        join
    endtask
    
    // Test priority level arbitration
    task test_priority_arbitration();
        axi4_master_write_seq write_seq;
        
        // Create priority scenarios
        typedef struct {
            int master_id;
            int priority_level;
            int burst_length;
            bit [63:0] address;
        } priority_config_t;
        
        priority_config_t configs[] = '{
            '{0, 3, 64, 64'h0002_0000}, // High priority, long burst
            '{1, 2, 32, 64'h0002_1000}, // Medium priority
            '{2, 1, 16, 64'h0002_2000}, // Low priority
            '{3, 3, 8,  64'h0002_3000}, // High priority, short burst
            '{4, 0, 128,64'h0002_4000}, // Lowest priority, longest burst
            '{5, 2, 24, 64'h0002_5000}, // Medium priority
            '{6, 3, 4,  64'h0002_6000}, // High priority, shortest burst
            '{7, 1, 48, 64'h0002_7000}  // Low priority
        };
        
        // Launch all priority-based transactions
        fork
            for (int i = 0; i < 8; i++) begin
                automatic int idx = i;
                fork
                    begin
                        write_seq = axi4_master_write_seq::type_id::create($sformatf("priority_%0d_m%0d", configs[idx].priority_level, configs[idx].master_id));
                        write_seq.start_address = configs[idx].address;
                        write_seq.burst_length = configs[idx].burst_length;
                        write_seq.priority_level = configs[idx].priority_level;
                        write_seq.axi_id = configs[idx].master_id;
                        write_seq.measure_latency = 1;
                        write_seq.start(env.master_agent[configs[idx].master_id].sequencer);
                    end
                join_none
            end
        join
        
        #1000ns; // Allow priority arbitration to complete
        
        // Test priority inversion scenarios
        fork
            begin
                // Low priority master holds resource
                write_seq = axi4_master_write_seq::type_id::create("low_priority_hold");
                write_seq.start_address = 64'h0002_8000;
                write_seq.burst_length = 128;
                write_seq.priority_level = 0;
                write_seq.hold_resource = 1;
                write_seq.start(env.master_agent[0].sequencer);
            end
            begin
                #100ns;
                // High priority master needs same resource
                write_seq = axi4_master_write_seq::type_id::create("high_priority_blocked");
                write_seq.start_address = 64'h0002_8000; // Same address
                write_seq.burst_length = 4;
                write_seq.priority_level = 3;
                write_seq.detect_priority_inversion = 1;
                write_seq.start(env.master_agent[1].sequencer);
            end
        join
    endtask
    
    // Test bandwidth sharing and fairness
    task test_bandwidth_sharing();
        axi4_master_write_seq write_seq[8];
        axi4_master_read_seq read_seq[8];
        int transaction_counts[8];
        real start_time, end_time;
        
        start_time = $realtime;
        
        // Equal bandwidth sharing test
        fork
            for (int i = 0; i < 8; i++) begin
                automatic int master_id = i;
                fork
                    begin
                        transaction_counts[master_id] = 0;
                        repeat(50) begin // Each master attempts 50 transactions
                            write_seq[master_id] = axi4_master_write_seq::type_id::create($sformatf("bw_write_%0d_%0d", master_id, transaction_counts[master_id]));
                            write_seq[master_id].start_address = 64'h0003_0000 + (master_id * 2048) + (transaction_counts[master_id] * 64);
                            write_seq[master_id].burst_length = 4;
                            write_seq[master_id].axi_id = master_id;
                            write_seq[master_id].fair_share_mode = 1;
                            write_seq[master_id].start(env.master_agent[master_id].sequencer);
                            transaction_counts[master_id]++;
                            #10ns; // Small gap between transactions
                        end
                    end
                join_none
            end
        join
        
        end_time = $realtime;
        
        // Analyze bandwidth distribution
        `uvm_info(get_type_name(), $sformatf("Bandwidth test completed in %0.2f ns", (end_time - start_time)/1ns), UVM_LOW)
        
        // Weighted bandwidth sharing test
        begin
            int weights[] = '{1, 2, 4, 8, 4, 2, 1, 1}; // Different bandwidth weights
            fork
            for (int i = 0; i < 8; i++) begin
                automatic int master_id = i;
                automatic int weight = weights[master_id];
                fork
                    begin
                        repeat(weight * 20) begin // Transactions proportional to weight
                            write_seq[master_id] = axi4_master_write_seq::type_id::create($sformatf("weighted_write_%0d", master_id));
                            write_seq[master_id].start_address = 64'h0003_8000 + (master_id * 1024);
                            write_seq[master_id].burst_length = 8;
                            write_seq[master_id].bandwidth_weight = weight;
                            write_seq[master_id].start(env.master_agent[master_id].sequencer);
                            #(20ns / weight); // Higher weight = shorter delay
                        end
                    end
                join_none
            end
        join
        
        #500ns; // Allow weighted sharing to stabilize
        end // End weights begin block
    endtask
    
    // Test hot slave contention
    task test_hot_slave_contention();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // All masters heavily access slave 0 (hot slave)
        fork
            for (int i = 0; i < 8; i++) begin
                automatic int master_id = i;
                fork
                    begin
                        repeat(20) begin
                            // Write to hot slave
                            write_seq = axi4_master_write_seq::type_id::create($sformatf("hot_write_%0d", master_id));
                            write_seq.start_address = 64'h0000_0000 + (master_id * 512); // All to slave 0
                            write_seq.burst_length = $urandom_range(1, 16);
                            write_seq.axi_id = master_id;
                            write_seq.contention_aware = 1;
                            write_seq.start(env.master_agent[master_id].sequencer);
                            
                            // Read from hot slave
                            read_seq = axi4_master_read_seq::type_id::create($sformatf("hot_read_%0d", master_id));
                            read_seq.start_address = 64'h0000_0000 + (master_id * 512);
                            read_seq.burst_length = $urandom_range(1, 8);
                            read_seq.axi_id = master_id + 8;
                            read_seq.contention_aware = 1;
                            read_seq.start(env.master_agent[master_id].sequencer);
                            
                            #($urandom_range(10, 50) * 1ns); // Random delays
                        end
                    end
                join_none
            end
        join
        
        #1000ns; // Allow hot slave contention to resolve
        
        // Test with backoff strategies
        fork
            for (int i = 0; i < 8; i++) begin
                automatic int master_id = i;
                fork
                    begin
                        repeat(15) begin
                            write_seq = axi4_master_write_seq::type_id::create($sformatf("backoff_write_%0d", master_id));
                            write_seq.start_address = 64'h0000_0000 + (master_id * 256);
                            write_seq.burst_length = 8;
                            write_seq.enable_backoff = 1;
                            write_seq.backoff_multiplier = master_id + 1;
                            write_seq.start(env.master_agent[master_id].sequencer);
                            
                            // Exponential backoff delay
                            #((2 ** master_id) * 10ns);
                        end
                    end
                join_none
            end
        join
    endtask
    
    // Test distributed load across all slaves
    task test_distributed_load();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Distribute load evenly across all slaves
        fork
            for (int master = 0; master < 8; master++) begin
                automatic int m_id = master;
                fork
                    begin
                        for (int slave = 0; slave < 8; slave++) begin
                            automatic int s_id = slave;
                            fork
                                begin
                                    // Write to each slave
                                    write_seq = axi4_master_write_seq::type_id::create($sformatf("dist_write_m%0d_s%0d", m_id, s_id));
                                    write_seq.start_address = 64'h0000_0000 + (s_id * 64'h0001_0000) + (m_id * 1024);
                                    write_seq.burst_length = 8;
                                    write_seq.axi_id = m_id;
                                    write_seq.target_slave = s_id;
                                    write_seq.start(env.master_agent[m_id].sequencer);
                                    
                                    // Read from each slave
                                    read_seq = axi4_master_read_seq::type_id::create($sformatf("dist_read_m%0d_s%0d", m_id, s_id));
                                    read_seq.start_address = 64'h0000_0000 + (s_id * 64'h0001_0000) + (m_id * 1024);
                                    read_seq.burst_length = 4;
                                    read_seq.axi_id = m_id + 8;
                                    read_seq.target_slave = s_id;
                                    read_seq.start(env.master_agent[m_id].sequencer);
                                end
                            join_none
                        end
                    end
                join_none
            end
        join
        
        #800ns; // Allow distributed load to complete
    endtask
    
    // Test burst interference
    task test_burst_interference();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        
        // Long bursts vs short bursts interference
        fork
            begin
                // Long burst masters
                for (int i = 0; i < 4; i++) begin
                    automatic int master_id = i;
                    fork
                        begin
                            write_seq = axi4_master_write_seq::type_id::create($sformatf("long_burst_%0d", master_id));
                            write_seq.start_address = 64'h0005_0000 + (master_id * 8192);
                            write_seq.burst_length = 256; // Very long burst
                            write_seq.axi_id = master_id;
                            write_seq.measure_interference = 1;
                            write_seq.start(env.master_agent[master_id].sequencer);
                        end
                    join_none
                end
            end
            begin
                #100ns; // Let long bursts start
                // Short burst masters (should interfere)
                for (int i = 4; i < 8; i++) begin
                    automatic int master_id = i;
                    fork
                        begin
                            repeat(50) begin // Many short bursts
                                write_seq = axi4_master_write_seq::type_id::create($sformatf("short_burst_%0d", master_id));
                                write_seq.start_address = 64'h0005_0000 + ((master_id - 4) * 8192) + 4096;
                                write_seq.burst_length = 1; // Single transfer
                                write_seq.axi_id = master_id;
                                write_seq.high_priority = 1;
                                write_seq.start(env.master_agent[master_id].sequencer);
                                #20ns;
                            end
                        end
                    join_none
                end
            end
        join
        
        // Test read-write interference
        fork
            for (int i = 0; i < 8; i++) begin
                automatic int master_id = i;
                fork
                    begin
                        // Interleaved read-write pattern
                        repeat(10) begin
                            write_seq = axi4_master_write_seq::type_id::create($sformatf("rw_write_%0d", master_id));
                            write_seq.start_address = 64'h0006_0000 + (master_id * 2048);
                            write_seq.burst_length = 16;
                            write_seq.axi_id = master_id * 2;
                            write_seq.start(env.master_agent[master_id].sequencer);
                            
                            read_seq = axi4_master_read_seq::type_id::create($sformatf("rw_read_%0d", master_id));
                            read_seq.start_address = 64'h0006_0000 + (master_id * 2048) + 1024;
                            read_seq.burst_length = 8;
                            read_seq.axi_id = (master_id * 2) + 1;
                            read_seq.start(env.master_agent[master_id].sequencer);
                            
                            #50ns;
                        end
                    end
                join_none
            end
        join
    endtask
    
    // Test maximum throughput stress
    task test_maximum_throughput();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        real start_time, end_time;
        int total_transactions = 0;
        
        `uvm_info(get_type_name(), "Starting maximum throughput stress test", UVM_LOW)
        start_time = $realtime;
        
        // Maximum load on all masters and slaves
        fork
            for (int i = 0; i < 8; i++) begin
                automatic int master_id = i;
                fork
                    begin
                        repeat(100) begin // High transaction count
                            fork
                                begin
                                    write_seq = axi4_master_write_seq::type_id::create($sformatf("max_write_%0d", master_id));
                                    write_seq.start_address = 64'h0007_0000 + (master_id * 4096) + ($urandom % 2048);
                                    write_seq.burst_length = $urandom_range(1, 256);
                                    write_seq.burst_size = 1 << $urandom_range(0, 7); // 1 to 128 bytes
                                    write_seq.axi_id = master_id;
                                    write_seq.max_throughput_mode = 1;
                                    write_seq.start(env.master_agent[master_id].sequencer);
                                    total_transactions++;
                                end
                                begin
                                    read_seq = axi4_master_read_seq::type_id::create($sformatf("max_read_%0d", master_id));
                                    read_seq.start_address = 64'h0007_0000 + (master_id * 4096) + ($urandom % 2048);
                                    read_seq.burst_length = $urandom_range(1, 128);
                                    read_seq.burst_size = 1 << $urandom_range(0, 7);
                                    read_seq.axi_id = master_id + 8;
                                    read_seq.max_throughput_mode = 1;
                                    read_seq.start(env.master_agent[master_id].sequencer);
                                    total_transactions++;
                                end
                            join_none
                            
                            // Minimal delay for maximum stress
                            #1ns;
                        end
                    end
                join_none
            end
        join
        
        end_time = $realtime;
        
        `uvm_info(get_type_name(), $sformatf("Maximum throughput test completed: %0d transactions in %0.2f ns", 
                  total_transactions, (end_time - start_time)/1ns), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Average throughput: %0.2f transactions/ns", 
                  total_transactions / ((end_time - start_time)/1ns)), UVM_LOW)
    endtask
    
endclass : axi4_multi_master_contention_test