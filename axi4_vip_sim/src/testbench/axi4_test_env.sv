//==============================================================================
// AXI4 Test Environment - Top-level testbench environment
// Integrates all agents, scoreboard, and provides configuration management
//==============================================================================

class axi4_test_env extends uvm_env;
    
    // Factory registration
    `uvm_component_utils(axi4_test_env)
    
    // Environment components
    axi4_master_agent m_master_agent;
    axi4_slave_agent  m_slave_agent;
    axi4_scoreboard   m_scoreboard;
    
    // Virtual interface handles
    virtual axi4_if vif;
    
    // Configuration parameters
    bit enable_scoreboard = 1;
    bit enable_coverage = 1;
    string test_name = "axi4_basic_test";
    
    // Environment statistics
    int total_tests_run = 0;
    int tests_passed = 0;
    int tests_failed = 0;
    
    // Constructor
    function new(string name = "axi4_test_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get virtual interface
        if (!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("NOVIF", "Virtual interface must be set for: " + get_full_name())
        end
        
        // Get configuration
        uvm_config_db#(bit)::get(this, "", "enable_scoreboard", enable_scoreboard);
        uvm_config_db#(bit)::get(this, "", "enable_coverage", enable_coverage);
        uvm_config_db#(string)::get(this, "", "test_name", test_name);
        
        // Create and configure master agent
        m_master_agent = axi4_master_agent::type_id::create("m_master_agent", this);
        uvm_config_db#(virtual axi4_if.master)::set(this, "m_master_agent", "master_vif", vif.master);
        uvm_config_db#(virtual axi4_if.monitor)::set(this, "m_master_agent", "monitor_vif", vif.monitor);
        uvm_config_db#(bit)::set(this, "m_master_agent", "is_active", UVM_ACTIVE);
        uvm_config_db#(string)::set(this, "m_master_agent", "agent_name", "AXI4_MASTER");
        
        // Create and configure slave agent
        m_slave_agent = axi4_slave_agent::type_id::create("m_slave_agent", this);
        uvm_config_db#(virtual axi4_if.slave)::set(this, "m_slave_agent", "slave_vif", vif.slave);
        uvm_config_db#(virtual axi4_if.monitor)::set(this, "m_slave_agent", "monitor_vif", vif.monitor);
        uvm_config_db#(bit)::set(this, "m_slave_agent", "is_active", UVM_ACTIVE);
        uvm_config_db#(string)::set(this, "m_slave_agent", "agent_name", "AXI4_SLAVE");
        uvm_config_db#(bit [63:0])::set(this, "m_slave_agent", "base_address", 64'h1000_0000);
        uvm_config_db#(bit [63:0])::set(this, "m_slave_agent", "size_bytes", 64'h1000_0000); // 256MB
        
        // Create scoreboard if enabled
        if (enable_scoreboard) begin
            m_scoreboard = axi4_scoreboard::type_id::create("m_scoreboard", this);
        end
        
        `uvm_info(get_type_name(), $sformatf("AXI4 Test Environment created for test: %s", test_name), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("  Scoreboard: %s", enable_scoreboard ? "ENABLED" : "DISABLED"), UVM_MEDIUM)
        `uvm_info(get_type_name(), $sformatf("  Coverage: %s", enable_coverage ? "ENABLED" : "DISABLED"), UVM_MEDIUM)
    endfunction
    
    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect agents to scoreboard
        if (enable_scoreboard) begin
            m_master_agent.ap.connect(m_scoreboard.master_fifo.analysis_export);
            m_slave_agent.ap.connect(m_scoreboard.slave_fifo.analysis_export);
        end
        
        `uvm_info(get_type_name(), "AXI4 Test Environment connections completed", UVM_MEDIUM)
    endfunction
    
    // End of elaboration phase
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        print_environment_topology();
    endfunction
    
    // Print environment topology
    virtual function void print_environment_topology();
        `uvm_info(get_type_name(), "=== AXI4 ENVIRONMENT TOPOLOGY ===", UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Test Environment: %s", get_full_name()), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Master Agent: %s (%s)", 
                                             m_master_agent.get_full_name(),
                                             m_master_agent.is_active ? "ACTIVE" : "PASSIVE"), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Slave Agent: %s (%s)", 
                                             m_slave_agent.get_full_name(),
                                             m_slave_agent.is_active ? "ACTIVE" : "PASSIVE"), UVM_LOW)
        if (m_scoreboard != null) begin
            `uvm_info(get_type_name(), $sformatf("  Scoreboard: %s", m_scoreboard.get_full_name()), UVM_LOW)
        end
        `uvm_info(get_type_name(), "=================================", UVM_LOW)
    endfunction
    
    // Configure slave memory
    virtual function void configure_slave_memory();
        // Initialize some test patterns in slave memory
        for (int i = 0; i < 1024; i++) begin
            m_slave_agent.write_memory(64'h1000_0000 + i, (i % 256));
        end
        
        // Initialize special test patterns
        m_slave_agent.write_memory(64'h1000_1000, 8'hAA);
        m_slave_agent.write_memory(64'h1000_1001, 8'h55);
        m_slave_agent.write_memory(64'h1000_1002, 8'hFF);
        m_slave_agent.write_memory(64'h1000_1003, 8'h00);
        
        `uvm_info(get_type_name(), "Slave memory initialized with test patterns", UVM_MEDIUM)
    endfunction
    
    // Configure slave behavior
    virtual function void configure_slave_behavior(int error_rate = 5, 
                                                  int read_latency_min = 1, int read_latency_max = 10,
                                                  int write_latency_min = 1, int write_latency_max = 10);
        m_slave_agent.set_error_rate(error_rate);
        m_slave_agent.set_latency_range(read_latency_min, read_latency_max, write_latency_min, write_latency_max);
        
        `uvm_info(get_type_name(), $sformatf("Slave configured: Error rate=%0d%%, Read latency=[%0d:%0d], Write latency=[%0d:%0d]",
                                             error_rate, read_latency_min, read_latency_max, write_latency_min, write_latency_max), UVM_MEDIUM)
    endfunction
    
    // Run a specific sequence on master
    virtual task run_master_sequence(uvm_sequence_base seq, string seq_name = "sequence");
        if (m_master_agent.is_active) begin
            `uvm_info(get_type_name(), $sformatf("Starting %s on master agent", seq_name), UVM_MEDIUM)
            seq.start(m_master_agent.m_sequencer);
            `uvm_info(get_type_name(), $sformatf("Completed %s on master agent", seq_name), UVM_MEDIUM)
        end else begin
            `uvm_error(get_type_name(), "Cannot run sequence on passive master agent")
        end
    endtask
    
    // Run multiple sequences in parallel
    virtual task run_parallel_sequences(uvm_sequence_base sequences[], string sequence_names[]);
        if (sequences.size() != sequence_names.size()) begin
            `uvm_error(get_type_name(), "Sequence array size mismatch")
            return;
        end
        
        if (!m_master_agent.is_active) begin
            `uvm_error(get_type_name(), "Cannot run sequences on passive master agent")
            return;
        end
        
        `uvm_info(get_type_name(), $sformatf("Starting %0d parallel sequences", sequences.size()), UVM_MEDIUM)
        
        fork
            begin
                foreach (sequences[i]) begin
                    fork
                        automatic int idx = i;
                        begin
                            `uvm_info(get_type_name(), $sformatf("Starting parallel sequence: %s", sequence_names[idx]), UVM_MEDIUM)
                            sequences[idx].start(m_master_agent.m_sequencer);
                            `uvm_info(get_type_name(), $sformatf("Completed parallel sequence: %s", sequence_names[idx]), UVM_MEDIUM)
                        end
                    join_none
                end
                wait fork;
            end
        join
        
        `uvm_info(get_type_name(), "All parallel sequences completed", UVM_MEDIUM)
    endtask
    
    // Wait for a specified number of transactions to complete
    virtual task wait_for_transactions(int num_transactions, realtime timeout = 100us);
        realtime start_time = $realtime;
        int initial_count = 0;
        int current_count = 0;
        
        if (m_scoreboard != null) begin
            initial_count = m_scoreboard.total_transactions;
        end
        
        while (current_count < (initial_count + num_transactions)) begin
            #1us;
            
            if (m_scoreboard != null) begin
                current_count = m_scoreboard.total_transactions;
            end else begin
                current_count++; // Fallback if no scoreboard
            end
            
            if (($realtime - start_time) > timeout) begin
                `uvm_error(get_type_name(), $sformatf("Timeout waiting for %0d transactions", num_transactions))
                break;
            end
        end
        
        `uvm_info(get_type_name(), $sformatf("Completed waiting for %0d transactions", num_transactions), UVM_MEDIUM)
    endtask
    
    // Wait for all activity to settle
    virtual task wait_for_idle(realtime idle_time = 10us);
        `uvm_info(get_type_name(), $sformatf("Waiting for system to become idle for %0t", idle_time), UVM_MEDIUM)
        
        // Wait for interface to become idle
        fork
            begin
                wait (!vif.awvalid && !vif.wvalid && !vif.bvalid && 
                      !vif.arvalid && !vif.rvalid);
                #idle_time;
            end
            begin
                #(idle_time * 10); // Maximum wait time
            end
        join_any
        disable fork;
        
        `uvm_info(get_type_name(), "System idle detected", UVM_MEDIUM)
    endtask
    
    // Test result checking
    virtual function bit check_test_result();
        bit test_passed = 1;
        
        if (m_scoreboard != null) begin
            if (m_scoreboard.mismatched_transactions > 0 || 
                m_scoreboard.protocol_violations > 0 ||
                m_scoreboard.data_mismatches > 0 ||
                m_scoreboard.address_violations > 0 ||
                m_scoreboard.timing_violations > 0) begin
                test_passed = 0;
            end
        end
        
        return test_passed;
    endfunction
    
    // Final phase
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        
        // Check test results
        if (check_test_result()) begin
            tests_passed++;
            `uvm_info(get_type_name(), $sformatf("Test %s PASSED", test_name), UVM_LOW)
        end else begin
            tests_failed++;
            `uvm_error(get_type_name(), $sformatf("Test %s FAILED", test_name))
        end
        
        total_tests_run++;
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "=== AXI4 TEST ENVIRONMENT REPORT ===", UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Test Name: %s", test_name), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Total Tests Run: %0d", total_tests_run), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Tests Passed: %0d", tests_passed), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Tests Failed: %0d", tests_failed), UVM_LOW)
        
        if (total_tests_run > 0) begin
            real pass_rate = (real'(tests_passed) / real'(total_tests_run)) * 100.0;
            `uvm_info(get_type_name(), $sformatf("Pass Rate: %.1f%%", pass_rate), UVM_LOW)
        end
        
        `uvm_info(get_type_name(), "====================================", UVM_LOW)
    endfunction
    
endclass : axi4_test_env


//==============================================================================
// AXI4 Base Test - Base class for all AXI4 tests
//==============================================================================
class axi4_base_test extends uvm_test;
    
    // Factory registration
    `uvm_component_utils(axi4_base_test)
    
    // Test environment
    axi4_test_env m_env;
    
    // Virtual interface
    virtual axi4_if vif;
    
    // Test configuration
    string test_name = "axi4_base_test";
    int test_timeout = 1000000; // 1ms default timeout
    
    // Constructor
    function new(string name = "axi4_base_test", uvm_component parent = null);
        super.new(name, parent);
        test_name = name;
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Set test timeout
        uvm_top.set_timeout(test_timeout * 1ns);
        
        // Get virtual interface
        if (!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif)) begin
            `uvm_fatal("NOVIF", "Virtual interface must be set for: " + get_full_name())
        end
        
        // Create environment
        m_env = axi4_test_env::type_id::create("m_env", this);
        uvm_config_db#(virtual axi4_if)::set(this, "m_env", "vif", vif);
        uvm_config_db#(string)::set(this, "m_env", "test_name", test_name);
        
        `uvm_info(get_type_name(), $sformatf("Created base test: %s", test_name), UVM_MEDIUM)
    endfunction
    
    // End of elaboration phase
    virtual function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
    endfunction
    
    // Main test phase - override in derived tests
    virtual task main_phase(uvm_phase phase);
        `uvm_info(get_type_name(), $sformatf("Starting main phase of test: %s", test_name), UVM_MEDIUM)
        
        // Default: wait a bit and finish
        phase.raise_objection(this);
        #100us;
        phase.drop_objection(this);
        
        `uvm_info(get_type_name(), $sformatf("Completed main phase of test: %s", test_name), UVM_MEDIUM)
    endtask
    
    // Report test result
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        if (m_env.check_test_result()) begin
            `uvm_info(get_type_name(), $sformatf("*** TEST %s PASSED ***", test_name), UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), $sformatf("*** TEST %s FAILED ***", test_name))
        end
    endfunction
    
endclass : axi4_base_test


//==============================================================================
// AXI4 Basic Test - Simple functionality test
//==============================================================================
class axi4_basic_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_basic_test)
    
    function new(string name = "axi4_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual task main_phase(uvm_phase phase);
        axi4_basic_sequence basic_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting AXI4 Basic Test", UVM_LOW)
        
        // Configure environment
        m_env.configure_slave_memory();
        m_env.configure_slave_behavior(5, 1, 5, 1, 5); // 5% error rate, low latency
        
        // Create and run basic sequence
        basic_seq = axi4_basic_sequence::type_id::create("basic_seq");
        basic_seq.num_transactions = 50;
        
        m_env.run_master_sequence(basic_seq, "Basic Sequence");
        
        // Wait for all transactions to complete
        m_env.wait_for_transactions(50, 500us);
        m_env.wait_for_idle(20us);
        
        `uvm_info(get_type_name(), "Completed AXI4 Basic Test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_basic_test


//==============================================================================
// AXI4 Comprehensive Test - Tests multiple sequence types
//==============================================================================
class axi4_comprehensive_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_comprehensive_test)
    
    function new(string name = "axi4_comprehensive_test", uvm_component parent = null);
        super.new(name, parent);
        test_timeout = 5000000; // 5ms timeout for comprehensive test
    endfunction
    
    virtual task main_phase(uvm_phase phase);
        // Sequence instances
        axi4_basic_sequence basic_seq;
        axi4_burst_sequence burst_seq;
        axi4_wrap_sequence wrap_seq;
        axi4_exclusive_sequence exclusive_seq;
        axi4_qos_sequence qos_seq;
        axi4_security_sequence security_seq;
        axi4_error_sequence error_seq;
        axi4_stress_sequence stress_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting AXI4 Comprehensive Test", UVM_LOW)
        
        // Configure environment
        m_env.configure_slave_memory();
        m_env.configure_slave_behavior(3, 1, 8, 1, 8); // 3% error rate, moderate latency
        
        // Create all sequences
        basic_seq = axi4_basic_sequence::type_id::create("basic_seq");
        burst_seq = axi4_burst_sequence::type_id::create("burst_seq");
        wrap_seq = axi4_wrap_sequence::type_id::create("wrap_seq");
        exclusive_seq = axi4_exclusive_sequence::type_id::create("exclusive_seq");
        qos_seq = axi4_qos_sequence::type_id::create("qos_seq");
        security_seq = axi4_security_sequence::type_id::create("security_seq");
        error_seq = axi4_error_sequence::type_id::create("error_seq");
        stress_seq = axi4_stress_sequence::type_id::create("stress_seq");
        
        // Configure sequences
        basic_seq.num_transactions = 30;
        burst_seq.num_transactions = 20;
        stress_seq.num_transactions = 100;
        
        // Run sequences sequentially
        `uvm_info(get_type_name(), "Phase 1: Basic Transactions", UVM_MEDIUM)
        m_env.run_master_sequence(basic_seq, "Basic Sequence");
        m_env.wait_for_idle(10us);
        
        `uvm_info(get_type_name(), "Phase 2: Burst Transactions", UVM_MEDIUM)
        m_env.run_master_sequence(burst_seq, "Burst Sequence");
        m_env.wait_for_idle(10us);
        
        `uvm_info(get_type_name(), "Phase 3: WRAP Transactions", UVM_MEDIUM)
        m_env.run_master_sequence(wrap_seq, "WRAP Sequence");
        m_env.wait_for_idle(10us);
        
        `uvm_info(get_type_name(), "Phase 4: Exclusive Access", UVM_MEDIUM)
        m_env.run_master_sequence(exclusive_seq, "Exclusive Sequence");
        m_env.wait_for_idle(10us);
        
        `uvm_info(get_type_name(), "Phase 5: QoS Testing", UVM_MEDIUM)
        m_env.run_master_sequence(qos_seq, "QoS Sequence");
        m_env.wait_for_idle(10us);
        
        `uvm_info(get_type_name(), "Phase 6: Security Testing", UVM_MEDIUM)
        m_env.run_master_sequence(security_seq, "Security Sequence");
        m_env.wait_for_idle(10us);
        
        `uvm_info(get_type_name(), "Phase 7: Error Injection", UVM_MEDIUM)
        m_env.run_master_sequence(error_seq, "Error Sequence");
        m_env.wait_for_idle(10us);
        
        `uvm_info(get_type_name(), "Phase 8: Stress Testing", UVM_MEDIUM)
        m_env.run_master_sequence(stress_seq, "Stress Sequence");
        
        // Final wait
        m_env.wait_for_idle(50us);
        
        `uvm_info(get_type_name(), "Completed AXI4 Comprehensive Test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_comprehensive_test