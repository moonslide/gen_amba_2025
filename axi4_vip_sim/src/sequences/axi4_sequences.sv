//==============================================================================
// AXI4 Test Sequences - Collection of reusable sequence classes
// Includes basic, burst, exclusive, and stress test sequences
//==============================================================================

//==============================================================================
// Base AXI4 Sequence - Common functionality for all sequences
//==============================================================================
class axi4_base_sequence extends uvm_sequence #(axi4_transaction);
    
    `uvm_object_utils(axi4_base_sequence)
    
    // Configuration parameters
    int num_transactions = 10;
    bit [63:0] addr_min = 64'h1000_0000;
    bit [63:0] addr_max = 64'h1FFF_FFFF;
    int max_outstanding = 4;
    
    // Statistics
    int transactions_sent = 0;
    int write_transactions = 0;
    int read_transactions = 0;
    
    function new(string name = "axi4_base_sequence");
        super.new(name);
    endfunction
    
    // Pre-body setup
    virtual task pre_body();
        `uvm_info(get_type_name(), $sformatf("Starting sequence %s with %0d transactions", 
                                             get_name(), num_transactions), UVM_MEDIUM)
        transactions_sent = 0;
        write_transactions = 0;
        read_transactions = 0;
    endtask
    
    // Post-body cleanup and reporting
    virtual task post_body();
        `uvm_info(get_type_name(), $sformatf("Sequence %s completed: %0d total, %0d writes, %0d reads", 
                                             get_name(), transactions_sent, write_transactions, read_transactions), UVM_MEDIUM)
    endtask
    
    // Utility function to create and randomize transaction
    virtual function axi4_transaction create_transaction(string name = "trans");
        axi4_transaction trans;
        trans = axi4_transaction::type_id::create(name);
        
        if (!trans.randomize() with {
            addr >= addr_min;
            addr <= addr_max;
        }) begin
            `uvm_error(get_type_name(), "Failed to randomize transaction")
        end
        
        return trans;
    endfunction
    
    // Update statistics
    virtual function void update_stats(axi4_transaction trans);
        transactions_sent++;
        if (trans.trans_type == axi4_transaction::WRITE_TRANS) 
            write_transactions++;
        else 
            read_transactions++;
    endfunction
    
endclass : axi4_base_sequence


//==============================================================================
// Basic AXI4 Sequence - Single transactions with simple patterns
//==============================================================================
class axi4_basic_sequence extends axi4_base_sequence;
    
    `uvm_object_utils(axi4_basic_sequence)
    
    function new(string name = "axi4_basic_sequence");
        super.new(name);
        num_transactions = 20;
    endfunction
    
    virtual task body();
        axi4_transaction trans;
        
        repeat (num_transactions) begin
            trans = create_transaction("basic_trans");
            
            // Force basic transaction characteristics
            assert(trans.randomize() with {
                len inside {[0:7]};        // Short bursts
                size inside {[0:3]};       // Up to 8 bytes
                burst_type dist {axi4_transaction::INCR := 70, 
                               axi4_transaction::FIXED := 20, 
                               axi4_transaction::WRAP := 10};
                inject_addr_error == 0;
                inject_data_error == 0;
                inject_4kb_violation == 0;
            });
            
            start_item(trans);
            finish_item(trans);
            
            update_stats(trans);
            
            `uvm_info(get_type_name(), $sformatf("Sent basic transaction %0d: %s", 
                                                 transactions_sent, trans.convert2string()), UVM_HIGH)
        end
    endtask
    
endclass : axi4_basic_sequence


//==============================================================================
// Burst AXI4 Sequence - Long burst transactions
//==============================================================================
class axi4_burst_sequence extends axi4_base_sequence;
    
    `uvm_object_utils(axi4_burst_sequence)
    
    function new(string name = "axi4_burst_sequence");
        super.new(name);
        num_transactions = 15;
    endfunction
    
    virtual task body();
        axi4_transaction trans;
        
        repeat (num_transactions) begin
            trans = create_transaction("burst_trans");
            
            // Force burst characteristics
            assert(trans.randomize() with {
                len inside {[8:255]};      // Long bursts
                size inside {[2:6]};       // 4-64 byte transfers
                burst_type dist {axi4_transaction::INCR := 80, 
                               axi4_transaction::WRAP := 20};
                inject_addr_error == 0;
                inject_data_error == 0;
                inject_4kb_violation == 0;
            });
            
            start_item(trans);
            finish_item(trans);
            
            update_stats(trans);
            
            `uvm_info(get_type_name(), $sformatf("Sent burst transaction %0d: %s", 
                                                 transactions_sent, trans.convert2string()), UVM_HIGH)
        end
    endtask
    
endclass : axi4_burst_sequence


//==============================================================================
// WRAP Burst Sequence - Focused on WRAP burst testing
//==============================================================================
class axi4_wrap_sequence extends axi4_base_sequence;
    
    `uvm_object_utils(axi4_wrap_sequence)
    
    function new(string name = "axi4_wrap_sequence");
        super.new(name);
        num_transactions = 12;
    endfunction
    
    virtual task body();
        axi4_transaction trans;
        int wrap_lengths[] = {1, 3, 7, 15}; // 2, 4, 8, 16 transfers
        int sizes[] = {0, 1, 2, 3, 4, 5, 6}; // 1-64 bytes
        
        // Test all combinations of WRAP lengths and sizes
        foreach (wrap_lengths[i]) begin
            foreach (sizes[j]) begin
                trans = create_transaction("wrap_trans");
                
                assert(trans.randomize() with {
                    burst_type == axi4_transaction::WRAP;
                    len == wrap_lengths[i];
                    size == sizes[j];
                    // Ensure address alignment for WRAP
                    (addr % ((len + 1) * (1 << size))) == 0;
                    inject_4kb_violation == 0;
                });
                
                start_item(trans);
                finish_item(trans);
                
                update_stats(trans);
                
                `uvm_info(get_type_name(), $sformatf("Sent WRAP transaction %0d: len=%0d, size=%0d, addr=0x%0h", 
                                                     transactions_sent, trans.len+1, 1<<trans.size, trans.addr), UVM_HIGH)
            end
        end
    endtask
    
endclass : axi4_wrap_sequence


//==============================================================================
// Exclusive Access Sequence - Tests exclusive transactions
//==============================================================================
class axi4_exclusive_sequence extends axi4_base_sequence;
    
    `uvm_object_utils(axi4_exclusive_sequence)
    
    function new(string name = "axi4_exclusive_sequence");
        super.new(name);
        num_transactions = 8;
    endfunction
    
    virtual task body();
        axi4_transaction trans;
        bit [63:0] exclusive_addr;
        
        // Test exclusive access pairs
        for (int i = 0; i < num_transactions/2; i++) begin
            // Generate exclusive address
            exclusive_addr = addr_min + (i * 64); // 64-byte aligned
            
            // Exclusive read
            trans = create_transaction("exclusive_read");
            assert(trans.randomize() with {
                trans_type == axi4_transaction::READ_TRANS;
                exclusive_access == 1;
                addr == exclusive_addr;
                len inside {[0:3]};        // Short for exclusive
                size inside {[2:3]};       // 4 or 8 bytes
                burst_type == axi4_transaction::INCR;
            });
            
            start_item(trans);
            finish_item(trans);
            update_stats(trans);
            
            `uvm_info(get_type_name(), $sformatf("Sent exclusive read %0d at 0x%0h", 
                                                 i+1, exclusive_addr), UVM_HIGH)
            
            // Small delay between exclusive read and write
            repeat ($urandom_range(1, 5)) @(p_sequencer.aclk);
            
            // Exclusive write to same address
            trans = create_transaction("exclusive_write");
            assert(trans.randomize() with {
                trans_type == axi4_transaction::WRITE_TRANS;
                exclusive_access == 1;
                addr == exclusive_addr;
                len inside {[0:3]};        // Same length as read
                size inside {[2:3]};       // Same size as read
                burst_type == axi4_transaction::INCR;
            });
            
            start_item(trans);
            finish_item(trans);
            update_stats(trans);
            
            `uvm_info(get_type_name(), $sformatf("Sent exclusive write %0d at 0x%0h", 
                                                 i+1, exclusive_addr), UVM_HIGH)
        end
    endtask
    
endclass : axi4_exclusive_sequence


//==============================================================================
// QoS Sequence - Tests different Quality of Service levels
//==============================================================================
class axi4_qos_sequence extends axi4_base_sequence;
    
    `uvm_object_utils(axi4_qos_sequence)
    
    function new(string name = "axi4_qos_sequence");
        super.new(name);
        num_transactions = 16;
    endfunction
    
    virtual task body();
        axi4_transaction trans;
        int qos_levels[] = {0, 3, 7, 11, 15}; // Low to critical priority
        
        // Test each QoS level
        foreach (qos_levels[i]) begin
            repeat (3) begin // 3 transactions per QoS level
                trans = create_transaction("qos_trans");
                
                assert(trans.randomize() with {
                    qos == qos_levels[i];
                    len inside {[0:15]};
                    size inside {[0:4]};
                });
                
                start_item(trans);
                finish_item(trans);
                
                update_stats(trans);
                
                `uvm_info(get_type_name(), $sformatf("Sent QoS=%0d transaction %0d: %s", 
                                                     qos_levels[i], transactions_sent, trans.convert2string()), UVM_HIGH)
            end
        end
    endtask
    
endclass : axi4_qos_sequence


//==============================================================================
// Security Sequence - Tests different protection types
//==============================================================================
class axi4_security_sequence extends axi4_base_sequence;
    
    `uvm_object_utils(axi4_security_sequence)
    
    function new(string name = "axi4_security_sequence");
        super.new(name);
        num_transactions = 16;
    endfunction
    
    virtual task body();
        axi4_transaction trans;
        
        // Test all protection combinations
        for (int priv = 0; priv <= 1; priv++) begin
            for (int sec = 0; sec <= 1; sec++) begin
                for (int inst = 0; inst <= 1; inst++) begin
                    repeat (2) begin
                        trans = create_transaction("security_trans");
                        
                        assert(trans.randomize() with {
                            privilege == axi4_transaction::privilege_e'(priv);
                            security == axi4_transaction::security_e'(sec);
                            access_type == axi4_transaction::access_type_e'(inst);
                            len inside {[0:7]};
                            size inside {[0:3]};
                        });
                        
                        start_item(trans);
                        finish_item(trans);
                        
                        update_stats(trans);
                        
                        `uvm_info(get_type_name(), $sformatf("Sent security transaction %0d: PROT=3'b%b%b%b", 
                                                             transactions_sent, inst, sec, priv), UVM_HIGH)
                    end
                end
            end
        end
    endtask
    
endclass : axi4_security_sequence


//==============================================================================
// Error Injection Sequence - Tests error conditions
//==============================================================================
class axi4_error_sequence extends axi4_base_sequence;
    
    `uvm_object_utils(axi4_error_sequence)
    
    function new(string name = "axi4_error_sequence");
        super.new(name);
        num_transactions = 6;
    endfunction
    
    virtual task body();
        axi4_transaction trans;
        
        // 4KB boundary violation test
        repeat (2) begin
            trans = create_transaction("4kb_error_trans");
            assert(trans.randomize() with {
                inject_4kb_violation == 1;
                len inside {[4:15]};
                size inside {[2:4]};
            });
            
            start_item(trans);
            finish_item(trans);
            update_stats(trans);
            
            `uvm_info(get_type_name(), $sformatf("Sent 4KB violation transaction %0d", transactions_sent), UVM_HIGH)
        end
        
        // Address error injection
        repeat (2) begin
            trans = create_transaction("addr_error_trans");
            assert(trans.randomize() with {
                inject_addr_error == 1;
                len inside {[0:7]};
            });
            
            start_item(trans);
            finish_item(trans);
            update_stats(trans);
            
            `uvm_info(get_type_name(), $sformatf("Sent address error transaction %0d", transactions_sent), UVM_HIGH)
        end
        
        // Data error injection  
        repeat (2) begin
            trans = create_transaction("data_error_trans");
            assert(trans.randomize() with {
                trans_type == axi4_transaction::WRITE_TRANS;
                inject_data_error == 1;
                len inside {[0:7]};
            });
            
            start_item(trans);
            finish_item(trans);
            update_stats(trans);
            
            `uvm_info(get_type_name(), $sformatf("Sent data error transaction %0d", transactions_sent), UVM_HIGH)
        end
    endtask
    
endclass : axi4_error_sequence


//==============================================================================
// Stress Test Sequence - High-throughput random transactions
//==============================================================================
class axi4_stress_sequence extends axi4_base_sequence;
    
    `uvm_object_utils(axi4_stress_sequence)
    
    function new(string name = "axi4_stress_sequence");
        super.new(name);
        num_transactions = 200;
    endfunction
    
    virtual task body();
        axi4_transaction trans;
        
        repeat (num_transactions) begin
            trans = create_transaction("stress_trans");
            
            // Completely randomized with high variability
            assert(trans.randomize() with {
                len inside {[0:255]};
                size inside {[0:6]};
                burst_type dist {axi4_transaction::INCR := 60, 
                               axi4_transaction::FIXED := 20, 
                               axi4_transaction::WRAP := 20};
                qos inside {[0:15]};
                region inside {[0:15]};
                // Lower error injection rate for stress testing
                inject_addr_error dist {0 := 98, 1 := 2};
                inject_data_error dist {0 := 98, 1 := 2};
                inject_4kb_violation dist {0 := 99, 1 := 1};
            });
            
            start_item(trans);
            finish_item(trans);
            
            update_stats(trans);
            
            // Random delay between transactions
            if ($urandom_range(1, 100) <= 10) begin // 10% chance of delay
                repeat ($urandom_range(1, 10)) @(p_sequencer.aclk);
            end
            
            if (transactions_sent % 50 == 0) begin
                `uvm_info(get_type_name(), $sformatf("Stress test progress: %0d/%0d transactions", 
                                                     transactions_sent, num_transactions), UVM_MEDIUM)
            end
        end
    endtask
    
endclass : axi4_stress_sequence


//==============================================================================
// Outstanding Transaction Sequence - Tests multiple outstanding transactions
//==============================================================================
class axi4_outstanding_sequence extends axi4_base_sequence;
    
    `uvm_object_utils(axi4_outstanding_sequence)
    
    function new(string name = "axi4_outstanding_sequence");
        super.new(name);
        num_transactions = 32;
        max_outstanding = 8;
    endfunction
    
    virtual task body();
        axi4_transaction trans_queue[$];
        int outstanding_count = 0;
        
        // Launch transactions with different IDs
        for (int i = 0; i < num_transactions; i++) begin
            trans_queue.push_back(create_transaction($sformatf("outstanding_trans_%0d", i)));
            
            assert(trans_queue[$].randomize() with {
                id == (i % 16); // Cycle through IDs
                len inside {[0:15]};
                size inside {[0:3]};
            });
        end
        
        // Send all transactions with controlled outstanding limit
        foreach (trans_queue[i]) begin
            // Wait if too many outstanding
            while (outstanding_count >= max_outstanding) begin
                @(p_sequencer.aclk);
                outstanding_count--; // Simulate completion (simplified)
            end
            
            start_item(trans_queue[i]);
            finish_item(trans_queue[i]);
            
            outstanding_count++;
            update_stats(trans_queue[i]);
            
            `uvm_info(get_type_name(), $sformatf("Sent outstanding transaction %0d, ID=0x%0h, outstanding=%0d", 
                                                 transactions_sent, trans_queue[i].id, outstanding_count), UVM_HIGH)
        end
        
        // Wait for all to complete
        repeat (100) @(p_sequencer.aclk);
    endtask
    
endclass : axi4_outstanding_sequence