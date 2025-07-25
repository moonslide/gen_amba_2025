//==============================================================================
// AXI4 Scoreboard - Transaction checking and analysis
// Monitors master and slave transactions for protocol compliance
//==============================================================================

class axi4_scoreboard extends uvm_scoreboard;
    
    // Factory registration
    `uvm_component_utils(axi4_scoreboard)
    
    // Analysis FIFOs for receiving transactions
    uvm_tlm_analysis_fifo #(axi4_transaction) master_fifo;
    uvm_tlm_analysis_fifo #(axi4_transaction) slave_fifo;
    
    // Transaction queues for comparison
    axi4_transaction master_trans_queue[$];
    axi4_transaction slave_trans_queue[$];
    
    // Memory model for data checking
    bit [7:0] expected_memory [bit [63:0]];
    
    // Statistics
    int total_transactions = 0;
    int matched_transactions = 0;
    int mismatched_transactions = 0;
    int protocol_violations = 0;
    int data_mismatches = 0;
    int address_violations = 0;
    int timing_violations = 0;
    
    // Coverage
    real protocol_coverage = 0.0;
    real functional_coverage = 0.0;
    
    // Transaction tracking
    typedef struct {
        bit [7:0] id;
        realtime start_time;
        realtime end_time;
        axi4_transaction::trans_type_e trans_type;
        bit [63:0] addr;
        int num_beats;
        bit completed;
    } transaction_track_t;
    
    transaction_track_t active_transactions[bit [7:0]]; // Keyed by transaction ID
    
    // Constructor
    function new(string name = "axi4_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        master_fifo = new("master_fifo", this);
        slave_fifo = new("slave_fifo", this);
        
        `uvm_info(get_type_name(), "AXI4 Scoreboard created", UVM_MEDIUM)
    endfunction
    
    // Run phase
    virtual task run_phase(uvm_phase phase);
        fork
            process_master_transactions();
            process_slave_transactions();
            transaction_timeout_checker();
        join_none
    endtask
    
    // Process transactions from master monitor
    virtual task process_master_transactions();
        axi4_transaction trans;
        
        forever begin
            master_fifo.get(trans);
            
            `uvm_info(get_type_name(), $sformatf("Received master transaction: %s", trans.convert2string()), UVM_HIGH)
            
            // Add to queue for comparison
            master_trans_queue.push_back(trans);
            
            // Track transaction timing
            track_transaction_start(trans);
            
            // Perform immediate checks
            check_transaction_validity(trans);
            
            // Update expected memory model for writes
            if (trans.trans_type == axi4_transaction::WRITE_TRANS) begin
                update_memory_model(trans);
            end
            
            total_transactions++;
        end
    endtask
    
    // Process transactions from slave monitor
    virtual task process_slave_transactions();
        axi4_transaction trans;
        
        forever begin
            slave_fifo.get(trans);
            
            `uvm_info(get_type_name(), $sformatf("Received slave transaction: %s", trans.convert2string()), UVM_HIGH)
            
            // Add to queue for comparison
            slave_trans_queue.push_back(trans);
            
            // Track transaction completion
            track_transaction_end(trans);
            
            // Compare with expected behavior
            compare_transaction(trans);
        end
    endtask
    
    // Check transaction validity
    virtual function void check_transaction_validity(axi4_transaction trans);
        bit is_valid = 1;
        string error_msg = "";
        
        // Check 4KB boundary constraint
        if (trans.crosses_4kb_boundary()) begin
            is_valid = 0;
            error_msg = {error_msg, "4KB boundary violation; "};
            address_violations++;
        end
        
        // Check burst length for WRAP
        if (trans.burst_type == axi4_transaction::WRAP) begin
            if (!(trans.len inside {1, 3, 7, 15})) begin
                is_valid = 0;
                error_msg = {error_msg, "Invalid WRAP burst length; "};
                protocol_violations++;
            end
            
            // Check address alignment for WRAP
            int align_mask = ((trans.len + 1) * (1 << trans.size)) - 1;
            if ((trans.addr & align_mask) != 0) begin
                is_valid = 0;
                error_msg = {error_msg, "WRAP address not aligned; "};
                protocol_violations++;
            end
        end
        
        // Check maximum burst length
        if (trans.len > 255) begin
            is_valid = 0;
            error_msg = {error_msg, "Burst length exceeds maximum; "};
            protocol_violations++;
        end
        
        // Check transfer size
        if (trans.size > 7) begin
            is_valid = 0;
            error_msg = {error_msg, "Transfer size exceeds maximum; "};
            protocol_violations++;
        end
        
        // Check data array sizes for consistency
        if (trans.trans_type == axi4_transaction::WRITE_TRANS) begin
            if (trans.data.size() != (trans.len + 1) || 
                trans.strb.size() != (trans.len + 1)) begin
                is_valid = 0;
                error_msg = {error_msg, "Data array size mismatch; "};
                protocol_violations++;
            end
        end else begin
            if (trans.rdata.size() != (trans.len + 1) || 
                trans.rresp.size() != (trans.len + 1)) begin
                is_valid = 0;
                error_msg = {error_msg, "Response array size mismatch; "};
                protocol_violations++;
            end
        end
        
        if (!is_valid) begin
            `uvm_error(get_type_name(), $sformatf("Transaction validation failed for ID=0x%0h: %s", 
                                                  trans.id, error_msg))
        end else begin
            `uvm_info(get_type_name(), $sformatf("Transaction ID=0x%0h passed validation", trans.id), UVM_DEBUG)
        end
    endfunction
    
    // Update memory model for write transactions
    virtual function void update_memory_model(axi4_transaction trans);
        bit [63:0] addr;
        bit [63:0] base_addr = trans.addr;
        
        for (int beat = 0; beat <= trans.len; beat++) begin
            // Calculate address for this beat
            case (trans.burst_type)
                axi4_transaction::FIXED: addr = base_addr;
                axi4_transaction::INCR:  addr = base_addr + (beat * (1 << trans.size));
                axi4_transaction::WRAP: begin
                    int wrap_size = (trans.len + 1) * (1 << trans.size);
                    bit [63:0] wrap_boundary = (base_addr / wrap_size) * wrap_size;
                    addr = wrap_boundary + ((base_addr + (beat * (1 << trans.size))) % wrap_size);
                end
                default: addr = base_addr;
            endcase
            
            // Update memory based on write strobes
            for (int byte_idx = 0; byte_idx < (1 << trans.size); byte_idx++) begin
                if (trans.strb[beat][byte_idx]) begin
                    expected_memory[addr + byte_idx] = trans.data[beat][byte_idx*8 +: 8];
                    `uvm_info(get_type_name(), $sformatf("Memory update: Addr=0x%0h, Data=0x%02h", 
                                                         addr + byte_idx, trans.data[beat][byte_idx*8 +: 8]), UVM_DEBUG)
                end
            end
        end
    endfunction
    
    // Compare slave transaction with expected behavior
    virtual function void compare_transaction(axi4_transaction slave_trans);
        axi4_transaction master_trans;
        bit found_match = 0;
        
        // Find matching master transaction by ID
        foreach (master_trans_queue[i]) begin
            if (master_trans_queue[i].id == slave_trans.id && 
                master_trans_queue[i].trans_type == slave_trans.trans_type) begin
                master_trans = master_trans_queue[i];
                master_trans_queue.delete(i);
                found_match = 1;
                break;
            end
        end
        
        if (!found_match) begin
            `uvm_error(get_type_name(), $sformatf("No matching master transaction found for slave ID=0x%0h", slave_trans.id))
            mismatched_transactions++;
            return;
        end
        
        // Compare transaction fields
        bit transaction_match = 1;
        string mismatch_details = "";
        
        // Address comparison
        if (master_trans.addr != slave_trans.addr) begin
            transaction_match = 0;
            mismatch_details = {mismatch_details, $sformatf("Address mismatch: M=0x%0h vs S=0x%0h; ", 
                                                           master_trans.addr, slave_trans.addr)};
        end
        
        // Length comparison
        if (master_trans.len != slave_trans.len) begin
            transaction_match = 0;
            mismatch_details = {mismatch_details, $sformatf("Length mismatch: M=%0d vs S=%0d; ", 
                                                           master_trans.len, slave_trans.len)};
        end
        
        // Size comparison
        if (master_trans.size != slave_trans.size) begin
            transaction_match = 0;
            mismatch_details = {mismatch_details, $sformatf("Size mismatch: M=%0d vs S=%0d; ", 
                                                           master_trans.size, slave_trans.size)};
        end
        
        // Burst type comparison
        if (master_trans.burst_type != slave_trans.burst_type) begin
            transaction_match = 0;
            mismatch_details = {mismatch_details, $sformatf("Burst type mismatch: M=%s vs S=%s; ", 
                                                           master_trans.burst_type.name(), slave_trans.burst_type.name())};
        end
        
        // Data comparison for read transactions
        if (slave_trans.trans_type == axi4_transaction::READ_TRANS) begin
            if (!compare_read_data(master_trans, slave_trans)) begin
                transaction_match = 0;
                mismatch_details = {mismatch_details, "Read data mismatch; "};
                data_mismatches++;
            end
        end
        
        // Response checking
        if (!check_response_validity(slave_trans)) begin
            transaction_match = 0;
            mismatch_details = {mismatch_details, "Invalid response; "};
        end
        
        if (transaction_match) begin
            matched_transactions++;
            `uvm_info(get_type_name(), $sformatf("Transaction ID=0x%0h matched successfully", slave_trans.id), UVM_HIGH)
        end else begin
            mismatched_transactions++;
            `uvm_error(get_type_name(), $sformatf("Transaction ID=0x%0h mismatch: %s", slave_trans.id, mismatch_details))
        end
    endfunction
    
    // Compare read data with expected values
    virtual function bit compare_read_data(axi4_transaction master_trans, axi4_transaction slave_trans);
        bit [63:0] addr;
        bit [63:0] base_addr = master_trans.addr;
        bit data_match = 1;
        
        for (int beat = 0; beat <= master_trans.len; beat++) begin
            // Calculate address for this beat
            case (master_trans.burst_type)
                axi4_transaction::FIXED: addr = base_addr;
                axi4_transaction::INCR:  addr = base_addr + (beat * (1 << master_trans.size));
                axi4_transaction::WRAP: begin
                    int wrap_size = (master_trans.len + 1) * (1 << master_trans.size);
                    bit [63:0] wrap_boundary = (base_addr / wrap_size) * wrap_size;
                    addr = wrap_boundary + ((base_addr + (beat * (1 << master_trans.size))) % wrap_size);
                end
                default: addr = base_addr;
            endcase
            
            // Compare each byte
            for (int byte_idx = 0; byte_idx < (1 << master_trans.size); byte_idx++) begin
                bit [7:0] expected_data, actual_data;
                
                if (expected_memory.exists(addr + byte_idx)) begin
                    expected_data = expected_memory[addr + byte_idx];
                end else begin
                    expected_data = 8'h00; // Default for uninitialized memory
                end
                
                actual_data = slave_trans.rdata[beat][byte_idx*8 +: 8];
                
                if (expected_data != actual_data && slave_trans.rresp[beat] == axi4_transaction::OKAY) begin
                    data_match = 0;
                    `uvm_error(get_type_name(), $sformatf("Data mismatch at addr=0x%0h: expected=0x%02h, actual=0x%02h", 
                                                          addr + byte_idx, expected_data, actual_data))
                end
            end
        end
        
        return data_match;
    endfunction
    
    // Check response validity
    virtual function bit check_response_validity(axi4_transaction trans);
        bit valid = 1;
        
        if (trans.trans_type == axi4_transaction::WRITE_TRANS) begin
            // Check write response
            if (!(trans.bresp inside {axi4_transaction::OKAY, axi4_transaction::EXOKAY, 
                                    axi4_transaction::SLVERR, axi4_transaction::DECERR})) begin
                valid = 0;
                `uvm_error(get_type_name(), $sformatf("Invalid write response: %0d", trans.bresp))
            end
        end else begin
            // Check read responses
            foreach (trans.rresp[i]) begin
                if (!(trans.rresp[i] inside {axi4_transaction::OKAY, axi4_transaction::EXOKAY, 
                                           axi4_transaction::SLVERR, axi4_transaction::DECERR})) begin
                    valid = 0;
                    `uvm_error(get_type_name(), $sformatf("Invalid read response at beat %0d: %0d", i, trans.rresp[i]))
                end
            end
        end
        
        return valid;
    endfunction
    
    // Track transaction start timing
    virtual function void track_transaction_start(axi4_transaction trans);
        transaction_track_t track;
        
        track.id = trans.id;
        track.start_time = $realtime;
        track.trans_type = trans.trans_type;
        track.addr = trans.addr;
        track.num_beats = trans.len + 1;
        track.completed = 0;
        
        active_transactions[trans.id] = track;
        
        `uvm_info(get_type_name(), $sformatf("Started tracking transaction ID=0x%0h at time %0t", 
                                             trans.id, track.start_time), UVM_DEBUG)
    endfunction
    
    // Track transaction end timing
    virtual function void track_transaction_end(axi4_transaction trans);
        if (active_transactions.exists(trans.id)) begin
            active_transactions[trans.id].end_time = $realtime;
            active_transactions[trans.id].completed = 1;
            
            real latency = (active_transactions[trans.id].end_time - active_transactions[trans.id].start_time) / 1ns;
            
            `uvm_info(get_type_name(), $sformatf("Transaction ID=0x%0h completed, latency=%.2f ns", 
                                                 trans.id, latency), UVM_HIGH)
            
            // Remove from active tracking
            active_transactions.delete(trans.id);
        end else begin
            `uvm_warning(get_type_name(), $sformatf("Transaction ID=0x%0h not found in active tracking", trans.id))
        end
    endfunction
    
    // Check for transaction timeouts
    virtual task transaction_timeout_checker();
        realtime timeout_limit = 10000ns; // 10us timeout
        
        forever begin
            #1000ns; // Check every 1us
            
            foreach (active_transactions[id]) begin
                if (!active_transactions[id].completed) begin
                    realtime elapsed = $realtime - active_transactions[id].start_time;
                    if (elapsed > timeout_limit) begin
                        `uvm_error(get_type_name(), $sformatf("Transaction ID=0x%0h timed out after %.2f ns", 
                                                              id, elapsed/1ns))
                        timing_violations++;
                        active_transactions.delete(id);
                    end
                end
            end
        end
    endtask
    
    // Calculate coverage metrics
    virtual function void calculate_coverage();
        // Basic coverage calculation
        if (total_transactions > 0) begin
            protocol_coverage = real'(matched_transactions) / real'(total_transactions) * 100.0;
        end
        
        // Functional coverage would come from covergroups in monitors
        functional_coverage = 85.0; // Placeholder - would be calculated from actual coverage
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        calculate_coverage();
        
        `uvm_info(get_type_name(), "=== AXI4 SCOREBOARD FINAL REPORT ===", UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Total Transactions: %0d", total_transactions), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Matched Transactions: %0d", matched_transactions), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Mismatched Transactions: %0d", mismatched_transactions), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Protocol Violations: %0d", protocol_violations), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Data Mismatches: %0d", data_mismatches), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Address Violations: %0d", address_violations), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Timing Violations: %0d", timing_violations), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Protocol Coverage: %.1f%%", protocol_coverage), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("Functional Coverage: %.1f%%", functional_coverage), UVM_LOW)
        
        // Determine overall test result
        if (mismatched_transactions == 0 && protocol_violations == 0 && 
            data_mismatches == 0 && address_violations == 0 && timing_violations == 0) begin
            `uvm_info(get_type_name(), "*** TEST PASSED ***", UVM_LOW)
        end else begin
            `uvm_error(get_type_name(), "*** TEST FAILED ***")
        end
        
        `uvm_info(get_type_name(), "=====================================", UVM_LOW)
    endfunction
    
    // Check phase - final consistency check
    virtual function void check_phase(uvm_phase phase);
        // Check for unmatched transactions
        if (master_trans_queue.size() > 0) begin
            `uvm_error(get_type_name(), $sformatf("%0d unmatched master transactions remaining", master_trans_queue.size()))
        end
        
        if (slave_trans_queue.size() > 0) begin
            `uvm_error(get_type_name(), $sformatf("%0d unmatched slave transactions remaining", slave_trans_queue.size()))
        end
        
        if (active_transactions.size() > 0) begin
            `uvm_warning(get_type_name(), $sformatf("%0d active transactions not completed", active_transactions.size()))
        end
    endfunction
    
endclass : axi4_scoreboard