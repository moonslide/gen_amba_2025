//==============================================================================
// AXI4 Master Driver - Drives transactions from sequencer to DUT interface
// Implements complete AXI4 protocol including all channels and timing
//==============================================================================

class axi4_master_driver extends uvm_driver #(axi4_transaction);
    
    // Factory registration
    `uvm_component_utils(axi4_master_driver)
    
    // Virtual interface handle
    virtual axi4_if.master vif;
    
    // Configuration and statistics
    int num_transactions;
    int num_write_transactions;
    int num_read_transactions;
    int total_wait_cycles;
    
    // Outstanding transaction tracking
    axi4_transaction outstanding_writes[$];
    axi4_transaction outstanding_reads[$];
    int max_outstanding_reads = 16;
    int max_outstanding_writes = 16;
    
    // Constructor
    function new(string name = "axi4_master_driver", uvm_component parent = null);
        super.new(name, parent);
        num_transactions = 0;
        num_write_transactions = 0;
        num_read_transactions = 0;
        total_wait_cycles = 0;
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi4_if.master)::get(this, "", "vif", vif)) begin
            `uvm_fatal("NOVIF", "Virtual interface must be set for: " + get_full_name())
        end
    endfunction
    
    // Run phase - main driver loop
    virtual task run_phase(uvm_phase phase);
        axi4_transaction req;
        
        // Initialize interface
        initialize_interface();
        
        // Wait for reset release
        wait_for_reset_release();
        
        // Main driver loop
        forever begin
            // Get transaction from sequencer
            seq_item_port.get_next_item(req);
            
            // Drive the transaction
            drive_transaction(req);
            
            // Signal completion
            seq_item_port.item_done();
            
            // Update statistics
            num_transactions++;
            if (req.trans_type == axi4_transaction::WRITE_TRANS) 
                num_write_transactions++;
            else 
                num_read_transactions++;
        end
    endtask
    
    // Initialize interface to safe state
    virtual task initialize_interface();
        `uvm_info(get_type_name(), "Initializing AXI4 Master interface", UVM_MEDIUM)
        
        vif.master_cb.awvalid <= 1'b0;
        vif.master_cb.awid <= '0;
        vif.master_cb.awaddr <= '0;
        vif.master_cb.awlen <= '0;
        vif.master_cb.awsize <= '0;
        vif.master_cb.awburst <= '0;
        vif.master_cb.awlock <= '0;
        vif.master_cb.awcache <= '0;
        vif.master_cb.awprot <= '0;
        vif.master_cb.awqos <= '0;
        vif.master_cb.awregion <= '0;
        vif.master_cb.awuser <= '0;
        
        vif.master_cb.wvalid <= 1'b0;
        vif.master_cb.wdata <= '0;
        vif.master_cb.wstrb <= '0;
        vif.master_cb.wlast <= 1'b0;
        vif.master_cb.wuser <= '0;
        
        vif.master_cb.bready <= 1'b0;
        
        vif.master_cb.arvalid <= 1'b0;
        vif.master_cb.arid <= '0;
        vif.master_cb.araddr <= '0;
        vif.master_cb.arlen <= '0;
        vif.master_cb.arsize <= '0;
        vif.master_cb.arburst <= '0;
        vif.master_cb.arlock <= '0;
        vif.master_cb.arcache <= '0;
        vif.master_cb.arprot <= '0;
        vif.master_cb.arqos <= '0;
        vif.master_cb.arregion <= '0;
        vif.master_cb.aruser <= '0;
        
        vif.master_cb.rready <= 1'b0;
        
        vif.master_cb.csysreq <= 1'b0;
    endtask
    
    // Wait for reset deassertion
    virtual task wait_for_reset_release();
        `uvm_info(get_type_name(), "Waiting for reset release", UVM_MEDIUM)
        wait (vif.aresetn === 1'b0);
        wait (vif.aresetn === 1'b1);
        repeat (2) @(vif.master_cb);
        `uvm_info(get_type_name(), "Reset released, driver ready", UVM_MEDIUM)
    endtask
    
    // Main transaction driver
    virtual task drive_transaction(axi4_transaction req);
        `uvm_info(get_type_name(), $sformatf("Driving transaction: %s", req.convert2string()), UVM_HIGH)
        
        // Check outstanding transaction limits
        if (req.trans_type == axi4_transaction::WRITE_TRANS) begin
            while (outstanding_writes.size() >= max_outstanding_writes) begin
                @(vif.master_cb);
            end
        end else begin
            while (outstanding_reads.size() >= max_outstanding_reads) begin
                @(vif.master_cb);
            end
        end
        
        // Fork parallel processes for different channels
        fork
            begin
                if (req.trans_type == axi4_transaction::WRITE_TRANS) begin
                    fork
                        drive_write_address(req);
                        drive_write_data(req);
                        monitor_write_response(req);
                    join
                end else begin
                    fork
                        drive_read_address(req);
                        monitor_read_data(req);
                    join
                end
            end
        join
        
        `uvm_info(get_type_name(), $sformatf("Transaction completed: %s", req.convert2string()), UVM_HIGH)
    endtask
    
    // Drive write address channel
    virtual task drive_write_address(axi4_transaction req);
        int wait_cycles = 0;
        
        // Add to outstanding list
        outstanding_writes.push_back(req);
        
        // Apply address delay
        repeat (req.addr_delay) @(vif.master_cb);
        
        // Drive address phase
        vif.master_cb.awid <= req.id;
        vif.master_cb.awaddr <= req.addr;
        vif.master_cb.awlen <= req.len;
        vif.master_cb.awsize <= req.size;
        vif.master_cb.awburst <= req.burst_type;
        vif.master_cb.awlock <= req.lock;
        vif.master_cb.awcache <= req.cache;
        vif.master_cb.awprot <= req.get_prot();
        vif.master_cb.awqos <= req.qos;
        vif.master_cb.awregion <= req.region;
        vif.master_cb.awuser <= req.user;
        vif.master_cb.awvalid <= 1'b1;
        
        // Wait for handshake
        do begin
            @(vif.master_cb);
            wait_cycles++;
        end while (!vif.master_cb.awready);
        
        // Clear valid
        vif.master_cb.awvalid <= 1'b0;
        
        total_wait_cycles += wait_cycles;
        `uvm_info(get_type_name(), $sformatf("Write address sent for ID=0x%0h, wait_cycles=%0d", req.id, wait_cycles), UVM_HIGH)
    endtask
    
    // Drive write data channel
    virtual task drive_write_data(axi4_transaction req);
        int beat;
        int wait_cycles;
        
        for (beat = 0; beat <= req.len; beat++) begin
            wait_cycles = 0;
            
            // Apply data delay for this beat
            repeat (req.data_delay[beat]) @(vif.master_cb);
            
            // Drive data
            vif.master_cb.wdata <= req.data[beat];
            vif.master_cb.wstrb <= req.strb[beat];
            vif.master_cb.wlast <= (beat == req.len);
            vif.master_cb.wuser <= req.wuser[beat];
            vif.master_cb.wvalid <= 1'b1;
            
            // Wait for handshake
            do begin
                @(vif.master_cb);
                wait_cycles++;
            end while (!vif.master_cb.wready);
            
            // Clear valid
            vif.master_cb.wvalid <= 1'b0;
            
            `uvm_info(get_type_name(), $sformatf("Write data beat %0d/%0d sent, data=0x%0h, wait_cycles=%0d", 
                                                 beat+1, req.len+1, req.data[beat], wait_cycles), UVM_HIGH)
        end
    endtask
    
    // Monitor write response channel
    virtual task monitor_write_response(axi4_transaction req);
        int wait_cycles = 0;
        bit found = 0;
        
        // Enable ready
        vif.master_cb.bready <= 1'b1;
        
        // Wait for response with matching ID
        while (!found) begin
            @(vif.master_cb);
            wait_cycles++;
            
            if (vif.master_cb.bvalid && vif.master_cb.bready) begin
                if (vif.master_cb.bid == req.id) begin
                    // Capture response
                    req.bresp = axi4_transaction::resp_type_e'(vif.master_cb.bresp);
                    req.buser = vif.master_cb.buser;
                    found = 1;
                    
                    `uvm_info(get_type_name(), $sformatf("Write response received for ID=0x%0h, resp=%s, wait_cycles=%0d", 
                                                         req.id, req.bresp.name(), wait_cycles), UVM_HIGH)
                end
            end
        end
        
        // Remove from outstanding list
        for (int i = 0; i < outstanding_writes.size(); i++) begin
            if (outstanding_writes[i].id == req.id) begin
                outstanding_writes.delete(i);
                break;
            end
        end
        
        // Disable ready (can be policy-dependent)
        @(vif.master_cb);
        vif.master_cb.bready <= 1'b0;
    endtask
    
    // Drive read address channel
    virtual task drive_read_address(axi4_transaction req);
        int wait_cycles = 0;
        
        // Add to outstanding list
        outstanding_reads.push_back(req);
        
        // Apply address delay
        repeat (req.addr_delay) @(vif.master_cb);
        
        // Drive address phase
        vif.master_cb.arid <= req.id;
        vif.master_cb.araddr <= req.addr;
        vif.master_cb.arlen <= req.len;
        vif.master_cb.arsize <= req.size;
        vif.master_cb.arburst <= req.burst_type;
        vif.master_cb.arlock <= req.lock;
        vif.master_cb.arcache <= req.cache;
        vif.master_cb.arprot <= req.get_prot();
        vif.master_cb.arqos <= req.qos;
        vif.master_cb.arregion <= req.region;
        vif.master_cb.aruser <= req.user;
        vif.master_cb.arvalid <= 1'b1;
        
        // Wait for handshake
        do begin
            @(vif.master_cb);
            wait_cycles++;
        end while (!vif.master_cb.arready);
        
        // Clear valid
        vif.master_cb.arvalid <= 1'b0;
        
        total_wait_cycles += wait_cycles;
        `uvm_info(get_type_name(), $sformatf("Read address sent for ID=0x%0h, wait_cycles=%0d", req.id, wait_cycles), UVM_HIGH)
    endtask
    
    // Monitor read data channel
    virtual task monitor_read_data(axi4_transaction req);
        int beat = 0;
        int wait_cycles = 0;
        bit found = 0;
        
        // Initialize response arrays
        req.rdata = new[req.len + 1];
        req.rresp = new[req.len + 1];
        req.ruser = new[req.len + 1];
        
        // Enable ready
        vif.master_cb.rready <= 1'b1;
        
        // Collect all data beats
        while (beat <= req.len) begin
            @(vif.master_cb);
            wait_cycles++;
            
            if (vif.master_cb.rvalid && vif.master_cb.rready) begin
                if (vif.master_cb.rid == req.id) begin
                    // Capture data
                    req.rdata[beat] = vif.master_cb.rdata;
                    req.rresp[beat] = axi4_transaction::resp_type_e'(vif.master_cb.rresp);
                    req.ruser[beat] = vif.master_cb.ruser;
                    
                    `uvm_info(get_type_name(), $sformatf("Read data beat %0d/%0d received, ID=0x%0h, data=0x%0h, resp=%s", 
                                                         beat+1, req.len+1, req.id, req.rdata[beat], req.rresp[beat].name()), UVM_HIGH)
                    
                    // Check for last beat
                    if (vif.master_cb.rlast) begin
                        if (beat == req.len) begin
                            found = 1;
                        end else begin
                            `uvm_error(get_type_name(), $sformatf("RLAST asserted at beat %0d, expected at beat %0d", beat, req.len))
                        end
                    end
                    
                    beat++;
                end
            end
        end
        
        if (!found) begin
            `uvm_error(get_type_name(), $sformatf("Read transaction incomplete, RLAST not received for ID=0x%0h", req.id))
        end
        
        // Remove from outstanding list
        for (int i = 0; i < outstanding_reads.size(); i++) begin
            if (outstanding_reads[i].id == req.id) begin
                outstanding_reads.delete(i);
                break;
            end
        end
        
        // Disable ready
        @(vif.master_cb);
        vif.master_cb.rready <= 1'b0;
        
        `uvm_info(get_type_name(), $sformatf("Read transaction completed for ID=0x%0h, total_wait_cycles=%0d", req.id, wait_cycles), UVM_HIGH)
    endtask
    
    // Report phase - print statistics
    virtual function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), $sformatf("Driver Statistics:"), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Total Transactions: %0d", num_transactions), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Write Transactions: %0d", num_write_transactions), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Read Transactions: %0d", num_read_transactions), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Total Wait Cycles: %0d", total_wait_cycles), UVM_LOW)
        if (num_transactions > 0) begin
            `uvm_info(get_type_name(), $sformatf("  Average Wait Cycles: %.2f", real'(total_wait_cycles)/real'(num_transactions)), UVM_LOW)
        end
    endfunction
    
endclass : axi4_master_driver