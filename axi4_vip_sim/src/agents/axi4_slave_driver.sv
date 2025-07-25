//==============================================================================
// AXI4 Slave Driver - Responds to master transactions with configurable behavior
// Implements memory model with security checking and error injection
//==============================================================================

class axi4_slave_driver extends uvm_driver #(axi4_transaction);
    
    // Factory registration
    `uvm_component_utils(axi4_slave_driver)
    
    // Virtual interface handle
    virtual axi4_if.slave vif;
    
    // Memory model - associative array for sparse memory
    bit [7:0] memory [bit [63:0]];
    
    // Address range configuration
    bit [63:0] base_address = 64'h1000_0000;
    bit [63:0] size_bytes = 64'h1000_0000;  // 256MB default
    
    // Response configuration
    int read_latency_min = 1;
    int read_latency_max = 10;
    int write_latency_min = 1;
    int write_latency_max = 10;
    
    // Error injection configuration
    int error_rate_percent = 5;  // 5% error rate
    bit enable_security_check = 1;
    
    // Outstanding transaction tracking
    typedef struct {
        bit [7:0] id;
        bit [63:0] addr;
        bit [7:0] len;
        bit [2:0] size;
        bit [1:0] burst;
        bit [2:0] prot;
        int remaining_beats;
        bit [63:0] next_addr;
        int response_delay;
    } outstanding_trans_t;
    
    outstanding_trans_t outstanding_reads[$];
    outstanding_trans_t outstanding_writes[$];
    
    // Statistics
    int num_read_trans = 0;
    int num_write_trans = 0;
    int num_error_responses = 0;
    int num_security_violations = 0;
    
    // Constructor
    function new(string name = "axi4_slave_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi4_if.slave)::get(this, "", "vif", vif)) begin
            `uvm_fatal("NOVIF", "Virtual interface must be set for: " + get_full_name())
        end
        
        // Get configuration if available
        uvm_config_db#(bit [63:0])::get(this, "", "base_address", base_address);
        uvm_config_db#(bit [63:0])::get(this, "", "size_bytes", size_bytes);
        uvm_config_db#(int)::get(this, "", "error_rate_percent", error_rate_percent);
    endfunction
    
    // Run phase - main slave loop
    virtual task run_phase(uvm_phase phase);
        // Initialize interface
        initialize_interface();
        
        // Wait for reset release
        wait_for_reset_release();
        
        // Fork parallel processes for all channels
        fork
            handle_write_address_channel();
            handle_write_data_channel();
            handle_read_address_channel();
            handle_read_data_channel();
        join_none
        
        // Keep alive
        wait fork;
    endtask
    
    // Initialize interface to safe state
    virtual task initialize_interface();
        `uvm_info(get_type_name(), "Initializing AXI4 Slave interface", UVM_MEDIUM)
        
        vif.slave_cb.awready <= 1'b0;
        vif.slave_cb.wready <= 1'b0;
        vif.slave_cb.bvalid <= 1'b0;
        vif.slave_cb.bid <= '0;
        vif.slave_cb.bresp <= '0;
        vif.slave_cb.buser <= '0;
        
        vif.slave_cb.arready <= 1'b0;
        vif.slave_cb.rvalid <= 1'b0;
        vif.slave_cb.rid <= '0;
        vif.slave_cb.rdata <= '0;
        vif.slave_cb.rresp <= '0;
        vif.slave_cb.rlast <= 1'b0;
        vif.slave_cb.ruser <= '0;
        
        vif.slave_cb.csysack <= 1'b0;
        vif.slave_cb.cactive <= 1'b1;
    endtask
    
    // Wait for reset deassertion
    virtual task wait_for_reset_release();
        `uvm_info(get_type_name(), "Waiting for reset release", UVM_MEDIUM)
        wait (vif.aresetn === 1'b0);
        wait (vif.aresetn === 1'b1);
        repeat (2) @(vif.slave_cb);
        `uvm_info(get_type_name(), "Reset released, slave ready", UVM_MEDIUM)
    endtask
    
    // Handle write address channel
    virtual task handle_write_address_channel();
        outstanding_trans_t trans;
        int ready_delay;
        
        forever begin
            // Randomize ready delay (backpressure)
            ready_delay = $urandom_range(0, 3);
            repeat (ready_delay) @(vif.slave_cb);
            
            // Assert ready
            vif.slave_cb.awready <= 1'b1;
            @(vif.slave_cb);
            
            // Check for valid transaction
            if (vif.slave_cb.awvalid && vif.slave_cb.awready) begin
                // Capture transaction
                trans.id = vif.slave_cb.awid;
                trans.addr = vif.slave_cb.awaddr;
                trans.len = vif.slave_cb.awlen;
                trans.size = vif.slave_cb.awsize;
                trans.burst = vif.slave_cb.awburst;
                trans.prot = vif.slave_cb.awprot;
                trans.remaining_beats = vif.slave_cb.awlen + 1;
                trans.next_addr = vif.slave_cb.awaddr;
                trans.response_delay = $urandom_range(write_latency_min, write_latency_max);
                
                // Add to outstanding queue
                outstanding_writes.push_back(trans);
                num_write_trans++;
                
                `uvm_info(get_type_name(), $sformatf("Write address accepted: ID=0x%0h, Addr=0x%0h, Len=%0d", 
                                                     trans.id, trans.addr, trans.len+1), UVM_HIGH)
                
                // Check address range
                if (!is_address_in_range(trans.addr)) begin
                    `uvm_warning(get_type_name(), $sformatf("Write address 0x%0h out of range [0x%0h:0x%0h]", 
                                                           trans.addr, base_address, base_address + size_bytes - 1))
                end
            end
            
            // Deassert ready
            vif.slave_cb.awready <= 1'b0;
        end
    endtask
    
    // Handle write data channel
    virtual task handle_write_data_channel();
        outstanding_trans_t trans;
        int ready_delay;
        bit [63:0] write_addr;
        bit [7:0] write_data;
        int beat_count;
        
        forever begin
            // Wait for data if we have outstanding write address
            if (outstanding_writes.size() > 0) begin
                // Randomize ready delay
                ready_delay = $urandom_range(0, 2);
                repeat (ready_delay) @(vif.slave_cb);
                
                // Assert ready
                vif.slave_cb.wready <= 1'b1;
                @(vif.slave_cb);
                
                // Check for valid data
                if (vif.slave_cb.wvalid && vif.slave_cb.wready) begin
                    // Find matching write transaction (simple FIFO order for now)
                    trans = outstanding_writes[0];
                    
                    // Calculate write address for this beat
                    beat_count = (trans.len + 1) - trans.remaining_beats;
                    write_addr = calculate_beat_address(trans.next_addr, trans.burst, trans.size, beat_count);
                    
                    // Write data to memory (byte by byte based on strobe)
                    for (int byte_idx = 0; byte_idx < (1 << trans.size); byte_idx++) begin
                        if (vif.slave_cb.wstrb[byte_idx]) begin
                            write_data = vif.slave_cb.wdata[byte_idx*8 +: 8];
                            memory[write_addr + byte_idx] = write_data;
                            
                            `uvm_info(get_type_name(), $sformatf("Memory write: Addr=0x%0h, Data=0x%02h", 
                                                                 write_addr + byte_idx, write_data), UVM_DEBUG)
                        end
                    end
                    
                    // Update transaction state
                    trans.remaining_beats--;
                    trans.next_addr = get_next_address(trans.next_addr, trans.burst, trans.size);
                    outstanding_writes[0] = trans;
                    
                    `uvm_info(get_type_name(), $sformatf("Write data beat received: ID=0x%0h, Addr=0x%0h, Remaining=%0d", 
                                                         trans.id, write_addr, trans.remaining_beats), UVM_HIGH)
                    
                    // If last beat, prepare response
                    if (vif.slave_cb.wlast) begin
                        if (trans.remaining_beats == 0) begin
                            fork
                                send_write_response(outstanding_writes.pop_front());
                            join_none
                        end else begin
                            `uvm_error(get_type_name(), $sformatf("WLAST asserted with %0d beats remaining", trans.remaining_beats))
                        end
                    end
                end
                
                // Deassert ready
                vif.slave_cb.wready <= 1'b0;
            end else begin
                @(vif.slave_cb);
            end
        end
    endtask
    
    // Send write response
    virtual task send_write_response(outstanding_trans_t trans);
        bit [1:0] response;
        
        // Apply response delay
        repeat (trans.response_delay) @(vif.slave_cb);
        
        // Determine response based on address and security
        response = get_write_response(trans.addr, trans.prot);
        
        // Drive response
        vif.slave_cb.bid <= trans.id;
        vif.slave_cb.bresp <= response;
        vif.slave_cb.buser <= '0;
        vif.slave_cb.bvalid <= 1'b1;
        
        // Wait for ready
        do begin
            @(vif.slave_cb);
        end while (!vif.slave_cb.bready);
        
        // Clear valid
        vif.slave_cb.bvalid <= 1'b0;
        
        `uvm_info(get_type_name(), $sformatf("Write response sent: ID=0x%0h, BRESP=%s", 
                                             trans.id, get_response_name(response)), UVM_HIGH)
    endtask
    
    // Handle read address channel
    virtual task handle_read_address_channel();
        outstanding_trans_t trans;
        int ready_delay;
        
        forever begin
            // Randomize ready delay
            ready_delay = $urandom_range(0, 3);
            repeat (ready_delay) @(vif.slave_cb);
            
            // Assert ready
            vif.slave_cb.arready <= 1'b1;
            @(vif.slave_cb);
            
            // Check for valid transaction
            if (vif.slave_cb.arvalid && vif.slave_cb.arready) begin
                // Capture transaction
                trans.id = vif.slave_cb.arid;
                trans.addr = vif.slave_cb.araddr;
                trans.len = vif.slave_cb.arlen;
                trans.size = vif.slave_cb.arsize;
                trans.burst = vif.slave_cb.arburst;
                trans.prot = vif.slave_cb.arprot;
                trans.remaining_beats = vif.slave_cb.arlen + 1;
                trans.next_addr = vif.slave_cb.araddr;
                trans.response_delay = $urandom_range(read_latency_min, read_latency_max);
                
                // Add to outstanding queue
                outstanding_reads.push_back(trans);
                num_read_trans++;
                
                `uvm_info(get_type_name(), $sformatf("Read address accepted: ID=0x%0h, Addr=0x%0h, Len=%0d", 
                                                     trans.id, trans.addr, trans.len+1), UVM_HIGH)
                
                // Start read data response
                fork
                    send_read_data(outstanding_reads[$]);
                join_none
            end
            
            // Deassert ready
            vif.slave_cb.arready <= 1'b0;
        end
    endtask
    
    // Handle read data channel (just monitor ready)
    virtual task handle_read_data_channel();
        // This task can be used to monitor rready and adjust timing
        forever begin
            @(vif.slave_cb);
            // Could implement ready-based flow control here
        end
    endtask
    
    // Send read data response
    virtual task send_read_data(outstanding_trans_t trans);
        bit [63:0] read_addr;
        bit [511:0] read_data;  // Max AXI4 data width
        bit [1:0] response;
        int valid_delay;
        
        // Apply initial response delay
        repeat (trans.response_delay) @(vif.slave_cb);
        
        // Send all data beats
        for (int beat = 0; beat <= trans.len; beat++) begin
            // Calculate address for this beat
            read_addr = calculate_beat_address(trans.addr, trans.burst, trans.size, beat);
            
            // Read data from memory
            read_data = '0;
            for (int byte_idx = 0; byte_idx < (1 << trans.size); byte_idx++) begin
                if (memory.exists(read_addr + byte_idx)) begin
                    read_data[byte_idx*8 +: 8] = memory[read_addr + byte_idx];
                end else begin
                    read_data[byte_idx*8 +: 8] = $urandom();  // Uninitialized memory
                end
            end
            
            // Determine response
            response = get_read_response(read_addr, trans.prot);
            
            // Random valid delay between beats
            valid_delay = $urandom_range(0, 2);
            repeat (valid_delay) @(vif.slave_cb);
            
            // Drive read data
            vif.slave_cb.rid <= trans.id;
            vif.slave_cb.rdata <= read_data;
            vif.slave_cb.rresp <= response;
            vif.slave_cb.rlast <= (beat == trans.len);
            vif.slave_cb.ruser <= '0;
            vif.slave_cb.rvalid <= 1'b1;
            
            // Wait for ready
            do begin
                @(vif.slave_cb);
            end while (!vif.slave_cb.rready);
            
            // Clear valid
            vif.slave_cb.rvalid <= 1'b0;
            
            `uvm_info(get_type_name(), $sformatf("Read data beat %0d/%0d sent: ID=0x%0h, Addr=0x%0h, Data=0x%0h, RRESP=%s", 
                                                 beat+1, trans.len+1, trans.id, read_addr, read_data, get_response_name(response)), UVM_HIGH)
        end
        
        // Remove from outstanding queue
        for (int i = 0; i < outstanding_reads.size(); i++) begin
            if (outstanding_reads[i].id == trans.id) begin
                outstanding_reads.delete(i);
                break;
            end
        end
    endtask
    
    // Utility functions
    function bit is_address_in_range(bit [63:0] addr);
        return (addr >= base_address) && (addr < (base_address + size_bytes));
    endfunction
    
    function bit [63:0] calculate_beat_address(bit [63:0] start_addr, bit [1:0] burst_type, bit [2:0] size, int beat);
        bit [63:0] addr = start_addr;
        case (burst_type)
            2'b00: addr = start_addr; // FIXED
            2'b01: addr = start_addr + (beat * (1 << size)); // INCR
            2'b10: begin // WRAP
                bit [63:0] wrap_boundary = (start_addr / ((1 << size) * beat)) * ((1 << size) * beat);
                addr = wrap_boundary + ((start_addr + (beat * (1 << size))) % ((1 << size) * beat));
            end
            default: addr = start_addr;
        endcase
        return addr;
    endfunction
    
    function bit [63:0] get_next_address(bit [63:0] current_addr, bit [1:0] burst_type, bit [2:0] size);
        case (burst_type)
            2'b00: return current_addr; // FIXED
            2'b01: return current_addr + (1 << size); // INCR
            default: return current_addr + (1 << size);
        endcase
    endfunction
    
    function bit [1:0] get_write_response(bit [63:0] addr, bit [2:0] prot);
        // Check address range
        if (!is_address_in_range(addr)) begin
            num_error_responses++;
            return 2'b11; // DECERR
        end
        
        // Security check
        if (enable_security_check && (prot[1] == 0) && (addr >= base_address + size_bytes/2)) begin
            num_security_violations++;
            `uvm_warning(get_type_name(), $sformatf("Security violation: Non-secure access to secure region at 0x%0h", addr))
            return 2'b10; // SLVERR
        end
        
        // Random error injection
        if ($urandom_range(1, 100) <= error_rate_percent) begin
            num_error_responses++;
            return 2'b10; // SLVERR
        end
        
        return 2'b00; // OKAY
    endfunction
    
    function bit [1:0] get_read_response(bit [63:0] addr, bit [2:0] prot);
        return get_write_response(addr, prot); // Same logic
    endfunction
    
    function string get_response_name(bit [1:0] resp);
        case (resp)
            2'b00: return "OKAY";
            2'b01: return "EXOKAY";
            2'b10: return "SLVERR";
            2'b11: return "DECERR";
            default: return "UNKNOWN";
        endcase
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), $sformatf("Slave Statistics:"), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Read Transactions: %0d", num_read_trans), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Write Transactions: %0d", num_write_trans), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Error Responses: %0d", num_error_responses), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Security Violations: %0d", num_security_violations), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Address Range: 0x%0h - 0x%0h", base_address, base_address + size_bytes - 1), UVM_LOW)
    endfunction
    
endclass : axi4_slave_driver