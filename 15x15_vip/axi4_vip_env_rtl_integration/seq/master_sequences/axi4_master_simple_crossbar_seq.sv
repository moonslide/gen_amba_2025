//==============================================================================
// AXI4 Master Simple Crossbar Sequence - Tests all AXI channels
// ULTRATHINK: Proper write and read transactions with correct data patterns
//==============================================================================

class axi4_master_simple_crossbar_seq extends axi4_master_base_seq;
    `uvm_object_utils(axi4_master_simple_crossbar_seq)
    
    int master_id = 0;
    
    function new(string name = "axi4_master_simple_crossbar_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        axi4_master_tx write_xtn, read_xtn;
        
        // Add initial delay based on master_id to prevent simultaneous starts
        #(master_id * 10);
        
        `uvm_info(get_type_name(), $sformatf("Master %0d: Starting crossbar test with W and R", master_id), UVM_LOW)
        
        // WRITE TRANSACTION - with proper data pattern
        write_xtn = axi4_master_tx::type_id::create("write_xtn");
        
        if (!write_xtn.randomize() with {
            tx_type == axi4_master_tx::WRITE;
            awaddr == 64'h00001000 + (master_id * 64'h100);  // Unique address per master
            awlen == 3;           // 4 beats to test wlast properly
            awsize == 3'b011;     // 8 bytes
            awburst == 2'b01;     // INCR burst
            awid == master_id[3:0];
            wdata.size() == 4;    // 4 data beats
            wstrb.size() == 4;
            foreach(wdata[i]) {
                wdata[i] == (256'hCAFE0000_00000000 + i + (master_id << 8));  // Unique pattern
            }
            foreach(wstrb[i]) {
                wstrb[i] == '1;
            }
        }) begin
            `uvm_error(get_type_name(), "Write transaction randomization failed")
        end
        
        `uvm_info(get_type_name(), $sformatf("Sending WRITE to addr=0x%0h with %0d beats", 
                  write_xtn.awaddr, write_xtn.awlen+1), UVM_MEDIUM)
        
        start_item(write_xtn);
        finish_item(write_xtn);
        
        // Small delay between transactions
        #100;
        
        // READ TRANSACTION - read back what we wrote
        read_xtn = axi4_master_tx::type_id::create("read_xtn");
        
        if (!read_xtn.randomize() with {
            tx_type == axi4_master_tx::READ;
            araddr == 64'h00001000 + (master_id * 64'h100);  // Same address as write
            arlen == 3;           // 4 beats
            arsize == 3'b011;     // 8 bytes
            arburst == 2'b01;     // INCR burst
            arid == (master_id[3:0] ^ 4'h8);  // Different ID for read (toggle bit 3)
        }) begin
            `uvm_error(get_type_name(), "Read transaction randomization failed")
        end
        
        `uvm_info(get_type_name(), $sformatf("Sending READ from addr=0x%0h with %0d beats", 
                  read_xtn.araddr, read_xtn.arlen+1), UVM_MEDIUM)
        
        start_item(read_xtn);
        finish_item(read_xtn);
        
        // Check read data if available
        if (read_xtn.rdata.size() > 0) begin
            foreach(read_xtn.rdata[i]) begin
                `uvm_info(get_type_name(), $sformatf("Read data[%0d]: 0x%0h", i, read_xtn.rdata[i]), UVM_MEDIUM)
            end
        end
        
        `uvm_info(get_type_name(), $sformatf("Master %0d: Completed W+R test", master_id), UVM_LOW)
    endtask
    
endclass
