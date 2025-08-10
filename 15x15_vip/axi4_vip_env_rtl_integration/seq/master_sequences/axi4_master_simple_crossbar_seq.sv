//==============================================================================
// AXI4 Master Simple Crossbar Sequence - Quick test with reduced transactions
//==============================================================================

class axi4_master_simple_crossbar_seq extends axi4_master_base_seq;
    `uvm_object_utils(axi4_master_simple_crossbar_seq)
    
    int master_id = 0;
    
    function new(string name = "axi4_master_simple_crossbar_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        axi4_master_tx write_xtn;
        axi4_master_tx read_xtn;
        
        `uvm_info(get_type_name(), $sformatf("Master %0d: Starting simplified crossbar test", master_id), UVM_LOW)
        
        // Only test first 3 slaves to reduce simulation time
        for (int slave = 0; slave < 3; slave++) begin
            bit [63:0] slave_base_addr;
            bit [255:0] write_data;
            
            // Calculate slave base address
            // Slave 0: 0x00000000, Slave 1: 0x10000000, Slave 2: 0x20000000
            slave_base_addr = slave * 64'h10000000;
            
            // Generate unique data pattern
            write_data = {master_id[7:0], slave[7:0], 240'hABCD_1234};
            
            //--------------------------------------------------------------
            // WRITE TRANSACTION
            //--------------------------------------------------------------
            `uvm_info(get_type_name(), $sformatf("Master %0d: Writing to Slave %0d at addr 0x%0h", 
                      master_id, slave, slave_base_addr), UVM_LOW)
            
            write_xtn = axi4_master_tx::type_id::create("write_xtn");
            
            // Simple write with just 1 beat to make it faster
            if (!write_xtn.randomize() with {
                tx_type == WRITE;
                awaddr == slave_base_addr + (master_id * 'h100);
                awlen == 0;           // Single beat only
                awsize == 3'b011;     // 8 bytes
                awburst == 2'b00;     // FIXED burst
                awid == master_id[3:0];
                wdata.size() == 1;    // Single data beat
                wdata[0] == write_data;
            }) begin
                `uvm_error(get_type_name(), "Write transaction randomization failed")
            end
            
            `uvm_info(get_type_name(), $sformatf("Sending write transaction to sequencer"), UVM_HIGH)
            start_item(write_xtn);
            finish_item(write_xtn);
            `uvm_info(get_type_name(), $sformatf("Write transaction completed"), UVM_HIGH)
            
            // Small delay
            #50;
            
            //--------------------------------------------------------------
            // READ TRANSACTION
            //--------------------------------------------------------------
            `uvm_info(get_type_name(), $sformatf("Master %0d: Reading from Slave %0d at addr 0x%0h", 
                      master_id, slave, slave_base_addr), UVM_LOW)
            
            read_xtn = axi4_master_tx::type_id::create("read_xtn");
            
            // Simple read with just 1 beat
            if (!read_xtn.randomize() with {
                tx_type == READ;
                araddr == slave_base_addr + (master_id * 'h100);
                arlen == 0;           // Single beat only
                arsize == 3'b011;     // 8 bytes
                arburst == 2'b00;     // FIXED burst
                arid == master_id[3:0];
            }) begin
                `uvm_error(get_type_name(), "Read transaction randomization failed")
            end
            
            `uvm_info(get_type_name(), $sformatf("Sending read transaction to sequencer"), UVM_HIGH)
            start_item(read_xtn);
            finish_item(read_xtn);
            `uvm_info(get_type_name(), $sformatf("Read transaction completed"), UVM_HIGH)
            
            // Delay before next slave
            #50;
        end
        
        `uvm_info(get_type_name(), $sformatf("Master %0d: Completed all transactions", master_id), UVM_LOW)
    endtask
    
endclass