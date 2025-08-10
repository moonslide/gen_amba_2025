#!/usr/bin/env python3
"""Generate full crossbar test for AXI4 VIP environments"""

def generate_full_crossbar_test(num_masters, num_slaves):
    """Generate test that exercises all masters to all slaves"""
    
    test_code = f"""//==============================================================================
// AXI4 Full Crossbar Test - Tests all masters to all slaves
// This test verifies that every master can access every slave
//==============================================================================

class axi4_full_crossbar_test extends axi4_base_test;
    `uvm_component_utils(axi4_full_crossbar_test)
    
    function new(string name = "axi4_full_crossbar_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        axi4_virtual_full_crossbar_seq vseq;
        
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Starting Full Crossbar Test - All Masters to All Slaves", UVM_LOW)
        
        // Create and start the virtual sequence
        vseq = axi4_virtual_full_crossbar_seq::type_id::create("vseq");
        vseq.start(env.v_seqr);
        
        // Allow time for all transactions to complete
        #10000;
        
        `uvm_info(get_type_name(), "Full Crossbar Test Completed", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
endclass"""
    
    return test_code

def generate_full_crossbar_virtual_seq(num_masters, num_slaves):
    """Generate virtual sequence for full crossbar test"""
    
    vseq_code = f"""//==============================================================================
// AXI4 Virtual Full Crossbar Sequence
// Generates transactions from all masters to all slaves
//==============================================================================

class axi4_virtual_full_crossbar_seq extends axi4_virtual_base_seq;
    `uvm_object_utils(axi4_virtual_full_crossbar_seq)
    
    function new(string name = "axi4_virtual_full_crossbar_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        axi4_master_full_crossbar_seq master_seq[{num_masters}];
        
        `uvm_info(get_type_name(), "Starting Full Crossbar Virtual Sequence", UVM_LOW)
        
        // Start sequences on all {num_masters} masters in parallel
        fork
            begin
                for (int m = 0; m < {num_masters}; m++) begin
                    automatic int master_id = m;
                    fork
                        begin
                            `uvm_info(get_type_name(), $sformatf("Starting sequence on Master %0d", master_id), UVM_LOW)
                            master_seq[master_id] = axi4_master_full_crossbar_seq::type_id::create($sformatf("master_seq_%0d", master_id));
                            master_seq[master_id].master_id = master_id;
                            master_seq[master_id].start(p_sequencer.master_seqr[master_id]);
                            `uvm_info(get_type_name(), $sformatf("Completed sequence on Master %0d", master_id), UVM_LOW)
                        end
                    join_none
                end
                
                // Wait for all masters to complete
                wait fork;
            end
        join
        
        `uvm_info(get_type_name(), "All master sequences completed", UVM_LOW)
        
        // Add delay to let all transactions complete
        #5000;
        
        `uvm_info(get_type_name(), "Full Crossbar Virtual Sequence Completed", UVM_LOW)
    endtask
    
endclass"""
    
    return vseq_code

def generate_full_crossbar_master_seq(num_masters, num_slaves, addr_width=64, data_width=256):
    """Generate master sequence for full crossbar test"""
    
    # Calculate address spacing based on number of slaves
    addr_bits_per_slave = addr_width // num_slaves if num_slaves <= 16 else 4
    
    seq_code = f"""//==============================================================================
// AXI4 Master Full Crossbar Sequence
// Each master sends transactions to all slaves
//==============================================================================

class axi4_master_full_crossbar_seq extends axi4_master_base_seq;
    `uvm_object_utils(axi4_master_full_crossbar_seq)
    
    int master_id = 0;
    
    function new(string name = "axi4_master_full_crossbar_seq");
        super.new(name);
    endfunction
    
    virtual task body();
        axi4_master_tx write_xtn;
        axi4_master_tx read_xtn;
        
        `uvm_info(get_type_name(), $sformatf("Master %0d: Starting transactions to all slaves", master_id), UVM_LOW)
        
        // Send transactions to each of the {num_slaves} slaves
        for (int slave = 0; slave < {num_slaves}; slave++) begin
            bit [{addr_width-1}:0] slave_base_addr;
            bit [{data_width-1}:0] write_data;
            
            // Calculate slave base address
            // Address mapping for proper crossbar routing
            slave_base_addr = slave * {addr_width}'h{256//num_slaves:X}000000;
            
            // Generate unique data pattern for this master-slave pair
            write_data = {{master_id[7:0], slave[7:0], {data_width-16}'hDEADBEEF_CAFEBABE}};
            
            //--------------------------------------------------------------
            // WRITE TRANSACTION
            //--------------------------------------------------------------
            `uvm_info(get_type_name(), $sformatf("Master %0d: Writing to Slave %0d at addr 0x%0h", 
                      master_id, slave, slave_base_addr), UVM_LOW)
            
            write_xtn = axi4_master_tx::type_id::create("write_xtn");
            
            if (!write_xtn.randomize() with {{
                tx_type == WRITE;
                awaddr == slave_base_addr + (master_id * 'h100);  // Unique address per master
                awlen == 3;           // 4 beat burst
                awsize == 3'b101;     // 32 bytes per beat  
                awburst == 2'b01;     // INCR burst
                awid == master_id[3:0];  // Use master ID
                wdata.size() == awlen + 1;
                foreach(wdata[i]) {{
                    wdata[i] == write_data + i;
                }}
            }}) begin
                `uvm_error(get_type_name(), "Write transaction randomization failed")
            end
            
            start_item(write_xtn);
            finish_item(write_xtn);
            
            // Small delay between transactions
            #100;
            
            //--------------------------------------------------------------
            // READ TRANSACTION
            //--------------------------------------------------------------
            `uvm_info(get_type_name(), $sformatf("Master %0d: Reading from Slave %0d at addr 0x%0h", 
                      master_id, slave, slave_base_addr), UVM_LOW)
            
            read_xtn = axi4_master_tx::type_id::create("read_xtn");
            
            if (!read_xtn.randomize() with {{
                tx_type == READ;
                araddr == slave_base_addr + (master_id * 'h100);  // Same address as write
                arlen == 3;           // 4 beat burst
                arsize == 3'b101;     // 32 bytes per beat
                arburst == 2'b01;     // INCR burst
                arid == master_id[3:0];  // Use master ID
            }}) begin
                `uvm_error(get_type_name(), "Read transaction randomization failed")
            end
            
            start_item(read_xtn);
            finish_item(read_xtn);
            
            // Delay before next slave
            #100;
        end
        
        `uvm_info(get_type_name(), $sformatf("Master %0d: Completed all transactions", master_id), UVM_LOW)
    endtask
    
endclass"""
    
    return seq_code

def add_full_crossbar_test_to_vip(base_path, num_masters, num_slaves):
    """Add full crossbar test files to VIP environment"""
    import os
    
    # Create test file
    test_file = os.path.join(base_path, "test/axi4_full_crossbar_test.sv")
    with open(test_file, "w") as f:
        f.write(generate_full_crossbar_test(num_masters, num_slaves))
    
    # Create virtual sequence file
    vseq_file = os.path.join(base_path, "virtual_seq/axi4_virtual_full_crossbar_seq.sv")
    with open(vseq_file, "w") as f:
        f.write(generate_full_crossbar_virtual_seq(num_masters, num_slaves))
    
    # Create master sequence file
    mseq_file = os.path.join(base_path, "seq/master_sequences/axi4_master_full_crossbar_seq.sv")
    with open(mseq_file, "w") as f:
        f.write(generate_full_crossbar_master_seq(num_masters, num_slaves))
    
    print(f"Added full crossbar test files for {num_masters}x{num_slaves} configuration")

if __name__ == "__main__":
    import sys
    if len(sys.argv) != 4:
        print("Usage: python3 vip_full_crossbar_test_generator.py <base_path> <num_masters> <num_slaves>")
        sys.exit(1)
    
    base_path = sys.argv[1]
    num_m = int(sys.argv[2])
    num_s = int(sys.argv[3])
    
    add_full_crossbar_test_to_vip(base_path, num_m, num_s)