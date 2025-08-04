//==============================================================================
// AXI4 Master Driver - Enhanced Version with BFM Integration
//==============================================================================

class axi4_master_driver_enhanced extends uvm_driver #(axi4_master_tx);
    `uvm_component_utils(axi4_master_driver_enhanced)
    
    // Virtual interface handle to BFM
    virtual axi4_master_driver_bfm vif;
    
    // Configuration
    axi4_master_agent_config cfg;
    
    // Transaction counter
    int unsigned trans_cnt = 0;
    
    function new(string name = "axi4_master_driver_enhanced", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(), "Building enhanced master driver", UVM_LOW)
        
        // Get configuration
        if(!uvm_config_db#(axi4_master_agent_config)::get(this, "", "cfg", cfg))
            `uvm_fatal("CONFIG", "Cannot get master agent config from uvm_config_db")
            
        // Get virtual interface
        if(!uvm_config_db#(virtual axi4_master_driver_bfm)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not set in config_db")
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Starting enhanced master driver run_phase", UVM_LOW)
        
        // Wait for reset
        @(posedge vif.aresetn);
        `uvm_info(get_type_name(), "Reset released, driver ready", UVM_MEDIUM)
        
        forever begin
            `uvm_info(get_type_name(), "Waiting for next transaction from sequencer", UVM_HIGH)
            seq_item_port.get_next_item(req);
            trans_cnt++;
            
            `uvm_info(get_type_name(), $sformatf("Transaction #%0d: Got %s transaction", 
                trans_cnt, req.tx_type.name()), UVM_MEDIUM)
            
            // Drive the transaction
            drive_transaction(req);
            
            `uvm_info(get_type_name(), $sformatf("Transaction #%0d completed", trans_cnt), UVM_MEDIUM)
            seq_item_port.item_done();
        end
    endtask
    
    virtual task drive_transaction(axi4_master_tx tx);
        if (tx.tx_type == axi4_master_tx::WRITE) begin
            drive_write_transaction(tx);
        end else begin
            drive_read_transaction(tx);
        end
    endtask
    
    virtual task drive_write_transaction(axi4_master_tx tx);
        logic [DATA_WIDTH-1:0] data_array[];
        logic [(DATA_WIDTH/8)-1:0] strb_array[];
        logic [ID_WIDTH-1:0] resp_id;
        logic [1:0] resp;
        
        `uvm_info(get_type_name(), $sformatf("Driving WRITE transaction - addr=0x%0h, len=%0d, size=%0d, burst=%0d, id=%0d", 
            tx.awaddr, tx.awlen, tx.awsize, tx.awburst, tx.awid), UVM_MEDIUM)
        
        // Prepare data array
        data_array = new[tx.awlen + 1];
        strb_array = new[tx.awlen + 1];
        
        // Generate write data if not provided
        if (tx.wdata.size() == 0) begin
            tx.wdata = new[tx.awlen + 1];
            for (int i = 0; i <= tx.awlen; i++) begin
                tx.wdata[i] = $random();
                `uvm_info(get_type_name(), $sformatf("Generated write data[%0d] = 0x%0h", i, tx.wdata[i]), UVM_HIGH)
            end
        end
        
        // Copy to local arrays
        for (int i = 0; i <= tx.awlen; i++) begin
            data_array[i] = tx.wdata[i];
            strb_array[i] = '1; // All bytes valid
        end
        
        // Call BFM write transaction task
        vif.write_transaction(
            tx.awid,
            tx.awaddr,
            tx.awlen,
            tx.awsize,
            tx.awburst,
            data_array,
            strb_array
        );
        
        `uvm_info(get_type_name(), "WRITE transaction completed on BFM", UVM_MEDIUM)
    endtask
    
    virtual task drive_read_transaction(axi4_master_tx tx);
        logic [DATA_WIDTH-1:0] data_array[];
        logic [1:0] resp_array[];
        
        `uvm_info(get_type_name(), $sformatf("Driving READ transaction - addr=0x%0h, len=%0d, size=%0d, burst=%0d, id=%0d", 
            tx.araddr, tx.arlen, tx.arsize, tx.arburst, tx.arid), UVM_MEDIUM)
        
        // Allocate arrays
        data_array = new[tx.arlen + 1];
        resp_array = new[tx.arlen + 1];
        
        // Call BFM read transaction task
        vif.read_transaction(
            tx.arid,
            tx.araddr,
            tx.arlen,
            tx.arsize,
            tx.arburst,
            data_array,
            resp_array
        );
        
        // Store read data back in transaction
        tx.rdata = new[tx.arlen + 1];
        tx.rresp = new[tx.arlen + 1];
        
        for (int i = 0; i <= tx.arlen; i++) begin
            tx.rdata[i] = data_array[i];
            tx.rresp[i] = resp_array[i];
            `uvm_info(get_type_name(), $sformatf("Read data[%0d] = 0x%0h, resp=%0d", 
                i, tx.rdata[i], tx.rresp[i]), UVM_HIGH)
        end
        
        `uvm_info(get_type_name(), "READ transaction completed on BFM", UVM_MEDIUM)
    endtask
    
endclass : axi4_master_driver_enhanced