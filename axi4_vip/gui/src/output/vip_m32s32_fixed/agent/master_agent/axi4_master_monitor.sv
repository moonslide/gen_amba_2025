// AXI4 Master Monitor
class axi4_master_monitor extends uvm_monitor;
    `uvm_component_utils(axi4_master_monitor)
    
    virtual axi4_if vif;
    uvm_analysis_port #(axi4_transaction) item_collected_port;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
    endfunction
    
    task run_phase(uvm_phase phase);
        axi4_transaction trans;
        forever begin
            trans = axi4_transaction::type_id::create("trans");
            monitor_transaction(trans);
            item_collected_port.write(trans);
        end
    endtask
    
    task monitor_transaction(axi4_transaction trans);
        // Monitor write address channel
        @(posedge vif.aclk);
        if(vif.awvalid && vif.awready) begin
            trans.trans_type = axi4_transaction::WRITE;
            trans.addr = vif.awaddr;
            trans.len = vif.awlen;
            trans.size = vif.awsize;
            trans.burst = vif.awburst;
            trans.id = vif.awid;
            `uvm_info(get_type_name(), $sformatf("Monitored write transaction: addr=0x%0h", trans.addr), UVM_HIGH)
        end
        // Monitor read address channel
        else if(vif.arvalid && vif.arready) begin
            trans.trans_type = axi4_transaction::READ;
            trans.addr = vif.araddr;
            trans.len = vif.arlen;
            trans.size = vif.arsize;
            trans.burst = vif.arburst;
            trans.id = vif.arid;
            `uvm_info(get_type_name(), $sformatf("Monitored read transaction: addr=0x%0h", trans.addr), UVM_HIGH)
        end
    endtask
    
endclass
