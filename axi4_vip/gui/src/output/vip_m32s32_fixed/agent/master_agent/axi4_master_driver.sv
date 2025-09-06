// AXI4 Master Driver
class axi4_master_driver extends uvm_driver #(axi4_transaction);
    `uvm_component_utils(axi4_master_driver)
    
    virtual axi4_if vif;
    int master_id;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
    endfunction
    
    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    task drive_transaction(axi4_transaction tr);
        // Drive AW channel
        @(posedge vif.aclk);
        vif.awvalid <= 1'b1;
        vif.awaddr <= tr.addr;
        vif.awlen <= tr.len;
        vif.awsize <= tr.size;
        vif.awburst <= tr.burst;
        vif.awqos <= tr.qos_aw;
        wait(vif.awready);
        vif.awvalid <= 1'b0;
        
        // Drive W channel
        for(int i = 0; i <= tr.len; i++) begin
            @(posedge vif.aclk);
            vif.wvalid <= 1'b1;
            vif.wdata <= tr.data[i];
            vif.wstrb <= tr.strb[i];
            vif.wlast <= (i == tr.len);
            wait(vif.wready);
        end
        vif.wvalid <= 1'b0;
        
        // Wait for B response
        wait(vif.bvalid);
        tr.resp = vif.bresp;
        @(posedge vif.aclk);
        vif.bready <= 1'b1;
        @(posedge vif.aclk);
        vif.bready <= 1'b0;
    endtask
endclass
