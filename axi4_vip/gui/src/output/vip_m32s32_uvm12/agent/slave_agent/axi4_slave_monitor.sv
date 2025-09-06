// AXI4 Slave Monitor
import axi4_vip_pkg::*;

class axi4_slave_monitor extends uvm_monitor;
    `uvm_component_utils(axi4_slave_monitor)
    
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
            monitor_response(trans);
            item_collected_port.write(trans);
        end
    endtask
    
    task monitor_response(axi4_transaction trans);
        // Monitor write response
        @(posedge vif.aclk);
        if(vif.bvalid && vif.bready) begin
            trans.resp = vif.bresp;
            trans.id = vif.bid;
            `uvm_info(get_type_name(), $sformatf("Monitored write response: id=0x%0h resp=%0d", trans.id, trans.resp), UVM_HIGH)
        end
        // Monitor read data
        else if(vif.rvalid && vif.rready) begin
            trans.resp = vif.rresp;
            trans.id = vif.rid;
            `uvm_info(get_type_name(), $sformatf("Monitored read response: id=0x%0h resp=%0d", trans.id, trans.resp), UVM_HIGH)
        end
    endtask
    
endclass
