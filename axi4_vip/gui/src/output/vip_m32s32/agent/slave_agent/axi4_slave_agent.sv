// AXI4 Slave Agent
import axi4_vip_pkg::*;

class axi4_slave_agent extends uvm_agent;
    `uvm_component_utils(axi4_slave_agent)
    
    axi4_slave_driver driver;
    axi4_slave_monitor monitor;
    uvm_sequencer #(axi4_transaction) sequencer;
    
    int slave_id;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        monitor = axi4_slave_monitor::type_id::create("monitor", this);
        
        if(get_is_active() == UVM_ACTIVE) begin
            driver = axi4_slave_driver::type_id::create("driver", this);
            sequencer = uvm_sequencer#(axi4_transaction)::type_id::create("sequencer", this);
        end
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if(get_is_active() == UVM_ACTIVE) begin
            driver.seq_item_port.connect(sequencer.seq_item_export);
        end
    endfunction
    
endclass
