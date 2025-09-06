// AXI4 Base Test - UVM-1.2 Compatible
import axi4_vip_pkg::*;

class axi4_base_test extends uvm_test;
    `uvm_component_utils(axi4_base_test)
    
    axi4_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = axi4_env::type_id::create("env", this);
        
        // UVM-1.2: Set default sequences for each agent
        uvm_config_db#(uvm_object_wrapper)::set(this, "env.master_agents[*].sequencer.run_phase", 
                                               "default_sequence", null);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
        super.run_phase(phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting AXI4 base test (UVM-1.2)", UVM_LOW)
        
        // UVM-1.2: Enhanced test control
        #1000ns;
        
        `uvm_info(get_type_name(), "AXI4 base test completed successfully", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
    // UVM-1.2: Enhanced final phase for cleanup
    virtual function void final_phase(uvm_phase phase);
        super.final_phase(phase);
        `uvm_info(get_type_name(), "Final phase: Test cleanup completed", UVM_LOW)
    endfunction
endclass
