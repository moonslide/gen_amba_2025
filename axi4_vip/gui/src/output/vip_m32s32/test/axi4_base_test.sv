// AXI4 Base Test
class axi4_base_test extends uvm_test;
    `uvm_component_utils(axi4_base_test)
    
    axi4_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = axi4_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting AXI4 base test", UVM_LOW)
        
        // Run test sequences
        #1000ns;
        
        `uvm_info(get_type_name(), "Test completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
endclass
