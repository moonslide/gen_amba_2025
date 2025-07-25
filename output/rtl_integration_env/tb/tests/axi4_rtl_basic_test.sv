// Example test for RTL integration using tim_axi4_vip
// This test demonstrates basic read/write operations to your DUT

`ifndef AXI4_RTL_BASIC_TEST_SV
`define AXI4_RTL_BASIC_TEST_SV

class axi4_rtl_basic_test extends axi4_base_test;
    `uvm_component_utils(axi4_rtl_basic_test)
    
    // Virtual sequence handle
    axi4_virtual_write_read_seq virtual_seq;
    
    function new(string name = "axi4_rtl_basic_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Configure test parameters
        uvm_config_db#(int)::set(this, "*", "no_of_write_trans", 10);
        uvm_config_db#(int)::set(this, "*", "no_of_read_trans", 10);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_name(), "Starting RTL integration test", UVM_LOW)
        
        // Create and start virtual sequence
        virtual_seq = axi4_virtual_write_read_seq::type_id::create("virtual_seq");
        virtual_seq.start(env.virtual_seqr);
        
        #1000ns;
        
        phase.drop_objection(this);
    endtask
    
endclass

`endif
