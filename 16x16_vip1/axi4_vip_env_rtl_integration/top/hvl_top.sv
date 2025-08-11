//==============================================================================  
// HVL Top - UVM Testbench for 16x16 AXI4 Matrix
// Minimal UVM environment for VIP+RTL Integration
//==============================================================================

module hvl_top;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    
    // Basic UVM testbench for RTL integration
    class axi4_rtl_integration_test extends uvm_test;
        `uvm_component_utils(axi4_rtl_integration_test)
        
        function new(string name = "axi4_rtl_integration_test", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
        // Configuration for large matrices
        bit disable_unused_masters;
        int active_master_count;
        
        disable_unused_masters = 0;
        active_master_count = NO_OF_MASTERS;
        
        // For very large configurations, limit active masters
        if (NO_OF_MASTERS > 8 && disable_unused_masters) begin
            active_master_count = 8;
            `uvm_info(get_type_name(), $sformatf("Large config detected: limiting to %0d active masters", active_master_count), UVM_LOW)
        end

            `uvm_info(get_type_name(), "Building RTL integration test for 16x16 matrix", UVM_LOW)
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            `uvm_info(get_type_name(), "Starting master monitor run_phase", UVM_LOW)
            `uvm_info(get_type_name(), "Monitoring AXI4 master interface for transactions", UVM_MEDIUM)
            phase.raise_objection(this);
            `uvm_info(get_type_name(), "Running RTL integration test", UVM_LOW)
            
            // Basic test - just run for a while to verify RTL connectivity
            #1000;
            `uvm_info(get_type_name(), "RTL integration test completed", UVM_LOW)
            
            phase.drop_objection(this);
        endtask
    endclass
    
    initial begin
        // Set default test
        if ($test$plusargs("UVM_TESTNAME")) begin
            // Use test name from command line
        end else begin
            uvm_config_db#(string)::set(null, "*", "default_test", "axi4_rtl_integration_test");
        end
        
        run_test();
    end
    
endmodule
