//==============================================================================
// AXI4 VIP Package - Complete UVM-based AXI4 Verification IP
// Includes all classes, sequences, and utilities for AXI4 protocol verification
//==============================================================================

`ifndef AXI4_VIP_PKG_SV
`define AXI4_VIP_PKG_SV

package axi4_vip_pkg;
    
    // Import UVM library
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Package parameters - can be overridden by testbench
    parameter int DEFAULT_ADDR_WIDTH = 32;
    parameter int DEFAULT_DATA_WIDTH = 64;
    parameter int DEFAULT_ID_WIDTH   = 4;
    parameter int DEFAULT_USER_WIDTH = 1;
    parameter int DEFAULT_WSTRB_WIDTH = DEFAULT_DATA_WIDTH/8;
    
    // Protocol constants
    parameter bit [1:0] AXI4_BURST_FIXED = 2'b00;
    parameter bit [1:0] AXI4_BURST_INCR  = 2'b01;
    parameter bit [1:0] AXI4_BURST_WRAP  = 2'b10;
    parameter bit [1:0] AXI4_BURST_RESV  = 2'b11;
    
    parameter bit [1:0] AXI4_RESP_OKAY   = 2'b00;
    parameter bit [1:0] AXI4_RESP_EXOKAY = 2'b01;
    parameter bit [1:0] AXI4_RESP_SLVERR = 2'b10;
    parameter bit [1:0] AXI4_RESP_DECERR = 2'b11;
    
    parameter bit [2:0] AXI4_SIZE_1B   = 3'b000;
    parameter bit [2:0] AXI4_SIZE_2B   = 3'b001;
    parameter bit [2:0] AXI4_SIZE_4B   = 3'b010;
    parameter bit [2:0] AXI4_SIZE_8B   = 3'b011;
    parameter bit [2:0] AXI4_SIZE_16B  = 3'b100;
    parameter bit [2:0] AXI4_SIZE_32B  = 3'b101;
    parameter bit [2:0] AXI4_SIZE_64B  = 3'b110;
    parameter bit [2:0] AXI4_SIZE_128B = 3'b111;
    
    // Protection type encoding
    parameter bit [2:0] AXI4_PROT_UNPRIV_NONSECURE_DATA = 3'b000;
    parameter bit [2:0] AXI4_PROT_PRIV_NONSECURE_DATA   = 3'b001;
    parameter bit [2:0] AXI4_PROT_UNPRIV_SECURE_DATA    = 3'b010;
    parameter bit [2:0] AXI4_PROT_PRIV_SECURE_DATA      = 3'b011;
    parameter bit [2:0] AXI4_PROT_UNPRIV_NONSECURE_INST = 3'b100;
    parameter bit [2:0] AXI4_PROT_PRIV_NONSECURE_INST   = 3'b101;
    parameter bit [2:0] AXI4_PROT_UNPRIV_SECURE_INST    = 3'b110;
    parameter bit [2:0] AXI4_PROT_PRIV_SECURE_INST      = 3'b111;
    
    // Cache type encoding examples
    parameter bit [3:0] AXI4_CACHE_DEVICE_NON_BUFFERABLE = 4'b0000;
    parameter bit [3:0] AXI4_CACHE_DEVICE_BUFFERABLE     = 4'b0001;
    parameter bit [3:0] AXI4_CACHE_NORMAL_NON_CACHEABLE  = 4'b0010;
    parameter bit [3:0] AXI4_CACHE_WRITE_THROUGH         = 4'b0110;
    parameter bit [3:0] AXI4_CACHE_WRITE_BACK            = 4'b1110;
    
    // Utility macros for common operations
    `define AXI4_ADDR_ALIGNED(addr, size) ((addr & ((1 << size) - 1)) == 0)
    `define AXI4_4KB_BOUNDARY_CHECK(addr, len, size) \
        ((addr[31:12] == (addr + ((len + 1) * (1 << size)) - 1)[31:12]))
    `define AXI4_WRAP_BOUNDARY(addr, len, size) \
        ((addr / ((len + 1) * (1 << size))) * ((len + 1) * (1 << size)))
    
    // Include all source files in compilation order
    
    // 1. Configuration reader
    `include "config/axi4_config_reader.sv"
    
    // 2. Transaction class
    `include "sequences/axi4_transaction.sv"
    
    // 3. Driver classes
    `include "agents/axi4_master_driver.sv"
    `include "agents/axi4_slave_driver.sv"
    
    // 4. Monitor class
    `include "agents/axi4_monitor.sv"
    
    // 5. Agent classes
    `include "agents/axi4_master_agent.sv"
    
    // 6. Sequence classes
    `include "sequences/axi4_sequences.sv"
    
    // 7. Scoreboard
    `include "testbench/axi4_scoreboard.sv"
    
    // 8. Test environment and base test
    `include "testbench/axi4_test_env.sv"
    
    // Utility functions for package users
    function automatic bit is_valid_burst_length(bit [7:0] len, bit [1:0] burst_type);
        case (burst_type)
            AXI4_BURST_FIXED: return (len <= 8'hFF);
            AXI4_BURST_INCR:  return (len <= 8'hFF);
            AXI4_BURST_WRAP:  return (len inside {1, 3, 7, 15});
            default:          return 0;
        endcase
    endfunction
    
    function automatic bit is_valid_transfer_size(bit [2:0] size);
        return (size <= 3'b111);
    endfunction
    
    function automatic bit crosses_4kb_boundary(bit [63:0] addr, bit [7:0] len, bit [2:0] size);
        bit [63:0] start_addr = addr;
        bit [63:0] end_addr = addr + ((len + 1) * (1 << size)) - 1;
        return (start_addr[63:12] != end_addr[63:12]);
    endfunction
    
    function automatic int calculate_transfer_bytes(bit [7:0] len, bit [2:0] size);
        return (len + 1) * (1 << size);
    endfunction
    
    function automatic bit [63:0] align_address(bit [63:0] addr, bit [2:0] size);
        return addr & ~((1 << size) - 1);
    endfunction
    
    function automatic string burst_type_to_string(bit [1:0] burst_type);
        case (burst_type)
            AXI4_BURST_FIXED: return "FIXED";
            AXI4_BURST_INCR:  return "INCR";
            AXI4_BURST_WRAP:  return "WRAP";
            default:          return "RESERVED";
        endcase
    endfunction
    
    function automatic string response_to_string(bit [1:0] resp);
        case (resp)
            AXI4_RESP_OKAY:   return "OKAY";
            AXI4_RESP_EXOKAY: return "EXOKAY";
            AXI4_RESP_SLVERR: return "SLVERR";
            AXI4_RESP_DECERR: return "DECERR";
            default:          return "UNKNOWN";
        endcase
    endfunction
    
    function automatic string protection_to_string(bit [2:0] prot);
        case (prot)
            AXI4_PROT_UNPRIV_NONSECURE_DATA: return "UNPRIV_NONSECURE_DATA";
            AXI4_PROT_PRIV_NONSECURE_DATA:   return "PRIV_NONSECURE_DATA";
            AXI4_PROT_UNPRIV_SECURE_DATA:    return "UNPRIV_SECURE_DATA";
            AXI4_PROT_PRIV_SECURE_DATA:      return "PRIV_SECURE_DATA";
            AXI4_PROT_UNPRIV_NONSECURE_INST: return "UNPRIV_NONSECURE_INST";
            AXI4_PROT_PRIV_NONSECURE_INST:   return "PRIV_NONSECURE_INST";
            AXI4_PROT_UNPRIV_SECURE_INST:    return "UNPRIV_SECURE_INST";
            AXI4_PROT_PRIV_SECURE_INST:      return "PRIV_SECURE_INST";
            default:                         return "UNKNOWN_PROT";
        endcase
    endfunction
    
    // Configuration class for easy testbench setup
    class axi4_vip_config extends uvm_object;
        
        `uvm_object_utils(axi4_vip_config)
        
        // Interface parameters
        int addr_width = DEFAULT_ADDR_WIDTH;
        int data_width = DEFAULT_DATA_WIDTH;
        int id_width   = DEFAULT_ID_WIDTH;
        int user_width = DEFAULT_USER_WIDTH;
        
        // Agent configuration
        bit master_active = 1;
        bit slave_active = 1;
        bit enable_scoreboard = 1;
        bit enable_coverage = 1;
        
        // Memory configuration
        bit [63:0] slave_base_addr = 64'h1000_0000;
        bit [63:0] slave_size = 64'h1000_0000; // 256MB
        
        // Behavioral configuration
        int slave_error_rate = 5; // 5% error injection
        int read_latency_min = 1;
        int read_latency_max = 10;
        int write_latency_min = 1;
        int write_latency_max = 10;
        
        // Test configuration
        int max_outstanding_reads = 16;
        int max_outstanding_writes = 16;
        realtime timeout_period = 10000ns;
        
        function new(string name = "axi4_vip_config");
            super.new(name);
        endfunction
        
        // Validation function
        virtual function bit is_valid_config();
            bit valid = 1;
            
            if (addr_width < 12 || addr_width > 64) begin
                `uvm_error("CONFIG", $sformatf("Invalid addr_width: %0d", addr_width))
                valid = 0;
            end
            
            if (!(data_width inside {32, 64, 128, 256, 512})) begin
                `uvm_error("CONFIG", $sformatf("Invalid data_width: %0d", data_width))
                valid = 0;
            end
            
            if (id_width < 1 || id_width > 8) begin
                `uvm_error("CONFIG", $sformatf("Invalid id_width: %0d", id_width))
                valid = 0;
            end
            
            if (slave_size == 0) begin
                `uvm_error("CONFIG", "Slave size cannot be zero")
                valid = 0;
            end
            
            return valid;
        endfunction
        
        // Pretty print configuration
        virtual function void print_config();
            `uvm_info("CONFIG", "=== AXI4 VIP Configuration ===", UVM_LOW)
            `uvm_info("CONFIG", $sformatf("  Address Width: %0d bits", addr_width), UVM_LOW)
            `uvm_info("CONFIG", $sformatf("  Data Width: %0d bits", data_width), UVM_LOW)
            `uvm_info("CONFIG", $sformatf("  ID Width: %0d bits", id_width), UVM_LOW)
            `uvm_info("CONFIG", $sformatf("  User Width: %0d bits", user_width), UVM_LOW)
            `uvm_info("CONFIG", $sformatf("  Master Active: %0b", master_active), UVM_LOW)
            `uvm_info("CONFIG", $sformatf("  Slave Active: %0b", slave_active), UVM_LOW)
            `uvm_info("CONFIG", $sformatf("  Scoreboard: %0b", enable_scoreboard), UVM_LOW)
            `uvm_info("CONFIG", $sformatf("  Coverage: %0b", enable_coverage), UVM_LOW)
            `uvm_info("CONFIG", $sformatf("  Slave Address: 0x%0h - 0x%0h", 
                                         slave_base_addr, slave_base_addr + slave_size - 1), UVM_LOW)
            `uvm_info("CONFIG", $sformatf("  Error Rate: %0d%%", slave_error_rate), UVM_LOW)
            `uvm_info("CONFIG", "===============================", UVM_LOW)
        endfunction
        
    endclass : axi4_vip_config
    
    // Factory convenience functions
    function automatic axi4_transaction create_axi4_transaction(string name = "axi4_trans");
        axi4_transaction trans = axi4_transaction::type_id::create(name);
        return trans;
    endfunction
    
    function automatic axi4_basic_sequence create_basic_sequence(string name = "basic_seq");
        axi4_basic_sequence seq = axi4_basic_sequence::type_id::create(name);
        return seq;
    endfunction
    
    function automatic axi4_burst_sequence create_burst_sequence(string name = "burst_seq");
        axi4_burst_sequence seq = axi4_burst_sequence::type_id::create(name);
        return seq;
    endfunction
    
    function automatic axi4_stress_sequence create_stress_sequence(string name = "stress_seq");
        axi4_stress_sequence seq = axi4_stress_sequence::type_id::create(name);
        return seq;
    endfunction
    
    // Debug and analysis utilities
    class axi4_vip_reporter extends uvm_report_catcher;
        
        `uvm_object_utils(axi4_vip_reporter)
        
        int error_count = 0;
        int warning_count = 0;
        int info_count = 0;
        
        function new(string name = "axi4_vip_reporter");
            super.new(name);
        endfunction
        
        virtual function action_e catch(uvm_report_object client,
                                       uvm_severity severity,
                                       string id,
                                       string message,
                                       int verbosity,
                                       string filename,
                                       int line,
                                       string context_name);
            
            case (severity)
                UVM_ERROR: error_count++;
                UVM_WARNING: warning_count++;
                UVM_INFO: info_count++;
            endcase
            
            // Let message through
            return THROW;
        endfunction
        
        virtual function void report_summary();
            `uvm_info("VIP_REPORTER", "=== AXI4 VIP Message Summary ===", UVM_LOW)
            `uvm_info("VIP_REPORTER", $sformatf("  Errors: %0d", error_count), UVM_LOW)
            `uvm_info("VIP_REPORTER", $sformatf("  Warnings: %0d", warning_count), UVM_LOW)
            `uvm_info("VIP_REPORTER", $sformatf("  Info Messages: %0d", info_count), UVM_LOW)
            `uvm_info("VIP_REPORTER", "================================", UVM_LOW)
        endfunction
        
    endclass : axi4_vip_reporter
    
    // Global package variables for debugging
    axi4_vip_reporter global_reporter;
    
    // Package initialization function
    function automatic void axi4_vip_init();
        global_reporter = axi4_vip_reporter::type_id::create("global_reporter");
        uvm_report_cb::add(null, global_reporter);
        `uvm_info("AXI4_VIP_PKG", "AXI4 VIP Package initialized", UVM_MEDIUM)
    endfunction
    
    // Package finalization function
    function automatic void axi4_vip_finish();
        if (global_reporter != null) begin
            global_reporter.report_summary();
        end
        `uvm_info("AXI4_VIP_PKG", "AXI4 VIP Package finalized", UVM_MEDIUM)
    endfunction
    
endpackage : axi4_vip_pkg

`endif // AXI4_VIP_PKG_SV