//==============================================================================
// AXI4 Protection Checker
// 
// Description: Validates access permissions based on AxPROT signals
// Implements configurable memory regions with access control
//==============================================================================

`include "axi4_defines.sv"

module axi4_prot_checker #(
    parameter int ADDR_WIDTH = 32,
    parameter int NUM_REGIONS = 16
)(
    input logic                    clk,
    input logic                    rst_n,
    
    // Configuration interface
    input logic                    cfg_wen,
    input logic [3:0]              cfg_region_sel,
    input logic [ADDR_WIDTH-1:0]   cfg_base_addr,
    input logic [ADDR_WIDTH-1:0]   cfg_end_addr,
    input logic                    cfg_read_enable,
    input logic                    cfg_write_enable,
    input logic                    cfg_secure_only,
    input logic                    cfg_privileged_only,
    input logic                    cfg_data_only,
    input logic                    cfg_region_enable,
    
    // Access check interface
    input logic                    check_valid,
    input logic [ADDR_WIDTH-1:0]   check_addr,
    input logic                    check_write,  // 0=read, 1=write
    input axi4_prot_t              check_prot,
    output logic                   check_pass,
    output logic                   check_error,
    output logic [3:0]             check_error_type  // Error code
);

    // Memory region definition
    typedef struct packed {
        logic [ADDR_WIDTH-1:0]   base_addr;
        logic [ADDR_WIDTH-1:0]   end_addr;
        logic                    read_enable;
        logic                    write_enable;
        logic                    secure_only;      // Requires secure access
        logic                    privileged_only;  // Requires privileged access
        logic                    data_only;        // Data access only (no instruction)
        logic                    region_enable;
    } mem_region_t;
    
    // Error codes
    localparam logic [3:0] ERR_NONE           = 4'h0;
    localparam logic [3:0] ERR_NO_REGION      = 4'h1;  // No matching region
    localparam logic [3:0] ERR_READ_DENIED    = 4'h2;  // Read not allowed
    localparam logic [3:0] ERR_WRITE_DENIED   = 4'h3;  // Write not allowed
    localparam logic [3:0] ERR_NONSECURE      = 4'h4;  // Non-secure access denied
    localparam logic [3:0] ERR_UNPRIVILEGED   = 4'h5;  // Unprivileged access denied
    localparam logic [3:0] ERR_INSTRUCTION    = 4'h6;  // Instruction access denied
    
    // Region storage
    mem_region_t regions[NUM_REGIONS];
    
    // Region configuration
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_REGIONS; i++) begin
                regions[i] <= '0;
            end
        end else if (cfg_wen && cfg_region_sel < NUM_REGIONS) begin
            regions[cfg_region_sel].base_addr       <= cfg_base_addr;
            regions[cfg_region_sel].end_addr        <= cfg_end_addr;
            regions[cfg_region_sel].read_enable     <= cfg_read_enable;
            regions[cfg_region_sel].write_enable    <= cfg_write_enable;
            regions[cfg_region_sel].secure_only     <= cfg_secure_only;
            regions[cfg_region_sel].privileged_only <= cfg_privileged_only;
            regions[cfg_region_sel].data_only       <= cfg_data_only;
            regions[cfg_region_sel].region_enable   <= cfg_region_enable;
        end
    end
    
    // Access checking logic
    always_comb begin
        check_pass = 1'b0;
        check_error = 1'b0;
        check_error_type = ERR_NONE;
        
        if (check_valid) begin
            logic region_found = 1'b0;
            logic access_allowed = 1'b0;
            
            // Search for matching region
            for (int i = 0; i < NUM_REGIONS; i++) begin
                if (regions[i].region_enable &&
                    check_addr >= regions[i].base_addr &&
                    check_addr <= regions[i].end_addr) begin
                    
                    region_found = 1'b1;
                    
                    // Check access type
                    if (check_write && !regions[i].write_enable) begin
                        check_error = 1'b1;
                        check_error_type = ERR_WRITE_DENIED;
                        break;
                    end else if (!check_write && !regions[i].read_enable) begin
                        check_error = 1'b1;
                        check_error_type = ERR_READ_DENIED;
                        break;
                    end
                    
                    // Check security
                    if (regions[i].secure_only && check_prot.nonsecure) begin
                        check_error = 1'b1;
                        check_error_type = ERR_NONSECURE;
                        break;
                    end
                    
                    // Check privilege
                    if (regions[i].privileged_only && !check_prot.privileged) begin
                        check_error = 1'b1;
                        check_error_type = ERR_UNPRIVILEGED;
                        break;
                    end
                    
                    // Check instruction/data
                    if (regions[i].data_only && check_prot.instruction) begin
                        check_error = 1'b1;
                        check_error_type = ERR_INSTRUCTION;
                        break;
                    end
                    
                    // All checks passed
                    access_allowed = 1'b1;
                    break;
                end
            end
            
            if (!region_found) begin
                check_error = 1'b1;
                check_error_type = ERR_NO_REGION;
            end else if (access_allowed && !check_error) begin
                check_pass = 1'b1;
            end
        end
    end
    
    // Debug information
    `ifdef AXI4_PROT_DEBUG
    always_ff @(posedge clk) begin
        if (check_valid && check_error) begin
            $display("[%t] PROT_CHECKER: Access denied - Addr=%0h, Write=%b, PROT=%b%b%b, Error=%0h",
                     $time, check_addr, check_write, 
                     check_prot.instruction, check_prot.nonsecure, check_prot.privileged,
                     check_error_type);
        end
    end
    `endif
    
    // Coverage
    `ifdef AXI4_COVERAGE
    covergroup prot_access_cg @(posedge clk);
        prot_type: coverpoint check_prot {
            bins secure_priv_data    = {3'b000};
            bins secure_priv_inst    = {3'b100};
            bins secure_unpriv_data  = {3'b001};
            bins secure_unpriv_inst  = {3'b101};
            bins nonsec_priv_data    = {3'b010};
            bins nonsec_priv_inst    = {3'b110};
            bins nonsec_unpriv_data  = {3'b011};
            bins nonsec_unpriv_inst  = {3'b111};
        }
        
        error_type: coverpoint check_error_type {
            bins no_error = {ERR_NONE};
            bins no_region = {ERR_NO_REGION};
            bins read_denied = {ERR_READ_DENIED};
            bins write_denied = {ERR_WRITE_DENIED};
            bins nonsecure = {ERR_NONSECURE};
            bins unprivileged = {ERR_UNPRIVILEGED};
            bins instruction = {ERR_INSTRUCTION};
        }
        
        access_type: coverpoint check_write {
            bins read = {0};
            bins write = {1};
        }
        
        cross prot_type, error_type, access_type;
    endgroup
    
    prot_access_cg prot_cov = new();
    `endif
    
endmodule : axi4_prot_checker