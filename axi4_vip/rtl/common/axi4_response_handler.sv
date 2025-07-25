//==============================================================================
// AXI4 Response Handler
// 
// Description: Handles all AXI4 response types (OKAY, EXOKAY, SLVERR, DECERR)
// Includes error injection and response tracking
//==============================================================================

`include "axi4_defines.sv"

module axi4_response_handler #(
    parameter int ID_WIDTH = 4,
    parameter int DATA_WIDTH = 64,
    parameter int ADDR_WIDTH = 32
)(
    input logic                    clk,
    input logic                    rst_n,
    
    // Configuration
    input logic                    error_injection_en,
    input logic [1:0]              inject_resp_type,
    input logic [7:0]              inject_rate,  // 0-255, probability = rate/256
    
    // Exclusive access interface
    input logic                    exclusive_check_req,
    input logic [ID_WIDTH-1:0]     exclusive_check_id,
    input logic                    exclusive_check_pass,
    
    // Memory/slave response
    input logic                    slave_resp_valid,
    input logic [ID_WIDTH-1:0]     slave_resp_id,
    input logic                    slave_resp_error,  // SLVERR indication
    input logic                    slave_resp_is_write,
    
    // Address decode response  
    input logic                    decode_resp_valid,
    input logic [ID_WIDTH-1:0]     decode_resp_id,
    input logic                    decode_resp_hit,
    input logic                    decode_resp_is_write,
    
    // Final response output
    output logic                   resp_valid,
    input logic                    resp_ready,
    output logic [ID_WIDTH-1:0]    resp_id,
    output axi4_resp_t             resp_type,
    output logic                   resp_is_write,
    
    // Statistics
    output logic [31:0]            okay_count,
    output logic [31:0]            exokay_count,
    output logic [31:0]            slverr_count,
    output logic [31:0]            decerr_count
);

    // Response FIFO
    typedef struct packed {
        logic [ID_WIDTH-1:0]    id;
        axi4_resp_t             resp_type;
        logic                   is_write;
    } resp_entry_t;
    
    resp_entry_t resp_fifo[$];
    
    // Random number for error injection
    logic [7:0] rand_num;
    always_ff @(posedge clk) begin
        rand_num <= $random;
    end
    
    // Response generation logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            resp_fifo.delete();
        end else begin
            // Handle exclusive access response
            if (exclusive_check_req) begin
                resp_entry_t entry;
                entry.id = exclusive_check_id;
                entry.resp_type = exclusive_check_pass ? AXI4_RESP_EXOKAY : AXI4_RESP_OKAY;
                entry.is_write = 1'b1;  // Exclusive writes only
                
                // Apply error injection if enabled
                if (error_injection_en && rand_num < inject_rate) begin
                    entry.resp_type = axi4_resp_t'(inject_resp_type);
                end
                
                resp_fifo.push_back(entry);
            end
            
            // Handle decode error response (DECERR)
            if (decode_resp_valid && !decode_resp_hit) begin
                resp_entry_t entry;
                entry.id = decode_resp_id;
                entry.resp_type = AXI4_RESP_DECERR;
                entry.is_write = decode_resp_is_write;
                
                resp_fifo.push_back(entry);
            end
            
            // Handle slave response
            else if (slave_resp_valid) begin
                resp_entry_t entry;
                entry.id = slave_resp_id;
                entry.is_write = slave_resp_is_write;
                
                if (slave_resp_error) begin
                    entry.resp_type = AXI4_RESP_SLVERR;
                end else begin
                    entry.resp_type = AXI4_RESP_OKAY;
                end
                
                // Apply error injection if enabled
                if (error_injection_en && rand_num < inject_rate && !slave_resp_error) begin
                    entry.resp_type = axi4_resp_t'(inject_resp_type);
                end
                
                resp_fifo.push_back(entry);
            end
            
            // Output response
            if (resp_valid && resp_ready && resp_fifo.size() > 0) begin
                resp_fifo.pop_front();
            end
        end
    end
    
    // Output assignment
    always_comb begin
        resp_valid = resp_fifo.size() > 0;
        if (resp_valid) begin
            resp_id = resp_fifo[0].id;
            resp_type = resp_fifo[0].resp_type;
            resp_is_write = resp_fifo[0].is_write;
        end else begin
            resp_id = '0;
            resp_type = AXI4_RESP_OKAY;
            resp_is_write = 1'b0;
        end
    end
    
    // Response statistics
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            okay_count   <= '0;
            exokay_count <= '0;
            slverr_count <= '0;
            decerr_count <= '0;
        end else if (resp_valid && resp_ready) begin
            case (resp_type)
                AXI4_RESP_OKAY:   okay_count   <= okay_count + 1;
                AXI4_RESP_EXOKAY: exokay_count <= exokay_count + 1;
                AXI4_RESP_SLVERR: slverr_count <= slverr_count + 1;
                AXI4_RESP_DECERR: decerr_count <= decerr_count + 1;
            endcase
        end
    end
    
    // Debug output
    `ifdef AXI4_RESP_DEBUG
    always_ff @(posedge clk) begin
        if (resp_valid && resp_ready) begin
            string resp_str;
            case (resp_type)
                AXI4_RESP_OKAY:   resp_str = "OKAY";
                AXI4_RESP_EXOKAY: resp_str = "EXOKAY";
                AXI4_RESP_SLVERR: resp_str = "SLVERR";
                AXI4_RESP_DECERR: resp_str = "DECERR";
            endcase
            $display("[%t] RESPONSE: ID=%0h Type=%s %s",
                     $time, resp_id, resp_str, resp_is_write ? "Write" : "Read");
        end
        
        if (error_injection_en && resp_valid && resp_ready) begin
            if ((resp_type == AXI4_RESP_SLVERR || resp_type == AXI4_RESP_DECERR) &&
                !slave_resp_error && decode_resp_hit) begin
                $display("[%t] RESPONSE: Error injected!", $time);
            end
        end
    end
    `endif
    
    // Assertions
    `ifdef AXI4_RESP_CHECK
    // Check EXOKAY only for exclusive access
    property exokay_only_exclusive;
        @(posedge clk) disable iff (!rst_n)
        (resp_valid && resp_type == AXI4_RESP_EXOKAY) |->
        $past(exclusive_check_req && exclusive_check_pass);
    endproperty
    
    assert property (exokay_only_exclusive)
        else $error("EXOKAY response without successful exclusive access");
    
    // Check response ordering
    property resp_ordering;
        @(posedge clk) disable iff (!rst_n)
        resp_valid && !resp_ready |=> resp_valid && $stable(resp_id) && $stable(resp_type);
    endproperty
    
    assert property (resp_ordering)
        else $error("Response changed while waiting for ready");
    `endif
    
    // Coverage
    `ifdef AXI4_COVERAGE
    covergroup resp_coverage_cg @(posedge clk iff (resp_valid && resp_ready));
        resp_type_cp: coverpoint resp_type {
            bins okay   = {AXI4_RESP_OKAY};
            bins exokay = {AXI4_RESP_EXOKAY};
            bins slverr = {AXI4_RESP_SLVERR};
            bins decerr = {AXI4_RESP_DECERR};
        }
        
        write_read_cp: coverpoint resp_is_write {
            bins write = {1};
            bins read  = {0};
        }
        
        cross_resp_type: cross resp_type_cp, write_read_cp {
            // EXOKAY is only for writes
            illegal_bins exokay_read = binsof(resp_type_cp.exokay) && binsof(write_read_cp.read);
        }
        
        error_injection_cp: coverpoint error_injection_en {
            bins disabled = {0};
            bins enabled  = {1};
        }
    endgroup
    
    resp_coverage_cg resp_cov = new();
    `endif
    
endmodule : axi4_response_handler