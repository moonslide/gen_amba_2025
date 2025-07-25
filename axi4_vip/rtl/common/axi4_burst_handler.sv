//==============================================================================
// AXI4 Burst Handler
// 
// Description: Handles burst address generation and 4KB boundary checking
// Supports FIXED, INCR, and WRAP burst types
//==============================================================================

`include "axi4_defines.sv"

module axi4_burst_handler #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64
)(
    input logic                    clk,
    input logic                    rst_n,
    
    // Burst configuration
    input logic                    burst_start,
    input logic [ADDR_WIDTH-1:0]   start_addr,
    input logic [7:0]              burst_len,    // 0-255 (actual length - 1)
    input logic [2:0]              burst_size,   // 2^size bytes per beat
    input axi4_burst_t             burst_type,
    
    // Address generation
    input logic                    addr_req,
    output logic                   addr_valid,
    output logic [ADDR_WIDTH-1:0]  addr_out,
    output logic                   addr_last,
    output logic [7:0]             beat_count,
    
    // Error flags
    output logic                   burst_4kb_error,
    output logic                   burst_align_error,
    output logic                   burst_wrap_error
);

    // Internal state
    logic [ADDR_WIDTH-1:0]         current_addr;
    logic [7:0]                    remaining_beats;
    logic                          burst_active;
    logic [ADDR_WIDTH-1:0]         bytes_per_beat;
    logic [ADDR_WIDTH-1:0]         total_bytes;
    logic [ADDR_WIDTH-1:0]         wrap_boundary;
    logic [ADDR_WIDTH-1:0]         upper_wrap_boundary;
    
    // Calculate derived values
    always_comb begin
        bytes_per_beat = 1 << burst_size;
        total_bytes = (burst_len + 1) * bytes_per_beat;
        
        // WRAP boundary calculation
        if (burst_type == AXI4_BURST_WRAP) begin
            wrap_boundary = (start_addr / total_bytes) * total_bytes;
            upper_wrap_boundary = wrap_boundary + total_bytes;
        end else begin
            wrap_boundary = '0;
            upper_wrap_boundary = '0;
        end
    end
    
    // Burst validation
    always_comb begin
        burst_4kb_error = 1'b0;
        burst_align_error = 1'b0;
        burst_wrap_error = 1'b0;
        
        if (burst_start) begin
            // Check 4KB boundary crossing
            logic [ADDR_WIDTH-1:0] end_addr = start_addr + total_bytes - 1;
            if (start_addr[31:12] != end_addr[31:12]) begin
                burst_4kb_error = 1'b1;
            end
            
            // Check alignment
            if ((start_addr & (bytes_per_beat - 1)) != 0) begin
                burst_align_error = 1'b1;
            end
            
            // Check WRAP constraints
            if (burst_type == AXI4_BURST_WRAP) begin
                // Length must be 2, 4, 8, or 16
                if (burst_len != 1 && burst_len != 3 && 
                    burst_len != 7 && burst_len != 15) begin
                    burst_wrap_error = 1'b1;
                end
                
                // Start address must be aligned to size
                if ((start_addr & (total_bytes - 1)) != 0) begin
                    burst_align_error = 1'b1;
                end
            end
        end
    end
    
    // Burst state machine
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            burst_active <= 1'b0;
            current_addr <= '0;
            remaining_beats <= '0;
            beat_count <= '0;
        end else begin
            if (burst_start && !burst_active) begin
                burst_active <= 1'b1;
                current_addr <= start_addr;
                remaining_beats <= burst_len;
                beat_count <= '0;
            end else if (burst_active && addr_req && addr_valid) begin
                beat_count <= beat_count + 1;
                
                if (remaining_beats == 0) begin
                    burst_active <= 1'b0;
                end else begin
                    remaining_beats <= remaining_beats - 1;
                    
                    // Address increment based on burst type
                    case (burst_type)
                        AXI4_BURST_FIXED: begin
                            // Address remains constant
                            current_addr <= current_addr;
                        end
                        
                        AXI4_BURST_INCR: begin
                            // Incrementing address
                            current_addr <= current_addr + bytes_per_beat;
                        end
                        
                        AXI4_BURST_WRAP: begin
                            // Wrapping address
                            logic [ADDR_WIDTH-1:0] next_addr = current_addr + bytes_per_beat;
                            
                            if (next_addr >= upper_wrap_boundary) begin
                                current_addr <= wrap_boundary;
                            end else begin
                                current_addr <= next_addr;
                            end
                        end
                        
                        default: begin
                            // Reserved - treat as INCR
                            current_addr <= current_addr + bytes_per_beat;
                        end
                    endcase
                end
            end
        end
    end
    
    // Output assignments
    assign addr_valid = burst_active;
    assign addr_out = current_addr;
    assign addr_last = burst_active && (remaining_beats == 0);
    
    // Detailed address calculation functions for verification
    function automatic logic [ADDR_WIDTH-1:0] calc_incr_addr(
        input logic [ADDR_WIDTH-1:0] base_addr,
        input int beat_num,
        input logic [2:0] size
    );
        return base_addr + (beat_num * (1 << size));
    endfunction
    
    function automatic logic [ADDR_WIDTH-1:0] calc_wrap_addr(
        input logic [ADDR_WIDTH-1:0] base_addr,
        input int beat_num,
        input logic [2:0] size,
        input logic [7:0] len
    );
        logic [ADDR_WIDTH-1:0] bytes_per_beat = 1 << size;
        logic [ADDR_WIDTH-1:0] total_bytes = (len + 1) * bytes_per_beat;
        logic [ADDR_WIDTH-1:0] wrap_boundary = (base_addr / total_bytes) * total_bytes;
        logic [ADDR_WIDTH-1:0] offset = (base_addr + beat_num * bytes_per_beat) - wrap_boundary;
        
        return wrap_boundary + (offset % total_bytes);
    endfunction
    
    // Debug and monitoring
    `ifdef AXI4_BURST_DEBUG
    always_ff @(posedge clk) begin
        if (burst_start) begin
            $display("[%t] BURST_HANDLER: Start burst - Addr=%0h Len=%0d Size=%0d Type=%0s",
                     $time, start_addr, burst_len+1, burst_size,
                     burst_type == AXI4_BURST_FIXED ? "FIXED" :
                     burst_type == AXI4_BURST_INCR  ? "INCR"  :
                     burst_type == AXI4_BURST_WRAP  ? "WRAP"  : "RSVD");
                     
            if (burst_4kb_error) $display("[%t] BURST_HANDLER: ERROR - Burst crosses 4KB boundary!", $time);
            if (burst_align_error) $display("[%t] BURST_HANDLER: ERROR - Burst not aligned!", $time);
            if (burst_wrap_error) $display("[%t] BURST_HANDLER: ERROR - Invalid WRAP burst!", $time);
        end
        
        if (addr_req && addr_valid) begin
            $display("[%t] BURST_HANDLER: Beat %0d - Addr=%0h %s",
                     $time, beat_count, addr_out, addr_last ? "(LAST)" : "");
        end
    end
    `endif
    
    // Assertions
    `ifdef AXI4_BURST_CHECK
    // No 4KB crossing for any burst
    property no_4kb_cross;
        @(posedge clk) disable iff (!rst_n)
        burst_start |-> !burst_4kb_error;
    endproperty
    
    assert property (no_4kb_cross)
        else $error("Burst crosses 4KB boundary");
    
    // Valid WRAP lengths
    property valid_wrap_len;
        @(posedge clk) disable iff (!rst_n)
        (burst_start && burst_type == AXI4_BURST_WRAP) |-> !burst_wrap_error;
    endproperty
    
    assert property (valid_wrap_len)
        else $error("Invalid WRAP burst length");
    
    // Address alignment
    property addr_aligned;
        @(posedge clk) disable iff (!rst_n)
        burst_start |-> !burst_align_error;
    endproperty
    
    assert property (addr_aligned)
        else $error("Burst address not aligned");
    
    // Beat count accuracy
    property beat_count_check;
        @(posedge clk) disable iff (!rst_n)
        (addr_valid && addr_last) |-> (beat_count == burst_len);
    endproperty
    
    assert property (beat_count_check)
        else $error("Beat count mismatch");
    `endif
    
endmodule : axi4_burst_handler