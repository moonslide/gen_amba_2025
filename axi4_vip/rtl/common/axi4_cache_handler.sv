//==============================================================================
// AXI4 Cache Attribute Handler
// 
// Description: Handles AxCACHE attributes for transaction modification
// Supports modifiable/non-modifiable transactions and buffering
//==============================================================================

`include "axi4_defines.sv"

module axi4_cache_handler #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64,
    parameter int ID_WIDTH = 4,
    parameter int MAX_PENDING = 16
)(
    input logic                    clk,
    input logic                    rst_n,
    
    // Configuration
    input logic                    enable_merging,
    input logic                    enable_splitting,
    input logic                    enable_buffering,
    
    // Input transaction
    input logic                    in_valid,
    output logic                   in_ready,
    input logic [ID_WIDTH-1:0]     in_id,
    input logic [ADDR_WIDTH-1:0]   in_addr,
    input logic [7:0]              in_len,
    input logic [2:0]              in_size,
    input logic [1:0]              in_burst,
    input axi4_cache_t             in_cache,
    input logic                    in_write,
    
    // Output transaction(s)
    output logic                   out_valid,
    input logic                    out_ready,
    output logic [ID_WIDTH-1:0]    out_id,
    output logic [ADDR_WIDTH-1:0]  out_addr,
    output logic [7:0]             out_len,
    output logic [2:0]             out_size,
    output logic [1:0]             out_burst,
    output axi4_cache_t            out_cache,
    output logic                   out_write,
    
    // Early response for bufferable writes
    output logic                   early_resp_valid,
    output logic [ID_WIDTH-1:0]    early_resp_id,
    input logic                    early_resp_ready
);

    // Transaction buffer for pending operations
    typedef struct packed {
        logic                    valid;
        logic [ID_WIDTH-1:0]     id;
        logic [ADDR_WIDTH-1:0]   addr;
        logic [7:0]              len;
        logic [2:0]              size;
        logic [1:0]              burst;
        axi4_cache_t             cache;
        logic                    write;
        logic                    buffered;  // Early response sent
    } trans_entry_t;
    
    trans_entry_t trans_buffer[MAX_PENDING];
    logic [$clog2(MAX_PENDING)-1:0] wr_ptr, rd_ptr;
    logic buffer_full, buffer_empty;
    
    // Buffer control
    assign buffer_empty = (wr_ptr == rd_ptr) && !trans_buffer[rd_ptr].valid;
    assign buffer_full = (wr_ptr == rd_ptr) && trans_buffer[wr_ptr].valid;
    
    // Input acceptance
    assign in_ready = !buffer_full;
    
    // Transaction processing state machine
    typedef enum logic [2:0] {
        IDLE,
        CHECK_MERGE,
        SPLIT_TRANS,
        FORWARD,
        BUFFER_RESP
    } state_t;
    
    state_t state, next_state;
    
    // State machine
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end
    
    // Next state logic
    always_comb begin
        next_state = state;
        
        case (state)
            IDLE: begin
                if (in_valid && in_ready) begin
                    if (in_cache.modifiable && (enable_merging || enable_splitting)) begin
                        next_state = CHECK_MERGE;
                    end else if (in_cache.bufferable && in_write && enable_buffering) begin
                        next_state = BUFFER_RESP;
                    end else begin
                        next_state = FORWARD;
                    end
                end
            end
            
            CHECK_MERGE: begin
                // Simplified - just forward for now
                next_state = FORWARD;
            end
            
            SPLIT_TRANS: begin
                // Simplified - just forward for now
                next_state = FORWARD;
            end
            
            FORWARD: begin
                if (out_valid && out_ready) begin
                    next_state = IDLE;
                end
            end
            
            BUFFER_RESP: begin
                if (early_resp_valid && early_resp_ready) begin
                    next_state = FORWARD;
                end
            end
        endcase
    end
    
    // Buffer write
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < MAX_PENDING; i++) begin
                trans_buffer[i] <= '0;
            end
            wr_ptr <= '0;
        end else begin
            if (in_valid && in_ready) begin
                trans_buffer[wr_ptr].valid    <= 1'b1;
                trans_buffer[wr_ptr].id       <= in_id;
                trans_buffer[wr_ptr].addr     <= in_addr;
                trans_buffer[wr_ptr].len      <= in_len;
                trans_buffer[wr_ptr].size     <= in_size;
                trans_buffer[wr_ptr].burst    <= in_burst;
                trans_buffer[wr_ptr].cache    <= in_cache;
                trans_buffer[wr_ptr].write    <= in_write;
                trans_buffer[wr_ptr].buffered <= 1'b0;
                
                wr_ptr <= (wr_ptr + 1) % MAX_PENDING;
            end
        end
    end
    
    // Buffer read and output generation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_valid <= 1'b0;
            out_id <= '0;
            out_addr <= '0;
            out_len <= '0;
            out_size <= '0;
            out_burst <= '0;
            out_cache <= '0;
            out_write <= '0;
            early_resp_valid <= 1'b0;
            early_resp_id <= '0;
            rd_ptr <= '0;
        end else begin
            // Clear handshakes
            if (out_valid && out_ready) begin
                out_valid <= 1'b0;
                trans_buffer[rd_ptr].valid <= 1'b0;
                rd_ptr <= (rd_ptr + 1) % MAX_PENDING;
            end
            
            if (early_resp_valid && early_resp_ready) begin
                early_resp_valid <= 1'b0;
                trans_buffer[rd_ptr].buffered <= 1'b1;
            end
            
            // Process transactions
            if (!buffer_empty && !out_valid && state == FORWARD) begin
                trans_entry_t entry = trans_buffer[rd_ptr];
                
                // Check for modifications based on cache attributes
                if (entry.cache.modifiable) begin
                    // For modifiable transactions, we could:
                    // 1. Merge multiple small writes
                    // 2. Split large bursts
                    // 3. Prefetch additional data
                    // For now, just forward as-is
                end
                
                out_valid <= 1'b1;
                out_id    <= entry.id;
                out_addr  <= entry.addr;
                out_len   <= entry.len;
                out_size  <= entry.size;
                out_burst <= entry.burst;
                out_cache <= entry.cache;
                out_write <= entry.write;
            end
            
            // Generate early response for bufferable writes
            if (!buffer_empty && !early_resp_valid && state == BUFFER_RESP) begin
                trans_entry_t entry = trans_buffer[rd_ptr];
                
                if (entry.cache.bufferable && entry.write && !entry.buffered) begin
                    early_resp_valid <= 1'b1;
                    early_resp_id <= entry.id;
                end
            end
        end
    end
    
    // Cache attribute validation
    always_comb begin
        // Non-modifiable transaction checks
        if (in_valid && !in_cache.modifiable) begin
            // These transactions must not be modified
            assert (!enable_merging || !in_cache.modifiable) 
                else $error("Cannot merge non-modifiable transaction");
            assert (!enable_splitting || !in_cache.modifiable || 
                    (in_burst == AXI4_BURST_INCR && in_len > 15))
                else $error("Cannot split non-modifiable transaction");
        end
    end
    
    // Performance counters
    logic [31:0] modifiable_count;
    logic [31:0] bufferable_count;
    logic [31:0] merge_count;
    logic [31:0] split_count;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            modifiable_count <= '0;
            bufferable_count <= '0;
            merge_count <= '0;
            split_count <= '0;
        end else begin
            if (in_valid && in_ready) begin
                if (in_cache.modifiable) modifiable_count <= modifiable_count + 1;
                if (in_cache.bufferable) bufferable_count <= bufferable_count + 1;
            end
            // Increment merge/split counters when implemented
        end
    end
    
    // Debug
    `ifdef AXI4_CACHE_DEBUG
    always_ff @(posedge clk) begin
        if (in_valid && in_ready) begin
            $display("[%t] CACHE_HANDLER: Trans ID=%0h Addr=%0h Cache=%b%b%b%b",
                     $time, in_id, in_addr,
                     in_cache.allocate, in_cache.other_alloc,
                     in_cache.modifiable, in_cache.bufferable);
        end
        
        if (early_resp_valid) begin
            $display("[%t] CACHE_HANDLER: Early response for bufferable write ID=%0h",
                     $time, early_resp_id);
        end
    end
    `endif
    
endmodule : axi4_cache_handler