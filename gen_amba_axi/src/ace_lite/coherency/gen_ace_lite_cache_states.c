//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite MOESI Cache State Management Implementation
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "../../gen_amba_axi.h"
#include "../../gen_axi_utils.h"

//--------------------------------------------------------
// Generate MOESI cache state management logic
// Supports 5-state cache coherency: Modified, Owned, Exclusive, Shared, Invalid
//--------------------------------------------------------
int gen_ace_lite_cache_states(unsigned int numM, unsigned int numS, 
                              char *prefix, axi_features_t *features, FILE *fo)
{
    int i, j;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite MOESI Cache State Management\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %sace_lite_cache_states\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , CACHE_LINE_ENTRIES = 1024)  // Number of cache lines to track\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                    clk\n");
    fprintf(fo, "    , input  wire                    rst_n\n");
    
    // Add master interface connections for cache state tracking
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d cache state interface\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]    m%d_addr          // Address for state lookup\n", i);
        fprintf(fo, "    , input  wire                   m%d_state_req     // State query request\n", i);
        fprintf(fo, "    , input  wire [2:0]             m%d_new_state     // New cache state to set\n", i);
        fprintf(fo, "    , input  wire                   m%d_state_update  // Update cache state\n", i);
        fprintf(fo, "    , output reg  [2:0]             m%d_current_state // Current cache state\n", i);
        fprintf(fo, "    , output reg                    m%d_state_valid   // State lookup valid\n", i);
    }
    
    fprintf(fo, "    // Global cache state monitoring outputs\n");
    fprintf(fo, "    , output reg  [31:0]            cache_hits         // Total cache hits\n");
    fprintf(fo, "    , output reg  [31:0]            cache_misses       // Total cache misses\n");
    fprintf(fo, "    , output reg  [31:0]            state_transitions  // Total state transitions\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0] coherency_conflict // Coherency conflicts per master\n");
    fprintf(fo, ");\n\n");
    
    // MOESI state definitions
    fprintf(fo, "    // MOESI Cache State Encodings\n");
    fprintf(fo, "    localparam [2:0] STATE_INVALID   = 3'b000;  // I - Invalid (not cached)\n");
    fprintf(fo, "    localparam [2:0] STATE_SHARED    = 3'b001;  // S - Shared (read-only, may be in other caches)\n");
    fprintf(fo, "    localparam [2:0] STATE_EXCLUSIVE = 3'b010;  // E - Exclusive (read-only, only copy)\n");
    fprintf(fo, "    localparam [2:0] STATE_OWNED     = 3'b011;  // O - Owned (dirty, shared with others)\n");
    fprintf(fo, "    localparam [2:0] STATE_MODIFIED  = 3'b100;  // M - Modified (dirty, only copy)\n");
    fprintf(fo, "    localparam [2:0] STATE_RESERVED1 = 3'b101;  // Reserved for future use\n");
    fprintf(fo, "    localparam [2:0] STATE_RESERVED2 = 3'b110;  // Reserved for future use\n");
    fprintf(fo, "    localparam [2:0] STATE_ERROR     = 3'b111;  // Error state\n\n");
    
    // Cache line tracking structure
    fprintf(fo, "    // Cache Line State Tracking\n");
    fprintf(fo, "    // Each cache line tracks: address tag, state per master, LRU info\n");
    fprintf(fo, "    reg [WIDTH_AD-7:0] cache_tag [CACHE_LINE_ENTRIES-1:0];     // Address tag (excluding lower 6 bits)\n");
    fprintf(fo, "    reg [2:0]          cache_state [CACHE_LINE_ENTRIES-1:0][NUM_MASTER-1:0]; // State per master\n");
    fprintf(fo, "    reg                cache_valid [CACHE_LINE_ENTRIES-1:0];   // Valid cache line\n");
    fprintf(fo, "    reg [7:0]          cache_lru [CACHE_LINE_ENTRIES-1:0];     // LRU counter (0=most recent)\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] cache_owner [CACHE_LINE_ENTRIES-1:0]; // Master that owns this line\n");
    fprintf(fo, "\n");
    
    // Internal signals
    fprintf(fo, "    // Internal Cache Management Signals\n");
    fprintf(fo, "    reg [9:0] cache_index [NUM_MASTER-1:0];     // Cache index for each master\n");
    fprintf(fo, "    reg       cache_hit [NUM_MASTER-1:0];       // Cache hit indicator\n");
    fprintf(fo, "    reg [9:0] victim_index;                     // Index for cache replacement\n");
    fprintf(fo, "    reg       replacement_needed;               // Need to replace cache line\n");
    fprintf(fo, "    \n");
    
    // Cache lookup logic
    fprintf(fo, "    // Cache Lookup Logic\n");
    fprintf(fo, "    // Determines cache index and hit/miss for each master\n");
    fprintf(fo, "    integer k;\n");
    fprintf(fo, "    always @(*) begin\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        // Master %d cache lookup\n", i);
        fprintf(fo, "        cache_index[%d] = m%d_addr[15:6];  // Use middle bits for index\n", i, i);
        fprintf(fo, "        cache_hit[%d] = 1'b0;\n", i);
        fprintf(fo, "        m%d_current_state = STATE_INVALID;\n", i);
        fprintf(fo, "        m%d_state_valid = 1'b0;\n", i);
        fprintf(fo, "        \n");
        fprintf(fo, "        if (m%d_state_req) begin\n", i);
        fprintf(fo, "            for (k = 0; k < CACHE_LINE_ENTRIES; k = k + 1) begin\n");
        fprintf(fo, "                if (cache_valid[k] && \n");
        fprintf(fo, "                    (cache_tag[k] == m%d_addr[WIDTH_AD-1:6])) begin\n", i);
        fprintf(fo, "                    cache_hit[%d] = 1'b1;\n", i);
        fprintf(fo, "                    cache_index[%d] = k[9:0];\n", i);
        fprintf(fo, "                    m%d_current_state = cache_state[k][%d];\n", i, i);
        fprintf(fo, "                    m%d_state_valid = 1'b1;\n", i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "        \n");
    }
    
    fprintf(fo, "    end\n\n");
    
    // LRU victim selection logic
    fprintf(fo, "    // LRU Victim Selection Logic\n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        victim_index = 10'h000;\n");
    fprintf(fo, "        replacement_needed = 1'b0;\n");
    fprintf(fo, "        \n");
    fprintf(fo, "        // Find invalid entry first\n");
    fprintf(fo, "        for (k = 0; k < CACHE_LINE_ENTRIES; k = k + 1) begin\n");
    fprintf(fo, "            if (!cache_valid[k]) begin\n");
    fprintf(fo, "                victim_index = k[9:0];\n");
    fprintf(fo, "                replacement_needed = 1'b0;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "        \n");
    fprintf(fo, "        // If no invalid entries, find LRU\n");
    fprintf(fo, "        if (replacement_needed) begin\n");
    fprintf(fo, "            for (k = 0; k < CACHE_LINE_ENTRIES; k = k + 1) begin\n");
    fprintf(fo, "                if (cache_lru[k] == 8'hFF) begin  // Oldest LRU\n");
    fprintf(fo, "                    victim_index = k[9:0];\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // State transition logic
    fprintf(fo, "    // Cache State Update Logic\n");
    fprintf(fo, "    // Implements MOESI protocol state transitions\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            // Reset all cache states\n");
    fprintf(fo, "            for (k = 0; k < CACHE_LINE_ENTRIES; k = k + 1) begin\n");
    fprintf(fo, "                cache_valid[k] <= 1'b0;\n");
    fprintf(fo, "                cache_tag[k] <= {(WIDTH_AD-6){1'b0}};\n");
    fprintf(fo, "                cache_lru[k] <= 8'h00;\n");
    fprintf(fo, "                cache_owner[k] <= {NUM_MASTER{1'b0}};\n");
    
    for (j = 0; j < numM; j++) {
        fprintf(fo, "                cache_state[k][%d] <= STATE_INVALID;\n", j);
    }
    
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Reset statistics\n");
    fprintf(fo, "            cache_hits <= 32'h00000000;\n");
    fprintf(fo, "            cache_misses <= 32'h00000000;\n");
    fprintf(fo, "            state_transitions <= 32'h00000000;\n");
    fprintf(fo, "            coherency_conflict <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            \n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            // Update LRU counters (age all entries)\n");
    fprintf(fo, "            for (k = 0; k < CACHE_LINE_ENTRIES; k = k + 1) begin\n");
    fprintf(fo, "                if (cache_valid[k] && cache_lru[k] < 8'hFF) begin\n");
    fprintf(fo, "                    cache_lru[k] <= cache_lru[k] + 1;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    
    // Process state updates for each master
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d state update processing\n", i);
        fprintf(fo, "            if (m%d_state_update) begin\n", i);
        fprintf(fo, "                if (cache_hit[%d]) begin\n", i);
        fprintf(fo, "                    // Update existing cache line\n");
        fprintf(fo, "                    cache_state[cache_index[%d]][%d] <= m%d_new_state;\n", i, i, i);
        fprintf(fo, "                    cache_lru[cache_index[%d]] <= 8'h00;  // Mark as most recent\n", i);
        fprintf(fo, "                    cache_hits <= cache_hits + 1;\n");
        fprintf(fo, "                    state_transitions <= state_transitions + 1;\n");
        fprintf(fo, "                    \n");
        fprintf(fo, "                    // Check for coherency conflicts\n");
        fprintf(fo, "                    if (m%d_new_state == STATE_MODIFIED || m%d_new_state == STATE_EXCLUSIVE) begin\n", i, i);
        fprintf(fo, "                        for (k = 0; k < NUM_MASTER; k = k + 1) begin\n");
        fprintf(fo, "                            if (k != %d && cache_state[cache_index[%d]][k] != STATE_INVALID) begin\n", i, i);
        fprintf(fo, "                                coherency_conflict[%d] <= 1'b1;\n", i);
        fprintf(fo, "                                // Invalidate other masters' copies\n");
        fprintf(fo, "                                cache_state[cache_index[%d]][k] <= STATE_INVALID;\n", i);
        fprintf(fo, "                            end\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    \n");
        fprintf(fo, "                end else begin\n");
        fprintf(fo, "                    // Allocate new cache line\n");
        fprintf(fo, "                    cache_valid[victim_index] <= 1'b1;\n");
        fprintf(fo, "                    cache_tag[victim_index] <= m%d_addr[WIDTH_AD-1:6];\n", i);
        fprintf(fo, "                    cache_state[victim_index][%d] <= m%d_new_state;\n", i, i);
        fprintf(fo, "                    cache_lru[victim_index] <= 8'h00;\n");
        fprintf(fo, "                    cache_owner[victim_index][%d] <= 1'b1;\n", i);
        fprintf(fo, "                    cache_misses <= cache_misses + 1;\n");
        fprintf(fo, "                    state_transitions <= state_transitions + 1;\n");
        fprintf(fo, "                    \n");
        fprintf(fo, "                    // Clear other masters' ownership of this line\n");
        fprintf(fo, "                    for (k = 0; k < NUM_MASTER; k = k + 1) begin\n");
        fprintf(fo, "                        if (k != %d) begin\n", i);
        fprintf(fo, "                            cache_state[victim_index][k] <= STATE_INVALID;\n");
        fprintf(fo, "                            cache_owner[victim_index][k] <= 1'b0;\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Clear coherency conflict flag after one cycle\n");
        fprintf(fo, "            coherency_conflict[%d] <= 1'b0;\n", i);
        fprintf(fo, "            \n");
    }
    
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // State transition validation logic
    fprintf(fo, "    // MOESI Protocol State Transition Validation\n");
    fprintf(fo, "    // Ensures only valid MOESI transitions occur\n");
    fprintf(fo, "    function automatic logic valid_transition;\n");
    fprintf(fo, "        input [2:0] current_state;\n");
    fprintf(fo, "        input [2:0] new_state;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            case (current_state)\n");
    fprintf(fo, "                STATE_INVALID: begin\n");
    fprintf(fo, "                    // From Invalid: can go to any state except Owned\n");
    fprintf(fo, "                    valid_transition = (new_state != STATE_OWNED);\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                STATE_SHARED: begin\n");
    fprintf(fo, "                    // From Shared: can go to Invalid, Exclusive, or Modified\n");
    fprintf(fo, "                    valid_transition = (new_state == STATE_INVALID) || \n");
    fprintf(fo, "                                     (new_state == STATE_EXCLUSIVE) || \n");
    fprintf(fo, "                                     (new_state == STATE_MODIFIED);\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                STATE_EXCLUSIVE: begin\n");
    fprintf(fo, "                    // From Exclusive: can go to Invalid, Shared, or Modified\n");
    fprintf(fo, "                    valid_transition = (new_state == STATE_INVALID) || \n");
    fprintf(fo, "                                     (new_state == STATE_SHARED) || \n");
    fprintf(fo, "                                     (new_state == STATE_MODIFIED);\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                STATE_OWNED: begin\n");
    fprintf(fo, "                    // From Owned: can go to Invalid or Modified\n");
    fprintf(fo, "                    valid_transition = (new_state == STATE_INVALID) || \n");
    fprintf(fo, "                                     (new_state == STATE_MODIFIED);\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                STATE_MODIFIED: begin\n");
    fprintf(fo, "                    // From Modified: can go to Invalid, Shared, or Owned\n");
    fprintf(fo, "                    valid_transition = (new_state == STATE_INVALID) || \n");
    fprintf(fo, "                                     (new_state == STATE_SHARED) || \n");
    fprintf(fo, "                                     (new_state == STATE_OWNED);\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                default: begin\n");
    fprintf(fo, "                    valid_transition = 1'b0;  // Invalid current state\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            endcase\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    fprintf(fo, "endmodule\n\n");
    
    return 0;
}