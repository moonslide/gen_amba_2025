//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite Snoop Filter Module Generator
// Address-based coherency filtering and snoop management
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "../../gen_amba_axi.h"
#include "../../gen_axi_utils.h"
#include "../../gen_axi_validation.h"

//--------------------------------------------------------
// Generate ACE-Lite snoop filter module
//--------------------------------------------------------
int gen_ace_lite_snoop_filter(unsigned int numM, unsigned int numS,
                              unsigned int widthAD, unsigned int widthDA,
                              char *prefix, axi_features_t *features, FILE *fo)
{
    int i, j;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    // Register key signals for validation
    char module_name[128];
    snprintf(module_name, sizeof(module_name), "%sace_lite_snoop_filter", prefix);
    register_signal_width("conflict_count", "CONFLICT_COUNT_WIDTH-1:0", "output", module_name, __LINE__);
    register_signal_width("snoop_required", "NUM_MASTER-1:0", "output", module_name, __LINE__);
    register_signal_width("invalidate_required", "NUM_MASTER-1:0", "output", module_name, __LINE__);
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite Snoop Filter\n");
    fprintf(fo, "// Address-based coherency filtering and snoop request management\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %sace_lite_snoop_filter\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , SNOOP_FILTER_DEPTH = 128\n");
    fprintf(fo, "              , CACHELINE_SIZE = 64 // Cache line size in bytes\n");
    fprintf(fo, "              // Parameterized conflict counter width - scales with master count\n");
    fprintf(fo, "              , CONFLICT_COUNT_WIDTH = (NUM_MASTER <= 2) ? 2 : (NUM_MASTER <= 8) ? 4 : (NUM_MASTER <= 16) ? 5 : (NUM_MASTER <= 32) ? 6 : 8)\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                       clk\n");
    fprintf(fo, "    , input  wire                       rst_n\n");
    
    // Master interface inputs for address monitoring
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d snoop interface\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]       m%d_awaddr\n", i);
        fprintf(fo, "    , input  wire [1:0]                m%d_awdomain\n", i);
        fprintf(fo, "    , input  wire [2:0]                m%d_awsnoop\n", i);
        fprintf(fo, "    , input  wire                      m%d_awvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_awready\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]       m%d_araddr\n", i);
        fprintf(fo, "    , input  wire [1:0]                m%d_ardomain\n", i);
        fprintf(fo, "    , input  wire [3:0]                m%d_arsnoop\n", i);
        fprintf(fo, "    , input  wire                      m%d_arvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_arready\n", i);
    }
    
    // Snoop filter control inputs
    fprintf(fo, "    // Snoop filter control\n");
    fprintf(fo, "    , input  wire                       snoop_filter_enable\n");
    fprintf(fo, "    , input  wire                       snoop_filter_bypass\n");
    fprintf(fo, "    , input  wire [WIDTH_AD-1:0]        snoop_base_addr\n");
    fprintf(fo, "    , input  wire [WIDTH_AD-1:0]        snoop_addr_mask\n");
    
    // Snoop filter outputs
    fprintf(fo, "    // Snoop filter outputs\n");
    fprintf(fo, "    , output wire [NUM_MASTER-1:0]       snoop_required\n");
    fprintf(fo, "    , output wire [NUM_MASTER-1:0]       snoop_block\n");
    fprintf(fo, "    , output reg  [WIDTH_AD-1:0]         snoop_target_addr\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       snoop_target_masters\n");
    fprintf(fo, "    , output wire [7:0]                  filter_hit_count\n");
    fprintf(fo, "    , output wire [7:0]                  filter_miss_count\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Enhanced write-invalidate protocol outputs\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       invalidate_required\n");
    fprintf(fo, "    , output reg  [WIDTH_AD-1:0]         invalidate_addr\n");
    fprintf(fo, "    , output reg  [2:0]                  invalidate_type\n");
    fprintf(fo, "    , output wire                        invalidate_valid\n");
    fprintf(fo, "    , input  wire                        invalidate_ready\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Snoop response aggregation inputs\n");
    for (int k = 0; k < numM; k++) {
        fprintf(fo, "    , input  wire [4:0]              m%d_crresp\n", k);
        fprintf(fo, "    , input  wire                    m%d_crvalid\n", k);
        fprintf(fo, "    , output wire                    m%d_crready\n", k);
    }
    fprintf(fo, "    \n");
    fprintf(fo, "    // Write conflict detection outputs\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       conflict_detected\n");
    fprintf(fo, "    , output reg  [WIDTH_AD-1:0]         conflict_addr\n");
    fprintf(fo, "    , output wire [CONFLICT_COUNT_WIDTH-1:0] conflict_count\n");
    
    fprintf(fo, ");\n\n");
    
    // Parameter definitions
    fprintf(fo, "    // Snoop filter parameters\n");
    fprintf(fo, "    localparam CACHELINE_OFFSET_BITS = $clog2(CACHELINE_SIZE);\n");
    fprintf(fo, "    localparam TAG_BITS = WIDTH_AD - CACHELINE_OFFSET_BITS;\n");
    fprintf(fo, "    localparam FILTER_INDEX_BITS = $clog2(SNOOP_FILTER_DEPTH);\n\n");
    
    // Domain encodings
    fprintf(fo, "    // Domain encodings\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_NON_SHAREABLE = 2'b00;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_INNER_SHAREABLE = 2'b01;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_OUTER_SHAREABLE = 2'b10;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_SYSTEM = 2'b11;\n\n");
    
    // Snoop encodings
    fprintf(fo, "    // Write snoop types requiring filtering\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_NO_SNOOP = 3'b000;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_LINE_UNIQUE = 3'b001;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_CLEAN = 3'b010;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_EVICT = 3'b100;\n\n");
    
    fprintf(fo, "    // Read snoop types requiring filtering\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_NO_SNOOP = 4'b0000;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_SHARED = 4'b0001;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_CLEAN = 4'b0010;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_UNIQUE = 4'b0111;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_CLEAN_UNIQUE = 4'b1011;\n\n");
    
    // Snoop filter table structure
    fprintf(fo, "    // Snoop filter table - tracks coherent cache lines\n");
    fprintf(fo, "    reg [TAG_BITS-1:0] filter_tag_table [0:SNOOP_FILTER_DEPTH-1];\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] filter_master_table [0:SNOOP_FILTER_DEPTH-1]; // Masters with this line\n");
    fprintf(fo, "    reg [1:0] filter_state_table [0:SNOOP_FILTER_DEPTH-1]; // Line state\n");
    fprintf(fo, "    reg [SNOOP_FILTER_DEPTH-1:0] filter_valid;\n");
    fprintf(fo, "    reg [$clog2(SNOOP_FILTER_DEPTH)-1:0] filter_lru_ptr;\n\n");
    
    // Filter state encodings
    fprintf(fo, "    // Cache line state encodings\n");
    fprintf(fo, "    localparam [1:0] LINE_INVALID = 2'b00;\n");
    fprintf(fo, "    localparam [1:0] LINE_SHARED = 2'b01;\n");
    fprintf(fo, "    localparam [1:0] LINE_UNIQUE = 2'b10;\n");
    fprintf(fo, "    localparam [1:0] LINE_DIRTY = 2'b11;\n\n");
    
    // Performance counters
    fprintf(fo, "    // Performance monitoring\n");
    fprintf(fo, "    reg [7:0] hit_counter;\n");
    fprintf(fo, "    reg [7:0] miss_counter;\n");
    fprintf(fo, "    reg [CONFLICT_COUNT_WIDTH-1:0] conflict_counter;\n");
    fprintf(fo, "    assign filter_hit_count = hit_counter;\n");
    fprintf(fo, "    assign filter_miss_count = miss_counter;\n");
    fprintf(fo, "    assign conflict_count = conflict_counter;\n\n");
    
    // Enhanced write-invalidate protocol state machine
    fprintf(fo, "    // Write-Invalidate Protocol State Machine\n");
    fprintf(fo, "    localparam [2:0] INVAL_IDLE = 3'b000;\n");
    fprintf(fo, "    localparam [2:0] INVAL_DETECT = 3'b001;\n");
    fprintf(fo, "    localparam [2:0] INVAL_BROADCAST = 3'b010;\n");
    fprintf(fo, "    localparam [2:0] INVAL_WAIT_RESP = 3'b011;\n");
    fprintf(fo, "    localparam [2:0] INVAL_COMPLETE = 3'b100;\n\n");
    
    fprintf(fo, "    // Invalidation types\n");
    fprintf(fo, "    localparam [2:0] INVAL_TYPE_WRITE = 3'b001;\n");
    fprintf(fo, "    localparam [2:0] INVAL_TYPE_EVICT = 3'b010;\n");
    fprintf(fo, "    localparam [2:0] INVAL_TYPE_CLEAN_INVALID = 3'b011;\n");
    fprintf(fo, "    localparam [2:0] INVAL_TYPE_MAKE_INVALID = 3'b100;\n\n");
    
    fprintf(fo, "    // Write-invalidate protocol registers\n");
    fprintf(fo, "    reg [2:0] invalidate_state;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] invalidate_pending;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] invalidate_responses_rcvd;\n");
    fprintf(fo, "    reg [TAG_BITS-1:0] current_invalidate_tag;\n");
    fprintf(fo, "    reg [$clog2(SNOOP_FILTER_DEPTH)-1:0] current_invalidate_idx;\n");
    fprintf(fo, "    reg invalidate_in_progress;\n\n");
    
    fprintf(fo, "    // Write conflict detection registers\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] write_conflict_mask;\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] last_write_addr;\n");
    fprintf(fo, "    reg conflict_detected_reg;\n\n");
    
    fprintf(fo, "    // Snoop response aggregation\n");
    for (int k = 0; k < numM; k++) {
        fprintf(fo, "    assign m%d_crready = (invalidate_state == INVAL_WAIT_RESP) && invalidate_pending[%d];\n", k, k);
    }
    fprintf(fo, "\n");
    fprintf(fo, "    // Invalidate valid output\n");
    fprintf(fo, "    assign invalidate_valid = (invalidate_state == INVAL_BROADCAST) || (invalidate_state == INVAL_WAIT_RESP);\n\n");
    
    // Address tag extraction functions
    fprintf(fo, "    // Address tag extraction\n");
    fprintf(fo, "    function [TAG_BITS-1:0] extract_tag;\n");
    fprintf(fo, "        input [WIDTH_AD-1:0] addr;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            extract_tag = addr[WIDTH_AD-1:CACHELINE_OFFSET_BITS];\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Filter lookup function
    fprintf(fo, "    // Snoop filter lookup function\n");
    fprintf(fo, "    function [$clog2(SNOOP_FILTER_DEPTH)-1:0] filter_lookup;\n");
    fprintf(fo, "        input [TAG_BITS-1:0] tag;\n");
    fprintf(fo, "        integer k;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            filter_lookup = {$clog2(SNOOP_FILTER_DEPTH){1'b1}}; // Invalid index\n");
    fprintf(fo, "            for (k = 0; k < SNOOP_FILTER_DEPTH; k = k + 1) begin\n");
    fprintf(fo, "                if (filter_valid[k] && (filter_tag_table[k] == tag)) begin\n");
    fprintf(fo, "                    filter_lookup = k;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Generate snoop requirement detection for each master
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d snoop requirement logic\n", i);
        fprintf(fo, "    wire [TAG_BITS-1:0] m%d_aw_tag = extract_tag(m%d_awaddr);\n", i, i);
        fprintf(fo, "    wire [TAG_BITS-1:0] m%d_ar_tag = extract_tag(m%d_araddr);\n", i, i);
        fprintf(fo, "    wire m%d_aw_coherent = (m%d_awdomain != DOMAIN_NON_SHAREABLE) && \n", i, i);
        fprintf(fo, "                           (m%d_awsnoop != AWSNOOP_WRITE_NO_SNOOP);\n", i);
        fprintf(fo, "    wire m%d_ar_coherent = (m%d_ardomain != DOMAIN_NON_SHAREABLE) && \n", i, i);
        fprintf(fo, "                           (m%d_arsnoop != ARSNOOP_READ_NO_SNOOP);\n", i);
        fprintf(fo, "    \n");
    }
    
    // Intermediate lookup index registers  
    fprintf(fo, "    // Lookup index registers for filter operations\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    reg [$clog2(SNOOP_FILTER_DEPTH)-1:0] m%d_aw_lookup_idx, m%d_ar_lookup_idx;\n", i, i);
        fprintf(fo, "    reg [$clog2(SNOOP_FILTER_DEPTH)-1:0] m%d_aw_snoop_idx, m%d_ar_snoop_idx;\n", i, i);
    }
    fprintf(fo, "\n");
    
    // Write-invalidate protocol state machine
    fprintf(fo, "    // Enhanced Write-Invalidate Protocol State Machine\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            invalidate_state <= INVAL_IDLE;\n");
    fprintf(fo, "            invalidate_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            invalidate_responses_rcvd <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            invalidate_required <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            invalidate_addr <= {WIDTH_AD{1'b0}};\n");
    fprintf(fo, "            invalidate_type <= 3'b0;\n");
    fprintf(fo, "            invalidate_in_progress <= 1'b0;\n");
    fprintf(fo, "            conflict_detected <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            conflict_addr <= {WIDTH_AD{1'b0}};\n");
    fprintf(fo, "            write_conflict_mask <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            conflict_detected_reg <= 1'b0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            case (invalidate_state)\n");
    fprintf(fo, "                INVAL_IDLE: begin\n");
    fprintf(fo, "                    // Detect write conflicts requiring invalidation\n");
    fprintf(fo, "                    invalidate_required <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    conflict_detected <= {NUM_MASTER{1'b0}};\n");
    
    // Check for write conflicts from each master
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    \n");
        fprintf(fo, "                    // Master %d write conflict detection\n", i);
        fprintf(fo, "                    if (m%d_awvalid && m%d_awready && m%d_aw_coherent) begin\n", i, i, i);
        fprintf(fo, "                        current_invalidate_tag = extract_tag(m%d_awaddr);\n", i);
        fprintf(fo, "                        current_invalidate_idx = filter_lookup(current_invalidate_tag);\n");
        fprintf(fo, "                        \n");
        fprintf(fo, "                        // Check if other masters have this cache line\n");
        fprintf(fo, "                        if (current_invalidate_idx != {$clog2(SNOOP_FILTER_DEPTH){1'b1}}) begin\n");
        fprintf(fo, "                            write_conflict_mask = filter_master_table[current_invalidate_idx] & ~(1'b1 << %d);\n", i);
        fprintf(fo, "                            \n");
        fprintf(fo, "                            if (|write_conflict_mask) begin\n");
        fprintf(fo, "                                // Conflict detected - initiate invalidation\n");
        fprintf(fo, "                                invalidate_state <= INVAL_DETECT;\n");
        fprintf(fo, "                                invalidate_addr <= m%d_awaddr;\n", i);
        fprintf(fo, "                                invalidate_pending <= write_conflict_mask;\n");
        fprintf(fo, "                                conflict_detected[%d] <= 1'b1;\n", i);
        fprintf(fo, "                                conflict_addr <= m%d_awaddr;\n", i);
        fprintf(fo, "                                \n");
        fprintf(fo, "                                // Determine invalidation type based on snoop type\n");
        fprintf(fo, "                                case (m%d_awsnoop)\n", i);
        fprintf(fo, "                                    AWSNOOP_WRITE_LINE_UNIQUE: invalidate_type <= INVAL_TYPE_WRITE;\n");
        fprintf(fo, "                                    AWSNOOP_EVICT: invalidate_type <= INVAL_TYPE_EVICT;\n");
        fprintf(fo, "                                    default: invalidate_type <= INVAL_TYPE_WRITE;\n");
        fprintf(fo, "                                endcase\n");
        fprintf(fo, "                            end\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end\n");
    }
    
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                INVAL_DETECT: begin\n");
    fprintf(fo, "                    // Transition to broadcast invalidation\n");
    fprintf(fo, "                    invalidate_state <= INVAL_BROADCAST;\n");
    fprintf(fo, "                    invalidate_required <= invalidate_pending;\n");
    fprintf(fo, "                    invalidate_in_progress <= 1'b1;\n");
    fprintf(fo, "                    conflict_counter <= conflict_counter + 1;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                INVAL_BROADCAST: begin\n");
    fprintf(fo, "                    // Wait for invalidate_ready from interconnect\n");
    fprintf(fo, "                    if (invalidate_ready) begin\n");
    fprintf(fo, "                        invalidate_state <= INVAL_WAIT_RESP;\n");
    fprintf(fo, "                        invalidate_responses_rcvd <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                INVAL_WAIT_RESP: begin\n");
    fprintf(fo, "                    // Collect snoop responses from masters\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    if (m%d_crvalid && invalidate_pending[%d]) begin\n", i, i);
        fprintf(fo, "                        invalidate_responses_rcvd[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end\n");
    }
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Check if all required responses received\n");
    fprintf(fo, "                    if ((invalidate_responses_rcvd & invalidate_pending) == invalidate_pending) begin\n");
    fprintf(fo, "                        invalidate_state <= INVAL_COMPLETE;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                INVAL_COMPLETE: begin\n");
    fprintf(fo, "                    // Complete invalidation and update filter\n");
    fprintf(fo, "                    if (current_invalidate_idx != {$clog2(SNOOP_FILTER_DEPTH){1'b1}}) begin\n");
    fprintf(fo, "                        // Clear invalidated masters from filter\n");
    fprintf(fo, "                        filter_master_table[current_invalidate_idx] <= \n");
    fprintf(fo, "                            filter_master_table[current_invalidate_idx] & ~invalidate_pending;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Return to idle\n");
    fprintf(fo, "                    invalidate_state <= INVAL_IDLE;\n");
    fprintf(fo, "                    invalidate_required <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    invalidate_in_progress <= 1'b0;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                default: begin\n");
    fprintf(fo, "                    invalidate_state <= INVAL_IDLE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            endcase\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Filter table management logic  
    fprintf(fo, "    // Snoop filter table management\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            filter_valid <= {SNOOP_FILTER_DEPTH{1'b0}};\n");
    fprintf(fo, "            filter_lru_ptr <= 0;\n");
    fprintf(fo, "            hit_counter <= 8'h0;\n");
    fprintf(fo, "            miss_counter <= 8'h0;\n");
    fprintf(fo, "            conflict_counter <= {CONFLICT_COUNT_WIDTH{1'b0}};\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Initialize filter tables would be done with generate blocks in actual RTL\n");
    }
    fprintf(fo, "        end else if (snoop_filter_enable && !snoop_filter_bypass && !invalidate_in_progress) begin\n");
    
    // Process write transactions
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Process Master %d write transactions\n", i);
        fprintf(fo, "            if (m%d_awvalid && m%d_awready && m%d_aw_coherent) begin\n", i, i, i);
        fprintf(fo, "                m%d_aw_lookup_idx = filter_lookup(m%d_aw_tag);\n", i, i);
        fprintf(fo, "                if (m%d_aw_lookup_idx != {$clog2(SNOOP_FILTER_DEPTH){1'b1}}) begin\n", i);
        fprintf(fo, "                    // Hit: Update existing entry\n");
        fprintf(fo, "                    filter_master_table[m%d_aw_lookup_idx][%d] <= 1'b1;\n", i, i);
        fprintf(fo, "                    if (m%d_awsnoop == AWSNOOP_WRITE_LINE_UNIQUE) begin\n", i);
        fprintf(fo, "                        filter_state_table[m%d_aw_lookup_idx] <= LINE_UNIQUE;\n", i);
        fprintf(fo, "                        // Invalidate other masters\n");
        for (j = 0; j < numM; j++) {
            if (j != i) {
                fprintf(fo, "                        filter_master_table[m%d_aw_lookup_idx][%d] <= 1'b0;\n", i, j);
            }
        }
        fprintf(fo, "                    end else if (m%d_awsnoop == AWSNOOP_WRITE_CLEAN) begin\n", i);
        fprintf(fo, "                        filter_state_table[m%d_aw_lookup_idx] <= LINE_DIRTY;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    hit_counter <= hit_counter + 1;\n");
        fprintf(fo, "                end else begin\n");
        fprintf(fo, "                    // Miss: Allocate new entry\n");
        fprintf(fo, "                    filter_tag_table[filter_lru_ptr] <= m%d_aw_tag;\n", i);
        fprintf(fo, "                    filter_master_table[filter_lru_ptr] <= 1'b0;\n");
        fprintf(fo, "                    filter_master_table[filter_lru_ptr][%d] <= 1'b1;\n", i);
        fprintf(fo, "                    filter_state_table[filter_lru_ptr] <= LINE_SHARED;\n");
        fprintf(fo, "                    filter_valid[filter_lru_ptr] <= 1'b1;\n");
        fprintf(fo, "                    filter_lru_ptr <= (filter_lru_ptr + 1) %% SNOOP_FILTER_DEPTH;\n");
        fprintf(fo, "                    miss_counter <= miss_counter + 1;\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n\n");
    }
    
    // Process read transactions
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Process Master %d read transactions\n", i);
        fprintf(fo, "            if (m%d_arvalid && m%d_arready && m%d_ar_coherent) begin\n", i, i, i);
        fprintf(fo, "                m%d_ar_lookup_idx = filter_lookup(m%d_ar_tag);\n", i, i);
        fprintf(fo, "                if (m%d_ar_lookup_idx != {$clog2(SNOOP_FILTER_DEPTH){1'b1}}) begin\n", i);
        fprintf(fo, "                    // Hit: Update existing entry\n");
        fprintf(fo, "                    filter_master_table[m%d_ar_lookup_idx][%d] <= 1'b1;\n", i, i);
        fprintf(fo, "                    if (m%d_arsnoop == ARSNOOP_READ_UNIQUE) begin\n", i);
        fprintf(fo, "                        filter_state_table[m%d_ar_lookup_idx] <= LINE_UNIQUE;\n", i);
        fprintf(fo, "                        // Invalidate other masters\n");
        for (j = 0; j < numM; j++) {
            if (j != i) {
                fprintf(fo, "                        filter_master_table[m%d_ar_lookup_idx][%d] <= 1'b0;\n", i, j);
            }
        }
        fprintf(fo, "                    end else begin\n");
        fprintf(fo, "                        filter_state_table[m%d_ar_lookup_idx] <= LINE_SHARED;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    hit_counter <= hit_counter + 1;\n");
        fprintf(fo, "                end else begin\n");
        fprintf(fo, "                    // Miss: Allocate new entry for coherent reads\n");
        fprintf(fo, "                    if (m%d_arsnoop != ARSNOOP_READ_NO_SNOOP) begin\n", i);
        fprintf(fo, "                        filter_tag_table[filter_lru_ptr] <= m%d_ar_tag;\n", i);
        fprintf(fo, "                        filter_master_table[filter_lru_ptr] <= 1'b0;\n");
        fprintf(fo, "                        filter_master_table[filter_lru_ptr][%d] <= 1'b1;\n", i);
        fprintf(fo, "                        filter_state_table[filter_lru_ptr] <= LINE_SHARED;\n");
        fprintf(fo, "                        filter_valid[filter_lru_ptr] <= 1'b1;\n");
        fprintf(fo, "                        filter_lru_ptr <= (filter_lru_ptr + 1) %% SNOOP_FILTER_DEPTH;\n");
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    miss_counter <= miss_counter + 1;\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n\n");
    }
    
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Snoop requirement output generation
    fprintf(fo, "    // Snoop requirement output logic\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    wire m%d_snoop_req_aw, m%d_snoop_req_ar;\n", i, i);
        fprintf(fo, "    assign m%d_snoop_req_aw = m%d_awvalid && m%d_aw_coherent && snoop_filter_enable;\n", i, i, i);
        fprintf(fo, "    assign m%d_snoop_req_ar = m%d_arvalid && m%d_ar_coherent && snoop_filter_enable;\n", i, i, i);
        fprintf(fo, "    assign snoop_required[%d] = m%d_snoop_req_aw || m%d_snoop_req_ar;\n", i, i, i);
        fprintf(fo, "    assign snoop_block[%d] = snoop_required[%d] && !snoop_filter_bypass;\n", i, i);
    }
    fprintf(fo, "\n");
    
    // Snoop target generation
    fprintf(fo, "    // Snoop target address and master selection\n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        snoop_target_addr = 32'h0;\n");
    fprintf(fo, "        snoop_target_masters = {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "        \n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        // Master %d snoop targeting\n", i);
        fprintf(fo, "        if (snoop_required[%d]) begin\n", i);
        fprintf(fo, "            if (m%d_awvalid) begin\n", i);
        fprintf(fo, "                snoop_target_addr = m%d_awaddr;\n", i);
        fprintf(fo, "                // Find other masters with this cache line\n");
        fprintf(fo, "                m%d_aw_snoop_idx = filter_lookup(m%d_aw_tag);\n", i, i);
        fprintf(fo, "                if (m%d_aw_snoop_idx != {$clog2(SNOOP_FILTER_DEPTH){1'b1}}) begin\n", i);
        fprintf(fo, "                    snoop_target_masters = filter_master_table[m%d_aw_snoop_idx] & ~(1'b1 << %d);\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            end else if (m%d_arvalid) begin\n", i);
        fprintf(fo, "                snoop_target_addr = m%d_araddr;\n", i);
        fprintf(fo, "                // Find other masters with this cache line\n");
        fprintf(fo, "                m%d_ar_snoop_idx = filter_lookup(m%d_ar_tag);\n", i, i);
        fprintf(fo, "                if (m%d_ar_snoop_idx != {$clog2(SNOOP_FILTER_DEPTH){1'b1}}) begin\n", i);
        fprintf(fo, "                    snoop_target_masters = filter_master_table[m%d_ar_snoop_idx] & ~(1'b1 << %d);\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
    }
    fprintf(fo, "    end\n\n");
    
    // Generate validation assertions
    generate_rtl_signal_assertions("ace_lite_snoop_filter", fo);
    
    // Generate port validation checks
    port_connection_t port_checks[] = {
        {"conflict_count", "conflict_count", "CONFLICT_COUNT_WIDTH", 1},
        {"snoop_required", "snoop_required", "NUM_MASTER", 1},
        {"invalidate_required", "invalidate_required", "NUM_MASTER", 1}
    };
    validate_port_connections("ace_lite_snoop_filter", port_checks, 3, fo);
    
    fprintf(fo, "endmodule\n");
    
    return 0;
}