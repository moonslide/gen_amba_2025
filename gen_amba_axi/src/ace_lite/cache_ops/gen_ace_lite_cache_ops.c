//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite Cache Operations Module Generator
// Cache maintenance operation decode and dispatch
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "../../gen_amba_axi.h"
#include "../../gen_axi_utils.h"

//--------------------------------------------------------
// Generate ACE-Lite cache operations module
//--------------------------------------------------------
int gen_ace_lite_cache_ops(unsigned int numM, unsigned int numS, unsigned int widthAD, unsigned int widthDA,
                           char *prefix, axi_features_t *features, FILE *fo)
{
    int i;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite Cache Operations\n");
    fprintf(fo, "// Cache maintenance operation decode and dispatch\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %sace_lite_cache_ops\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , CACHE_OP_DEPTH = 32 // Cache operation queue depth\n");
    fprintf(fo, "              // Parameterized maintenance priority width - scales with queue depth and master count\n");
    fprintf(fo, "              , MAINT_PRIORITY_WIDTH = (CACHE_OP_DEPTH <= 16 && NUM_MASTER <= 8) ? 3 : (CACHE_OP_DEPTH <= 64 && NUM_MASTER <= 16) ? 4 : (NUM_MASTER <= 32) ? 5 : 6)\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                       clk\n");
    fprintf(fo, "    , input  wire                       rst_n\n");
    
    // Master cache operation interface inputs
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d cache operation interface\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]       m%d_awid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]       m%d_awaddr\n", i);
        fprintf(fo, "    , input  wire [2:0]                m%d_awsnoop\n", i);
        fprintf(fo, "    , input  wire [1:0]                m%d_awdomain\n", i);
        fprintf(fo, "    , input  wire                      m%d_awvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_awready\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]       m%d_arid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]       m%d_araddr\n", i);
        fprintf(fo, "    , input  wire [3:0]                m%d_arsnoop\n", i);
        fprintf(fo, "    , input  wire [1:0]                m%d_ardomain\n", i);
        fprintf(fo, "    , input  wire                      m%d_arvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_arready\n", i);
    }
    
    // Enhanced Cache Operation Control (Phase 4)
    fprintf(fo, "    // Enhanced Cache Operation Control\n");
    fprintf(fo, "    , input  wire                       cache_ops_enable\n");
    fprintf(fo, "    , input  wire                       cache_maint_bypass\n");
    fprintf(fo, "    , input  wire [WIDTH_AD-1:0]        cache_base_addr\n");
    fprintf(fo, "    , input  wire [WIDTH_AD-1:0]        cache_size\n");
    fprintf(fo, "    , input  wire [7:0]                 cache_line_size\n");
    fprintf(fo, "    // Advanced Cache Maintenance Control (Phase 4)\n");
    fprintf(fo, "    , input  wire                       maint_timeout_enable\n");
    fprintf(fo, "    , input  wire [15:0]                maint_timeout_cycles\n");
    fprintf(fo, "    , input  wire                       maint_completion_tracking\n");
    fprintf(fo, "    , input  wire                       maint_conflict_resolution\n");
    fprintf(fo, "    , input  wire [MAINT_PRIORITY_WIDTH-1:0] maint_priority_level\n");
    fprintf(fo, "    , input  wire                       maint_queuing_enable\n");
    fprintf(fo, "    , input  wire                       maint_scheduling_enable\n");
    
    // Enhanced Cache Operation Outputs (Phase 4)
    fprintf(fo, "    // Enhanced Cache Operation Outputs\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       cache_op_active\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       cache_maint_required\n");
    fprintf(fo, "    , output wire [3:0]                  cache_op_type [NUM_MASTER-1:0]\n");
    fprintf(fo, "    , output wire [WIDTH_AD-1:0]         cache_op_addr [NUM_MASTER-1:0]\n");
    fprintf(fo, "    , output wire [7:0]                  cache_op_pending_count\n");
    fprintf(fo, "    , output reg  [7:0]                  cache_clean_count\n");
    fprintf(fo, "    , output reg  [7:0]                  cache_invalidate_count\n");
    fprintf(fo, "    // Advanced Maintenance Operation Tracking (Phase 4)\n");
    fprintf(fo, "    , output reg  [7:0]                  maint_completion_count\n");
    fprintf(fo, "    , output reg  [7:0]                  maint_timeout_count\n");
    fprintf(fo, "    , output reg  [7:0]                  maint_error_count\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       maint_conflict_detected\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       maint_operation_complete\n");
    fprintf(fo, "    , output reg  [MAINT_PRIORITY_WIDTH-1:0] maint_current_priority\n");
    fprintf(fo, "    , output wire [7:0]                  maint_queue_depth\n");
    
    fprintf(fo, ");\n\n");
    
    // Enhanced Cache Maintenance Operation Type Encodings (Phase 4)
    fprintf(fo, "    // Enhanced Cache Maintenance Operation Type Encodings\n");
    fprintf(fo, "    localparam [3:0] CACHE_OP_NONE = 4'h0;\n");
    fprintf(fo, "    localparam [3:0] CACHE_OP_CLEAN = 4'h1;\n");
    fprintf(fo, "    localparam [3:0] CACHE_OP_INVALIDATE = 4'h2;\n");
    fprintf(fo, "    localparam [3:0] CACHE_OP_CLEAN_INVALIDATE = 4'h3;\n");
    fprintf(fo, "    localparam [3:0] CACHE_OP_MAKE_UNIQUE = 4'h4;\n");
    fprintf(fo, "    localparam [3:0] CACHE_OP_EVICT = 4'h5;\n");
    fprintf(fo, "    localparam [3:0] CACHE_OP_WRITEBACK = 4'h6;\n");
    fprintf(fo, "    localparam [3:0] CACHE_OP_ZERO = 4'h7;\n");
    fprintf(fo, "    // Advanced Cache Maintenance Types (Phase 4)\n");
    fprintf(fo, "    localparam [3:0] MAINT_CLEAN_POC = 4'h8;           // Clean to Point of Coherency\n");
    fprintf(fo, "    localparam [3:0] MAINT_CLEAN_POU = 4'h9;           // Clean to Point of Unification\n");
    fprintf(fo, "    localparam [3:0] MAINT_CLEAN_INV_POC = 4'hA;       // Clean and Invalidate to PoC\n");
    fprintf(fo, "    localparam [3:0] MAINT_INV_POC = 4'hB;             // Invalidate to PoC\n");
    fprintf(fo, "    localparam [3:0] MAINT_FLUSH_POC = 4'hC;           // Flush to PoC\n");
    fprintf(fo, "    localparam [3:0] MAINT_FLUSH_POU = 4'hD;           // Flush to PoU\n");
    fprintf(fo, "    localparam [3:0] MAINT_ZERO_POC = 4'hE;            // Zero to PoC\n");
    fprintf(fo, "    localparam [3:0] MAINT_PREFETCH = 4'hF;            // Prefetch operation\n\n");
    
    // Write snoop encodings for cache operations
    fprintf(fo, "    // Write snoop encodings (cache maintenance)\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_NO_SNOOP = 3'b000;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_LINE_UNIQUE = 3'b001;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_CLEAN = 3'b010;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_BACK = 3'b011;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_EVICT = 3'b100;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_EVICT = 3'b101;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_ZERO = 3'b110;\n\n");
    
    // Read snoop encodings for cache operations
    fprintf(fo, "    // Read snoop encodings (cache maintenance)\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_NO_SNOOP = 4'b0000;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_ONCE = 4'b0001;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_SHARED = 4'b0001;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_CLEAN = 4'b0010;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_NOT_SHARED_DIRTY = 4'b0011;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_UNIQUE = 4'b0111;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_CLEAN_SHARED = 4'b1000;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_CLEAN_INVALID = 4'b1001;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_MAKE_INVALID = 4'b1101;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_CLEAN_UNIQUE = 4'b1011;\n\n");
    
    // Enhanced Cache Operation Queue Structure (Phase 4)
    fprintf(fo, "    // Enhanced Cache Operation Queue\n");
    fprintf(fo, "    reg [WIDTH_ID-1:0] cache_op_queue_id [0:CACHE_OP_DEPTH-1];\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] cache_op_queue_addr [0:CACHE_OP_DEPTH-1];\n");
    fprintf(fo, "    reg [3:0] cache_op_queue_type [0:CACHE_OP_DEPTH-1];\n");
    fprintf(fo, "    reg [7:0] cache_op_queue_master [0:CACHE_OP_DEPTH-1];\n");
    fprintf(fo, "    reg [CACHE_OP_DEPTH-1:0] cache_op_queue_valid;\n");
    fprintf(fo, "    reg [$clog2(CACHE_OP_DEPTH)-1:0] cache_op_wr_ptr;\n");
    fprintf(fo, "    reg [$clog2(CACHE_OP_DEPTH)-1:0] cache_op_rd_ptr;\n");
    fprintf(fo, "    // Advanced Maintenance Operation Tracking (Phase 4)\n");
    fprintf(fo, "    reg [15:0] cache_op_queue_timestamp [0:CACHE_OP_DEPTH-1]; // Operation start time\n");
    fprintf(fo, "    reg [3:0] cache_op_queue_priority [0:CACHE_OP_DEPTH-1];   // Operation priority\n");
    fprintf(fo, "    reg [CACHE_OP_DEPTH-1:0] cache_op_queue_complete;        // Completion status\n");
    fprintf(fo, "    reg [CACHE_OP_DEPTH-1:0] cache_op_queue_timeout;         // Timeout status\n");
    fprintf(fo, "    reg [CACHE_OP_DEPTH-1:0] cache_op_queue_conflict;        // Conflict detection\n");
    fprintf(fo, "    reg [7:0] cache_op_queue_retry_count [0:CACHE_OP_DEPTH-1]; // Retry attempts\n\n");
    
    // Enhanced Performance Monitoring (Phase 4)
    fprintf(fo, "    // Enhanced Performance Monitoring\n");
    fprintf(fo, "    reg [15:0] total_cache_ops;\n");
    fprintf(fo, "    reg [7:0] cache_writeback_count;\n");
    fprintf(fo, "    reg [15:0] global_timestamp;           // Global time counter\n");
    fprintf(fo, "    reg [7:0] maint_poc_count;             // Point of Coherency operations\n");
    fprintf(fo, "    reg [7:0] maint_pou_count;             // Point of Unification operations\n");
    fprintf(fo, "    reg [7:0] maint_flush_count;           // Flush operations\n");
    fprintf(fo, "    reg [7:0] maint_prefetch_count;        // Prefetch operations\n");
    fprintf(fo, "    reg [15:0] maint_avg_completion_time;  // Average completion time\n");
    fprintf(fo, "    reg [7:0] maint_max_queue_depth;       // Maximum queue depth reached\n\n");
    
    // Cache operation decode functions
    fprintf(fo, "    // Cache operation decode functions\n");
    fprintf(fo, "    function [3:0] decode_write_cache_op;\n");
    fprintf(fo, "        input [2:0] awsnoop;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            case (awsnoop)\n");
    fprintf(fo, "                AWSNOOP_WRITE_CLEAN:     decode_write_cache_op = CACHE_OP_CLEAN;\n");
    fprintf(fo, "                AWSNOOP_WRITE_LINE_UNIQUE: decode_write_cache_op = CACHE_OP_MAKE_UNIQUE;\n");
    fprintf(fo, "                AWSNOOP_WRITE_BACK:      decode_write_cache_op = CACHE_OP_WRITEBACK;\n");
    fprintf(fo, "                AWSNOOP_EVICT:           decode_write_cache_op = CACHE_OP_EVICT;\n");
    fprintf(fo, "                AWSNOOP_WRITE_EVICT:     decode_write_cache_op = CACHE_OP_CLEAN_INVALIDATE;\n");
    fprintf(fo, "                AWSNOOP_WRITE_ZERO:      decode_write_cache_op = CACHE_OP_ZERO;\n");
    fprintf(fo, "                default:                 decode_write_cache_op = CACHE_OP_NONE;\n");
    fprintf(fo, "            endcase\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    fprintf(fo, "    function [3:0] decode_read_cache_op;\n");
    fprintf(fo, "        input [3:0] arsnoop;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            case (arsnoop)\n");
    fprintf(fo, "                ARSNOOP_READ_CLEAN:           decode_read_cache_op = CACHE_OP_CLEAN;\n");
    fprintf(fo, "                ARSNOOP_CLEAN_SHARED:         decode_read_cache_op = MAINT_CLEAN_POC;  // Enhanced PoC\n");
    fprintf(fo, "                ARSNOOP_CLEAN_INVALID:        decode_read_cache_op = MAINT_CLEAN_INV_POC; // Enhanced PoC\n");
    fprintf(fo, "                ARSNOOP_CLEAN_UNIQUE:         decode_read_cache_op = MAINT_CLEAN_POU;  // Enhanced PoU\n");
    fprintf(fo, "                ARSNOOP_MAKE_INVALID:         decode_read_cache_op = MAINT_INV_POC;    // Enhanced PoC\n");
    fprintf(fo, "                ARSNOOP_READ_UNIQUE:          decode_read_cache_op = CACHE_OP_MAKE_UNIQUE;\n");
    fprintf(fo, "                default:                      decode_read_cache_op = CACHE_OP_NONE;\n");
    fprintf(fo, "            endcase\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Add advanced maintenance operation decoding function (Phase 4)
    fprintf(fo, "    // Advanced Maintenance Operation Decoding (Phase 4)\n");
    fprintf(fo, "    function [3:0] decode_advanced_maint_op;\n");
    fprintf(fo, "        input [3:0] cache_op_type;\n");
    fprintf(fo, "        input [1:0] domain;\n");
    fprintf(fo, "        input cache_maint_enable;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            if (!cache_maint_enable) begin\n");
    fprintf(fo, "                decode_advanced_maint_op = cache_op_type;\n");
    fprintf(fo, "            end else begin\n");
    fprintf(fo, "                case ({domain, cache_op_type[1:0]})\n");
    fprintf(fo, "                    {2'b00, 2'b01}: decode_advanced_maint_op = MAINT_CLEAN_POC;     // Inner Shareable, Clean\n");
    fprintf(fo, "                    {2'b01, 2'b01}: decode_advanced_maint_op = MAINT_CLEAN_POU;     // Outer Shareable, Clean\n");
    fprintf(fo, "                    {2'b10, 2'b01}: decode_advanced_maint_op = MAINT_FLUSH_POC;     // System, Clean (Flush)\n");
    fprintf(fo, "                    {2'b00, 2'b10}: decode_advanced_maint_op = MAINT_INV_POC;       // Inner Shareable, Invalidate\n");
    fprintf(fo, "                    {2'b01, 2'b10}: decode_advanced_maint_op = MAINT_INV_POC;       // Outer Shareable, Invalidate\n");
    fprintf(fo, "                    {2'b10, 2'b10}: decode_advanced_maint_op = MAINT_FLUSH_POU;     // System, Invalidate (Flush)\n");
    fprintf(fo, "                    {2'b00, 2'b11}: decode_advanced_maint_op = MAINT_CLEAN_INV_POC; // Inner Shareable, Clean+Inv\n");
    fprintf(fo, "                    {2'b01, 2'b11}: decode_advanced_maint_op = MAINT_CLEAN_INV_POC; // Outer Shareable, Clean+Inv\n");
    fprintf(fo, "                    {2'b10, 2'b11}: decode_advanced_maint_op = MAINT_FLUSH_POC;     // System, Clean+Inv (Flush)\n");
    fprintf(fo, "                    default:        decode_advanced_maint_op = cache_op_type;\n");
    fprintf(fo, "                endcase\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Cache operation detection and queueing
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d cache operation detection\n", i);
        fprintf(fo, "    wire [3:0] m%d_aw_cache_op = decode_write_cache_op(m%d_awsnoop);\n", i, i);
        fprintf(fo, "    wire [3:0] m%d_ar_cache_op = decode_read_cache_op(m%d_arsnoop);\n", i, i);
        fprintf(fo, "    wire m%d_aw_is_cache_op = (m%d_aw_cache_op != CACHE_OP_NONE) && m%d_awvalid;\n", i, i, i);
        fprintf(fo, "    wire m%d_ar_is_cache_op = (m%d_ar_cache_op != CACHE_OP_NONE) && m%d_arvalid;\n", i, i, i);
        fprintf(fo, "    assign cache_op_type[%d] = m%d_aw_is_cache_op ? m%d_aw_cache_op : m%d_ar_cache_op;\n", i, i, i, i);
        fprintf(fo, "    assign cache_op_addr[%d] = m%d_aw_is_cache_op ? m%d_awaddr : m%d_araddr;\n", i, i, i, i);
        fprintf(fo, "\n");
    }
    
    // Enhanced Cache Operation Queue Management with Advanced Features (Phase 4)
    fprintf(fo, "    // Enhanced Cache Operation Queue Management\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            cache_op_queue_valid <= {CACHE_OP_DEPTH{1'b0}};\n");
    fprintf(fo, "            cache_op_wr_ptr <= 0;\n");
    fprintf(fo, "            cache_op_rd_ptr <= 0;\n");
    fprintf(fo, "            total_cache_ops <= 16'h0;\n");
    fprintf(fo, "            cache_clean_count <= 8'h0;\n");
    fprintf(fo, "            cache_invalidate_count <= 8'h0;\n");
    fprintf(fo, "            cache_writeback_count <= 8'h0;\n");
    fprintf(fo, "            // Enhanced Phase 4 counters reset\n");
    fprintf(fo, "            global_timestamp <= 16'h0;\n");
    fprintf(fo, "            maint_poc_count <= 8'h0;\n");
    fprintf(fo, "            maint_pou_count <= 8'h0;\n");
    fprintf(fo, "            maint_flush_count <= 8'h0;\n");
    fprintf(fo, "            maint_prefetch_count <= 8'h0;\n");
    fprintf(fo, "            maint_completion_count <= 8'h0;\n");
    fprintf(fo, "            maint_timeout_count <= 8'h0;\n");
    fprintf(fo, "            maint_error_count <= 8'h0;\n");
    fprintf(fo, "            maint_avg_completion_time <= 16'h0;\n");
    fprintf(fo, "            maint_max_queue_depth <= 8'h0;\n");
    fprintf(fo, "            maint_current_priority <= 4'h0;\n");
    fprintf(fo, "            // Reset advanced tracking arrays\n");
    fprintf(fo, "            cache_op_queue_complete <= {CACHE_OP_DEPTH{1'b0}};\n");
    fprintf(fo, "            cache_op_queue_timeout <= {CACHE_OP_DEPTH{1'b0}};\n");
    fprintf(fo, "            cache_op_queue_conflict <= {CACHE_OP_DEPTH{1'b0}};\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            cache_op_active[%d] <= 1'b0;\n", i);
        fprintf(fo, "            cache_maint_required[%d] <= 1'b0;\n", i);
        fprintf(fo, "            maint_conflict_detected[%d] <= 1'b0;\n", i);
        fprintf(fo, "            maint_operation_complete[%d] <= 1'b0;\n", i);
    }
    fprintf(fo, "        end else if (cache_ops_enable) begin\n");
    fprintf(fo, "            // Global timestamp increment\n");
    fprintf(fo, "            global_timestamp <= global_timestamp + 1;\n");
    
    // Enqueue cache operations
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d cache operation enqueue\n", i);
        fprintf(fo, "            if ((m%d_aw_is_cache_op && m%d_awready) || (m%d_ar_is_cache_op && m%d_arready)) begin\n", i, i, i, i);
        fprintf(fo, "                if (!cache_op_queue_valid[cache_op_wr_ptr]) begin\n");
        fprintf(fo, "                    // Enhanced Phase 4 operation queueing\n");
        fprintf(fo, "                    cache_op_queue_id[cache_op_wr_ptr] <= m%d_aw_is_cache_op ? m%d_awid : m%d_arid;\n", i, i, i);
        fprintf(fo, "                    cache_op_queue_addr[cache_op_wr_ptr] <= cache_op_addr[%d];\n", i);
        fprintf(fo, "                    // Use advanced maintenance operation decoding\n");
        fprintf(fo, "                    cache_op_queue_type[cache_op_wr_ptr] <= decode_advanced_maint_op(\n");
        fprintf(fo, "                        cache_op_type[%d], \n", i);
        fprintf(fo, "                        m%d_aw_is_cache_op ? m%d_awdomain : m%d_ardomain,\n", i, i, i);
        fprintf(fo, "                        maint_completion_tracking);\n");
        fprintf(fo, "                    cache_op_queue_master[cache_op_wr_ptr] <= %d;\n", i);
        fprintf(fo, "                    cache_op_queue_valid[cache_op_wr_ptr] <= 1'b1;\n");
        fprintf(fo, "                    // Enhanced Phase 4 tracking initialization\n");
        fprintf(fo, "                    cache_op_queue_timestamp[cache_op_wr_ptr] <= global_timestamp;\n");
        fprintf(fo, "                    cache_op_queue_priority[cache_op_wr_ptr] <= maint_priority_level;\n");
        fprintf(fo, "                    cache_op_queue_complete[cache_op_wr_ptr] <= 1'b0;\n");
        fprintf(fo, "                    cache_op_queue_timeout[cache_op_wr_ptr] <= 1'b0;\n");
        fprintf(fo, "                    cache_op_queue_conflict[cache_op_wr_ptr] <= 1'b0;\n");
        fprintf(fo, "                    cache_op_queue_retry_count[cache_op_wr_ptr] <= 8'h0;\n");
        fprintf(fo, "                    cache_op_wr_ptr <= (cache_op_wr_ptr + 1) %% CACHE_OP_DEPTH;\n");
        fprintf(fo, "                    total_cache_ops <= total_cache_ops + 1;\n");
        fprintf(fo, "                    \n");
        fprintf(fo, "                    // Enhanced operation type counters (Phase 4)\n");
        fprintf(fo, "                    case (cache_op_queue_type[cache_op_wr_ptr])\n");
        fprintf(fo, "                        CACHE_OP_CLEAN, CACHE_OP_CLEAN_INVALIDATE: \n");
        fprintf(fo, "                            cache_clean_count <= cache_clean_count + 1;\n");
        fprintf(fo, "                        CACHE_OP_INVALIDATE, CACHE_OP_MAKE_UNIQUE: \n");
        fprintf(fo, "                            cache_invalidate_count <= cache_invalidate_count + 1;\n");
        fprintf(fo, "                        CACHE_OP_WRITEBACK, CACHE_OP_EVICT: \n");
        fprintf(fo, "                            cache_writeback_count <= cache_writeback_count + 1;\n");
        fprintf(fo, "                        // Advanced Phase 4 maintenance operations\n");
        fprintf(fo, "                        MAINT_CLEAN_POC, MAINT_CLEAN_INV_POC, MAINT_INV_POC:\n");
        fprintf(fo, "                            maint_poc_count <= maint_poc_count + 1;\n");
        fprintf(fo, "                        MAINT_CLEAN_POU, MAINT_FLUSH_POU:\n");
        fprintf(fo, "                            maint_pou_count <= maint_pou_count + 1;\n");
        fprintf(fo, "                        MAINT_FLUSH_POC:\n");
        fprintf(fo, "                            maint_flush_count <= maint_flush_count + 1;\n");
        fprintf(fo, "                        MAINT_PREFETCH:\n");
        fprintf(fo, "                            maint_prefetch_count <= maint_prefetch_count + 1;\n");
        fprintf(fo, "                        default: ; // No counting for other ops\n");
        fprintf(fo, "                    endcase\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Master %d cache operation status\n", i);
        fprintf(fo, "            cache_op_active[%d] <= m%d_aw_is_cache_op || m%d_ar_is_cache_op;\n", i, i, i);
        fprintf(fo, "            cache_maint_required[%d] <= cache_op_active[%d] && !cache_maint_bypass;\n", i, i);
    }
    
    // Enhanced Phase 4 Advanced Cache Maintenance Operation Processing
    fprintf(fo, "            // Advanced Cache Maintenance Operation Processing (Phase 4)\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Timeout detection and handling\n");
    fprintf(fo, "            if (maint_timeout_enable) begin\n");
    fprintf(fo, "                for (integer j = 0; j < CACHE_OP_DEPTH; j = j + 1) begin\n");
    fprintf(fo, "                    if (cache_op_queue_valid[j] && !cache_op_queue_complete[j]) begin\n");
    fprintf(fo, "                        // Check for timeout\n");
    fprintf(fo, "                        if ((global_timestamp - cache_op_queue_timestamp[j]) >= maint_timeout_cycles) begin\n");
    fprintf(fo, "                            cache_op_queue_timeout[j] <= 1'b1;\n");
    fprintf(fo, "                            maint_timeout_count <= maint_timeout_count + 1;\n");
    fprintf(fo, "                            maint_error_count <= maint_error_count + 1;\n");
    fprintf(fo, "                            // Increment retry count\n");
    fprintf(fo, "                            if (cache_op_queue_retry_count[j] < 8'hFF) begin\n");
    fprintf(fo, "                                cache_op_queue_retry_count[j] <= cache_op_queue_retry_count[j] + 1;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Conflict resolution logic\n");
    fprintf(fo, "            if (maint_conflict_resolution) begin\n");
    fprintf(fo, "                for (integer j = 0; j < CACHE_OP_DEPTH; j = j + 1) begin\n");
    fprintf(fo, "                    if (cache_op_queue_valid[j] && !cache_op_queue_complete[j]) begin\n");
    fprintf(fo, "                        for (integer k = j + 1; k < CACHE_OP_DEPTH; k = k + 1) begin\n");
    fprintf(fo, "                            if (cache_op_queue_valid[k] && !cache_op_queue_complete[k]) begin\n");
    fprintf(fo, "                                // Check for address conflicts on cache line boundary\n");
    fprintf(fo, "                                if (cache_op_conflict(cache_op_queue_addr[j], cache_op_queue_addr[k])) begin\n");
    fprintf(fo, "                                    cache_op_queue_conflict[j] <= 1'b1;\n");
    fprintf(fo, "                                    cache_op_queue_conflict[k] <= 1'b1;\n");
    fprintf(fo, "                                    maint_conflict_detected[cache_op_queue_master[j]] <= 1'b1;\n");
    fprintf(fo, "                                    maint_conflict_detected[cache_op_queue_master[k]] <= 1'b1;\n");
    fprintf(fo, "                                end\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Priority-based operation scheduling\n");
    fprintf(fo, "            if (maint_scheduling_enable) begin\n");
    fprintf(fo, "                maint_current_priority <= maint_priority_level;\n");
    fprintf(fo, "                // Process highest priority operations first\n");
    fprintf(fo, "                for (integer j = 0; j < CACHE_OP_DEPTH; j = j + 1) begin\n");
    fprintf(fo, "                    if (cache_op_queue_valid[j] && !cache_op_queue_complete[j] && \n");
    fprintf(fo, "                        !cache_op_queue_timeout[j] && !cache_op_queue_conflict[j]) begin\n");
    fprintf(fo, "                        if (cache_op_queue_priority[j] >= maint_current_priority) begin\n");
    fprintf(fo, "                            // Mark as processing (simplified - real implementation would interface with cache)\n");
    fprintf(fo, "                            // This is where actual cache maintenance would occur\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Enhanced completion tracking and dequeue\n");
    fprintf(fo, "            if (cache_op_queue_valid[cache_op_rd_ptr]) begin\n");
    fprintf(fo, "                // Simulate completion for operations older than completion threshold\n");
    fprintf(fo, "                if ((global_timestamp - cache_op_queue_timestamp[cache_op_rd_ptr]) >= 16) begin\n");
    fprintf(fo, "                    cache_op_queue_complete[cache_op_rd_ptr] <= 1'b1;\n");
    fprintf(fo, "                    maint_completion_count <= maint_completion_count + 1;\n");
    fprintf(fo, "                    maint_operation_complete[cache_op_queue_master[cache_op_rd_ptr]] <= 1'b1;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Update average completion time\n");
    fprintf(fo, "                    maint_avg_completion_time <= (maint_avg_completion_time + \n");
    fprintf(fo, "                        (global_timestamp - cache_op_queue_timestamp[cache_op_rd_ptr])) >> 1;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Dequeue completed operation\n");
    fprintf(fo, "                    cache_op_queue_valid[cache_op_rd_ptr] <= 1'b0;\n");
    fprintf(fo, "                    cache_op_queue_complete[cache_op_rd_ptr] <= 1'b0;\n");
    fprintf(fo, "                    cache_op_queue_timeout[cache_op_rd_ptr] <= 1'b0;\n");
    fprintf(fo, "                    cache_op_queue_conflict[cache_op_rd_ptr] <= 1'b0;\n");
    fprintf(fo, "                    cache_op_rd_ptr <= (cache_op_rd_ptr + 1) %% CACHE_OP_DEPTH;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Cache line address alignment
    fprintf(fo, "    // Cache line address alignment\n");
    fprintf(fo, "    function [WIDTH_AD-1:0] align_to_cache_line;\n");
    fprintf(fo, "        input [WIDTH_AD-1:0] addr;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            align_to_cache_line = {addr[WIDTH_AD-1:$clog2(64)], {$clog2(64){1'b0}}}; // Assume 64-byte cache lines\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Cache operation conflict detection
    fprintf(fo, "    // Cache operation conflict detection\n");
    fprintf(fo, "    function cache_op_conflict;\n");
    fprintf(fo, "        input [WIDTH_AD-1:0] addr1;\n");
    fprintf(fo, "        input [WIDTH_AD-1:0] addr2;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            // Check if two addresses conflict on cache line boundary\n");
    fprintf(fo, "            cache_op_conflict = (align_to_cache_line(addr1) == align_to_cache_line(addr2));\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Enhanced Cache Operation Pending Count and Queue Depth Tracking (Phase 4)
    fprintf(fo, "    // Enhanced Cache Operation Pending Count\n");
    fprintf(fo, "    reg [7:0] pending_count;\n");
    fprintf(fo, "    reg [7:0] maint_queue_depth_reg;\n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        pending_count = 8'h0;\n");
    fprintf(fo, "        maint_queue_depth_reg = 8'h0;\n");
    fprintf(fo, "        for (integer j = 0; j < CACHE_OP_DEPTH; j = j + 1) begin\n");
    fprintf(fo, "            if (cache_op_queue_valid[j]) begin\n");
    fprintf(fo, "                pending_count = pending_count + 1;\n");
    fprintf(fo, "                if (!cache_op_queue_complete[j]) begin\n");
    fprintf(fo, "                    maint_queue_depth_reg = maint_queue_depth_reg + 1;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n");
    fprintf(fo, "    assign cache_op_pending_count = pending_count;\n");
    fprintf(fo, "    assign maint_queue_depth = maint_queue_depth_reg;\n\n");
    
    // Cache operation address range validation
    fprintf(fo, "    // Cache operation address validation\n");
    fprintf(fo, "    function cache_addr_valid;\n");
    fprintf(fo, "        input [WIDTH_AD-1:0] addr;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            cache_addr_valid = (addr >= cache_base_addr) && \n");
    fprintf(fo, "                              (addr < (cache_base_addr + cache_size));\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Enhanced Cache Operation Statistics and Advanced Monitoring (Phase 4)
    fprintf(fo, "    // Enhanced Cache Operation Statistics and Advanced Monitoring\n");
    fprintf(fo, "    reg [15:0] cache_op_cycles;\n");
    fprintf(fo, "    reg [7:0] max_pending_ops;\n");
    fprintf(fo, "    reg [15:0] maint_total_processing_time;   // Total processing time for all operations\n");
    fprintf(fo, "    reg [7:0] maint_successful_completions;   // Successfully completed operations\n");
    fprintf(fo, "    reg [7:0] maint_failed_operations;        // Failed/timed-out operations\n");
    fprintf(fo, "    reg [7:0] maint_conflicts_resolved;       // Number of conflicts resolved\n");
    fprintf(fo, "    reg [7:0] maint_priority_escalations;     // Priority escalation events\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            cache_op_cycles <= 16'h0;\n");
    fprintf(fo, "            max_pending_ops <= 8'h0;\n");
    fprintf(fo, "            maint_total_processing_time <= 16'h0;\n");
    fprintf(fo, "            maint_successful_completions <= 8'h0;\n");
    fprintf(fo, "            maint_failed_operations <= 8'h0;\n");
    fprintf(fo, "            maint_conflicts_resolved <= 8'h0;\n");
    fprintf(fo, "            maint_priority_escalations <= 8'h0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            if (|cache_op_active) begin\n");
    fprintf(fo, "                cache_op_cycles <= cache_op_cycles + 1;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Track maximum queue depth\n");
    fprintf(fo, "            if (pending_count > max_pending_ops) begin\n");
    fprintf(fo, "                max_pending_ops <= pending_count;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            if (maint_queue_depth_reg > maint_max_queue_depth) begin\n");
    fprintf(fo, "                maint_max_queue_depth <= maint_queue_depth_reg;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Advanced Phase 4 statistics tracking\n");
    fprintf(fo, "            for (integer j = 0; j < CACHE_OP_DEPTH; j = j + 1) begin\n");
    fprintf(fo, "                if (cache_op_queue_valid[j]) begin\n");
    fprintf(fo, "                    // Track total processing time\n");
    fprintf(fo, "                    if (!cache_op_queue_complete[j] && !cache_op_queue_timeout[j]) begin\n");
    fprintf(fo, "                        if (maint_total_processing_time < 16'hFFFF) begin\n");
    fprintf(fo, "                            maint_total_processing_time <= maint_total_processing_time + 1;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Track successful completions\n");
    fprintf(fo, "                    if (cache_op_queue_complete[j] && !cache_op_queue_timeout[j]) begin\n");
    fprintf(fo, "                        maint_successful_completions <= maint_successful_completions + 1;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Track failed operations\n");
    fprintf(fo, "                    if (cache_op_queue_timeout[j] || (cache_op_queue_retry_count[j] >= 8'h03)) begin\n");
    fprintf(fo, "                        maint_failed_operations <= maint_failed_operations + 1;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Track conflict resolutions\n");
    fprintf(fo, "                    if (cache_op_queue_conflict[j] && cache_op_queue_complete[j]) begin\n");
    fprintf(fo, "                        maint_conflicts_resolved <= maint_conflicts_resolved + 1;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Track priority escalations (operations that take longer get higher priority)\n");
    fprintf(fo, "                    if ((global_timestamp - cache_op_queue_timestamp[j]) > (maint_timeout_cycles >> 1) &&\n");
    fprintf(fo, "                        cache_op_queue_priority[j] < 4'hF) begin\n");
    fprintf(fo, "                        cache_op_queue_priority[j] <= cache_op_queue_priority[j] + 1;\n");
    fprintf(fo, "                        maint_priority_escalations <= maint_priority_escalations + 1;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    fprintf(fo, "endmodule\n");
    
    return 0;
}