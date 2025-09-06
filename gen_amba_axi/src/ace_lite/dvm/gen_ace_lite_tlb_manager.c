//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite TLB (Translation Lookaside Buffer) Manager Implementation
// Manages TLB invalidation, ASID tracking, and virtual address management
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "../../gen_amba_axi.h"
#include "../../gen_axi_utils.h"

//--------------------------------------------------------
// Generate TLB (Translation Lookaside Buffer) manager logic
// Implements TLB invalidation, ASID management, and VA tracking
//--------------------------------------------------------
int gen_ace_lite_tlb_manager(unsigned int numM, unsigned int numS, 
                             unsigned int widthAD, unsigned int widthDA,
                             char *prefix, axi_features_t *features, FILE *fo)
{
    int i, j;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite TLB (Translation Lookaside Buffer) Manager\n");
    fprintf(fo, "// Manages TLB invalidation, ASID tracking, and virtual address management\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %sace_lite_tlb_manager\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , TLB_ENTRIES = 128)  // TLB entries per master\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                    clk\n");
    fprintf(fo, "    , input  wire                    rst_n\n");
    
    // Add master interface connections for TLB operations
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d TLB interface\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]    m%d_tlb_va         // Virtual address\n", i);
        fprintf(fo, "    , input  wire [15:0]            m%d_tlb_asid       // Address Space ID\n", i);
        fprintf(fo, "    , input  wire [2:0]             m%d_tlb_op         // TLB operation type\n", i);
        fprintf(fo, "    , input  wire                   m%d_tlb_valid      // TLB request valid\n", i);
        fprintf(fo, "    , output reg                    m%d_tlb_ready      // TLB request ready\n", i);
        fprintf(fo, "    , output reg                    m%d_tlb_complete   // TLB operation complete\n", i);
        fprintf(fo, "    , output reg  [1:0]             m%d_tlb_resp       // TLB response\n", i);
        fprintf(fo, "    , output reg  [31:0]            m%d_tlb_entries_inv // Entries invalidated\n", i);
    }
    
    fprintf(fo, "    // Global TLB status outputs\n");
    fprintf(fo, "    , output reg                    tlb_invalidation_active  // TLB invalidation in progress\n");
    fprintf(fo, "    , output reg  [31:0]            tlb_total_invalidations  // Total invalidations\n");
    fprintf(fo, "    , output reg  [31:0]            tlb_entries_per_master [NUM_MASTER-1:0] // Valid entries per master\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0] tlb_maintenance_error   // TLB error per master\n");
    fprintf(fo, ");\n\n");
    
    // TLB operation type definitions
    fprintf(fo, "    // TLB Operation Type Definitions\n");
    fprintf(fo, "    localparam [2:0] TLB_INV_ALL        = 3'b000;  // Invalidate all entries\n");
    fprintf(fo, "    localparam [2:0] TLB_INV_ASID       = 3'b001;  // Invalidate by ASID\n");
    fprintf(fo, "    localparam [2:0] TLB_INV_VA         = 3'b010;  // Invalidate by Virtual Address\n");
    fprintf(fo, "    localparam [2:0] TLB_INV_VA_ASID    = 3'b011;  // Invalidate by VA and ASID\n");
    fprintf(fo, "    localparam [2:0] TLB_INV_RANGE      = 3'b100;  // Invalidate address range\n");
    fprintf(fo, "    localparam [2:0] TLB_FLUSH          = 3'b101;  // Flush all entries\n");
    fprintf(fo, "    localparam [2:0] TLB_LOOKUP         = 3'b110;  // TLB lookup (read-only)\n");
    fprintf(fo, "    localparam [2:0] TLB_SYNC           = 3'b111;  // TLB synchronization\n\n");
    
    // TLB response types
    fprintf(fo, "    // TLB Response Types\n");
    fprintf(fo, "    localparam [1:0] TLB_RESP_OK        = 2'b00;  // Operation successful\n");
    fprintf(fo, "    localparam [1:0] TLB_RESP_ERROR     = 2'b01;  // Operation failed\n");
    fprintf(fo, "    localparam [1:0] TLB_RESP_PARTIAL   = 2'b10;  // Partial invalidation\n");
    fprintf(fo, "    localparam [1:0] TLB_RESP_TIMEOUT   = 2'b11;  // Operation timed out\n\n");
    
    // TLB entry structure (simplified representation)
    fprintf(fo, "    // TLB Entry Structure (per master)\n");
    fprintf(fo, "    // Each master maintains its own TLB entries\n");
    fprintf(fo, "    reg [WIDTH_AD-13:0] tlb_tag [NUM_MASTER-1:0][TLB_ENTRIES-1:0];     // VA tag (page aligned)\n");
    fprintf(fo, "    reg [15:0]          tlb_asid [NUM_MASTER-1:0][TLB_ENTRIES-1:0];    // Address Space ID\n");
    fprintf(fo, "    reg                 tlb_valid [NUM_MASTER-1:0][TLB_ENTRIES-1:0];   // Valid bit\n");
    fprintf(fo, "    reg [7:0]           tlb_age [NUM_MASTER-1:0][TLB_ENTRIES-1:0];     // Age for replacement\n");
    fprintf(fo, "    reg                 tlb_global [NUM_MASTER-1:0][TLB_ENTRIES-1:0];  // Global translation\n");
    fprintf(fo, "    \n");
    
    // TLB operation state tracking
    fprintf(fo, "    // TLB Operation State Tracking\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] tlb_op_pending;      // Operations pending per master\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] tlb_op_complete;     // Operations complete per master\n");
    fprintf(fo, "    reg [31:0] invalidation_counter [NUM_MASTER-1:0]; // Invalidations per operation\n");
    fprintf(fo, "    \n");
    
    // TLB maintenance logic
    fprintf(fo, "    // TLB Maintenance and Invalidation Logic\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            // Reset all TLB entries and state\n");
    fprintf(fo, "            tlb_invalidation_active <= 1'b0;\n");
    fprintf(fo, "            tlb_total_invalidations <= 32'h00000000;\n");
    fprintf(fo, "            tlb_maintenance_error <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            tlb_op_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            tlb_op_complete <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Initialize per-master states\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d TLB initialization\n", i);
        fprintf(fo, "            m%d_tlb_ready <= 1'b1;\n", i);
        fprintf(fo, "            m%d_tlb_complete <= 1'b0;\n", i);
        fprintf(fo, "            m%d_tlb_resp <= TLB_RESP_OK;\n", i);
        fprintf(fo, "            m%d_tlb_entries_inv <= 32'h00000000;\n", i);
        fprintf(fo, "            tlb_entries_per_master[%d] <= 32'h00000000;\n", i);
        fprintf(fo, "            invalidation_counter[%d] <= 32'h00000000;\n", i);
        fprintf(fo, "            \n");
        fprintf(fo, "            // Clear all TLB entries for master %d\n", i);
        fprintf(fo, "            for (integer k = 0; k < TLB_ENTRIES; k = k + 1) begin\n");
        fprintf(fo, "                tlb_valid[%d][k] <= 1'b0;\n", i);
        fprintf(fo, "                tlb_tag[%d][k] <= {(WIDTH_AD-12){1'b0}};\n", i);
        fprintf(fo, "                tlb_asid[%d][k] <= 16'h0000;\n", i);
        fprintf(fo, "                tlb_age[%d][k] <= 8'h00;\n", i);
        fprintf(fo, "                tlb_global[%d][k] <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
    }
    
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            // Process TLB operations for each master\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d TLB operation processing\n", i);
        fprintf(fo, "            if (m%d_tlb_valid && m%d_tlb_ready) begin\n", i, i);
        fprintf(fo, "                // Start TLB operation\n");
        fprintf(fo, "                tlb_op_pending[%d] <= 1'b1;\n", i);
        fprintf(fo, "                m%d_tlb_ready <= 1'b0;\n", i);
        fprintf(fo, "                invalidation_counter[%d] <= 32'h00000000;\n", i);
        fprintf(fo, "                tlb_invalidation_active <= 1'b1;\n");
        fprintf(fo, "                \n");
        fprintf(fo, "                case (m%d_tlb_op)\n", i);
        fprintf(fo, "                    TLB_INV_ALL: begin\n");
        fprintf(fo, "                        // Invalidate all TLB entries\n");
        fprintf(fo, "                        for (integer k = 0; k < TLB_ENTRIES; k = k + 1) begin\n");
        fprintf(fo, "                            if (tlb_valid[%d][k]) begin\n", i);
        fprintf(fo, "                                tlb_valid[%d][k] <= 1'b0;\n", i);
        fprintf(fo, "                                invalidation_counter[%d] <= invalidation_counter[%d] + 1;\n", i, i);
        fprintf(fo, "                            end\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                        tlb_entries_per_master[%d] <= 32'h00000000;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    \n");
        fprintf(fo, "                    TLB_INV_ASID: begin\n");
        fprintf(fo, "                        // Invalidate entries matching ASID\n");
        fprintf(fo, "                        for (integer k = 0; k < TLB_ENTRIES; k = k + 1) begin\n");
        fprintf(fo, "                            if (tlb_valid[%d][k] && (tlb_asid[%d][k] == m%d_tlb_asid) && !tlb_global[%d][k]) begin\n", i, i, i, i);
        fprintf(fo, "                                tlb_valid[%d][k] <= 1'b0;\n", i);
        fprintf(fo, "                                invalidation_counter[%d] <= invalidation_counter[%d] + 1;\n", i, i);
        fprintf(fo, "                            end\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    \n");
        fprintf(fo, "                    TLB_INV_VA: begin\n");
        fprintf(fo, "                        // Invalidate entries matching Virtual Address\n");
        fprintf(fo, "                        for (integer k = 0; k < TLB_ENTRIES; k = k + 1) begin\n");
        fprintf(fo, "                            if (tlb_valid[%d][k] && (tlb_tag[%d][k] == m%d_tlb_va[WIDTH_AD-1:12])) begin\n", i, i, i);
        fprintf(fo, "                                tlb_valid[%d][k] <= 1'b0;\n", i);
        fprintf(fo, "                                invalidation_counter[%d] <= invalidation_counter[%d] + 1;\n", i, i);
        fprintf(fo, "                            end\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    \n");
        fprintf(fo, "                    TLB_INV_VA_ASID: begin\n");
        fprintf(fo, "                        // Invalidate entries matching both VA and ASID\n");
        fprintf(fo, "                        for (integer k = 0; k < TLB_ENTRIES; k = k + 1) begin\n");
        fprintf(fo, "                            if (tlb_valid[%d][k] && \n", i);
        fprintf(fo, "                                (tlb_tag[%d][k] == m%d_tlb_va[WIDTH_AD-1:12]) &&\n", i, i);
        fprintf(fo, "                                (tlb_asid[%d][k] == m%d_tlb_asid) && !tlb_global[%d][k]) begin\n", i, i, i);
        fprintf(fo, "                                tlb_valid[%d][k] <= 1'b0;\n", i);
        fprintf(fo, "                                invalidation_counter[%d] <= invalidation_counter[%d] + 1;\n", i, i);
        fprintf(fo, "                            end\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    \n");
        fprintf(fo, "                    TLB_FLUSH: begin\n");
        fprintf(fo, "                        // Flush all entries including global ones\n");
        fprintf(fo, "                        for (integer k = 0; k < TLB_ENTRIES; k = k + 1) begin\n");
        fprintf(fo, "                            if (tlb_valid[%d][k]) begin\n", i);
        fprintf(fo, "                                tlb_valid[%d][k] <= 1'b0;\n", i);
        fprintf(fo, "                                tlb_global[%d][k] <= 1'b0;\n", i);
        fprintf(fo, "                                invalidation_counter[%d] <= invalidation_counter[%d] + 1;\n", i, i);
        fprintf(fo, "                            end\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                        tlb_entries_per_master[%d] <= 32'h00000000;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    \n");
        fprintf(fo, "                    TLB_LOOKUP: begin\n");
        fprintf(fo, "                        // TLB lookup operation (read-only)\n");
        fprintf(fo, "                        // Count matching entries\n");
        fprintf(fo, "                        for (integer k = 0; k < TLB_ENTRIES; k = k + 1) begin\n");
        fprintf(fo, "                            if (tlb_valid[%d][k] && \n", i);
        fprintf(fo, "                                (tlb_tag[%d][k] == m%d_tlb_va[WIDTH_AD-1:12]) &&\n", i, i);
        fprintf(fo, "                                ((tlb_asid[%d][k] == m%d_tlb_asid) || tlb_global[%d][k])) begin\n", i, i, i);
        fprintf(fo, "                                invalidation_counter[%d] <= invalidation_counter[%d] + 1;\n", i, i);
        fprintf(fo, "                            end\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    \n");
        fprintf(fo, "                    TLB_SYNC: begin\n");
        fprintf(fo, "                        // TLB synchronization - no actual operation\n");
        fprintf(fo, "                        invalidation_counter[%d] <= 32'h00000001;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    \n");
        fprintf(fo, "                    default: begin\n");
        fprintf(fo, "                        // Unknown operation\n");
        fprintf(fo, "                        tlb_maintenance_error[%d] <= 1'b1;\n", i);
        fprintf(fo, "                        invalidation_counter[%d] <= 32'h00000000;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                endcase\n");
        fprintf(fo, "                \n");
        fprintf(fo, "            end else if (tlb_op_pending[%d] && !tlb_op_complete[%d]) begin\n", i, i);
        fprintf(fo, "                // Complete the TLB operation\n");
        fprintf(fo, "                tlb_op_complete[%d] <= 1'b1;\n", i);
        fprintf(fo, "                tlb_op_pending[%d] <= 1'b0;\n", i);
        fprintf(fo, "                m%d_tlb_ready <= 1'b1;\n", i);
        fprintf(fo, "                m%d_tlb_complete <= 1'b1;\n", i);
        fprintf(fo, "                m%d_tlb_entries_inv <= invalidation_counter[%d];\n", i, i);
        fprintf(fo, "                \n");
        fprintf(fo, "                // Update statistics\n");
        fprintf(fo, "                tlb_total_invalidations <= tlb_total_invalidations + invalidation_counter[%d];\n", i);
        fprintf(fo, "                \n");
        fprintf(fo, "                // Set response based on operation result\n");
        fprintf(fo, "                if (tlb_maintenance_error[%d]) begin\n", i);
        fprintf(fo, "                    m%d_tlb_resp <= TLB_RESP_ERROR;\n", i);
        fprintf(fo, "                end else if (invalidation_counter[%d] == 0 && m%d_tlb_op != TLB_SYNC) begin\n", i, i);
        fprintf(fo, "                    m%d_tlb_resp <= TLB_RESP_PARTIAL;\n", i);
        fprintf(fo, "                end else begin\n");
        fprintf(fo, "                    m%d_tlb_resp <= TLB_RESP_OK;\n", i);
        fprintf(fo, "                end\n");
        fprintf(fo, "                \n");
        fprintf(fo, "            end else if (tlb_op_complete[%d]) begin\n", i);
        fprintf(fo, "                // Clear completion flag\n");
        fprintf(fo, "                tlb_op_complete[%d] <= 1'b0;\n", i);
        fprintf(fo, "                m%d_tlb_complete <= 1'b0;\n", i);
        fprintf(fo, "                \n");
        fprintf(fo, "                // Clear error flag\n");
        fprintf(fo, "                tlb_maintenance_error[%d] <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Update valid entry count for master %d\n", i);
        fprintf(fo, "            tlb_entries_per_master[%d] <= 0;\n", i);
        fprintf(fo, "            for (integer k = 0; k < TLB_ENTRIES; k = k + 1) begin\n");
        fprintf(fo, "                if (tlb_valid[%d][k]) begin\n", i);
        fprintf(fo, "                    tlb_entries_per_master[%d] <= tlb_entries_per_master[%d] + 1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
    }
    
    fprintf(fo, "            // Update global TLB invalidation status\n");
    fprintf(fo, "            tlb_invalidation_active <= |tlb_op_pending;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // TLB age management for replacement policy
    fprintf(fo, "    // TLB Age Management for LRU Replacement\n");
    fprintf(fo, "    // Ages all TLB entries periodically to support replacement\n");
    fprintf(fo, "    reg [15:0] age_counter;\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            age_counter <= 16'h0000;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            age_counter <= age_counter + 1;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Age TLB entries every 256 cycles\n");
    fprintf(fo, "            if (age_counter[7:0] == 8'h00) begin\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                // Age master %d TLB entries\n", i);
        fprintf(fo, "                for (integer k = 0; k < TLB_ENTRIES; k = k + 1) begin\n");
        fprintf(fo, "                    if (tlb_valid[%d][k] && tlb_age[%d][k] < 8'hFF) begin\n", i, i);
        fprintf(fo, "                        tlb_age[%d][k] <= tlb_age[%d][k] + 1;\n", i, i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
    }
    
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // TLB statistics and monitoring
    fprintf(fo, "    // TLB Statistics and Monitoring\n");
    fprintf(fo, "    // Provides visibility into TLB usage and effectiveness\n");
    fprintf(fo, "    reg [31:0] tlb_hit_count [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [31:0] tlb_miss_count [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [31:0] tlb_access_count [NUM_MASTER-1:0];\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Note: In a real implementation, TLB hits/misses would be tracked\n");
    fprintf(fo, "    // based on actual address translation requests from the CPU/masters\n");
    fprintf(fo, "    // This is a simplified monitoring framework\n\n");
    
    fprintf(fo, "endmodule\n\n");
    
    return 0;
}