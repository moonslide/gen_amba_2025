//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite Exclusive Access Monitor Implementation
// Tracks and manages exclusive access operations per master
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "../../gen_amba_axi.h"
#include "../../gen_axi_utils.h"

//--------------------------------------------------------
// Generate ACE-Lite exclusive access monitor module
//--------------------------------------------------------
int gen_ace_lite_exclusive_monitor(unsigned int numM, unsigned int numS, 
                                   unsigned int widthAD, unsigned int widthDA,
                                   char *prefix, axi_features_t *features, FILE *fo)
{
    int i;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite Exclusive Access Monitor\n");
    fprintf(fo, "// Tracks exclusive access operations per master/ID pair\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %sace_lite_exclusive_monitor\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , EXCLUSIVE_DEPTH = 16) // Depth of exclusive tracking\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                       clk\n");
    fprintf(fo, "    , input  wire                       rst_n\n");
    
    // Master interface inputs for exclusive access tracking
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d exclusive access interface\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]       m%d_awid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]       m%d_awaddr\n", i);
        fprintf(fo, "    , input  wire [2:0]                m%d_awsize\n", i);
        fprintf(fo, "    , input  wire                      m%d_awlock\n", i);
        fprintf(fo, "    , input  wire                      m%d_awvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_awready\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]       m%d_arid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]       m%d_araddr\n", i);
        fprintf(fo, "    , input  wire [2:0]                m%d_arsize\n", i);
        fprintf(fo, "    , input  wire                      m%d_arlock\n", i);
        fprintf(fo, "    , input  wire                      m%d_arvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_arready\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]       m%d_bid\n", i);
        fprintf(fo, "    , input  wire [1:0]                m%d_bresp\n", i);
        fprintf(fo, "    , input  wire                      m%d_bvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_bready\n", i);
    }
    
    // Exclusive access control inputs
    fprintf(fo, "    // Exclusive access control\n");
    fprintf(fo, "    , input  wire                       exclusive_enable\n");
    fprintf(fo, "    , input  wire                       exclusive_clear_all\n");
    
    // Exclusive access status outputs  
    fprintf(fo, "    // Exclusive access status outputs\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       exclusive_active\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       exclusive_granted\n");
    fprintf(fo, "    , output wire [7:0]                  exclusive_count\n");
    fprintf(fo, "    , output reg  [7:0]                  exclusive_violations\n");
    fprintf(fo, "    , output reg  [7:0]                  exclusive_successes\n");
    
    fprintf(fo, ");\n\n");
    
    // Exclusive access tracking structure
    fprintf(fo, "    // Exclusive access tracking structure\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] exclusive_addr [0:EXCLUSIVE_DEPTH-1];\n");
    fprintf(fo, "    reg [WIDTH_ID-1:0] exclusive_id [0:EXCLUSIVE_DEPTH-1];\n");
    fprintf(fo, "    reg [7:0] exclusive_master [0:EXCLUSIVE_DEPTH-1];\n");
    fprintf(fo, "    reg [2:0] exclusive_size [0:EXCLUSIVE_DEPTH-1];\n");
    fprintf(fo, "    reg [EXCLUSIVE_DEPTH-1:0] exclusive_valid;\n");
    fprintf(fo, "    reg [$clog2(EXCLUSIVE_DEPTH)-1:0] exclusive_wr_ptr;\n");
    fprintf(fo, "    reg [7:0] exclusive_count_reg;\n\n");
    
    // Exclusive access address alignment
    fprintf(fo, "    // Exclusive access address alignment\n");
    fprintf(fo, "    function [WIDTH_AD-1:0] align_exclusive_addr;\n");
    fprintf(fo, "        input [WIDTH_AD-1:0] addr;\n");
    fprintf(fo, "        input [2:0] size;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            case (size)\n");
    fprintf(fo, "                3'b000: align_exclusive_addr = addr;                    // 1 byte\n");
    fprintf(fo, "                3'b001: align_exclusive_addr = {addr[WIDTH_AD-1:1], 1'b0};   // 2 bytes\n");
    fprintf(fo, "                3'b010: align_exclusive_addr = {addr[WIDTH_AD-1:2], 2'b0};   // 4 bytes\n");
    fprintf(fo, "                3'b011: align_exclusive_addr = {addr[WIDTH_AD-1:3], 3'b0};   // 8 bytes\n");
    fprintf(fo, "                3'b100: align_exclusive_addr = {addr[WIDTH_AD-1:4], 4'b0};   // 16 bytes\n");
    fprintf(fo, "                3'b101: align_exclusive_addr = {addr[WIDTH_AD-1:5], 5'b0};   // 32 bytes\n");
    fprintf(fo, "                3'b110: align_exclusive_addr = {addr[WIDTH_AD-1:6], 6'b0};   // 64 bytes\n");
    fprintf(fo, "                3'b111: align_exclusive_addr = {addr[WIDTH_AD-1:7], 7'b0};   // 128 bytes\n");
    fprintf(fo, "            endcase\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Exclusive access match detection
    fprintf(fo, "    // Exclusive access match detection\n");
    fprintf(fo, "    function exclusive_match;\n");
    fprintf(fo, "        input [WIDTH_AD-1:0] addr1, addr2;\n");
    fprintf(fo, "        input [WIDTH_ID-1:0] id1, id2;\n");
    fprintf(fo, "        input [7:0] master1, master2;\n");
    fprintf(fo, "        input [2:0] size1, size2;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            exclusive_match = (align_exclusive_addr(addr1, size1) == align_exclusive_addr(addr2, size2)) &&\n");
    fprintf(fo, "                             (id1 == id2) && (master1 == master2);\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Main exclusive access monitoring logic
    fprintf(fo, "    // Exclusive access monitoring logic\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            exclusive_valid <= {EXCLUSIVE_DEPTH{1'b0}};\n");
    fprintf(fo, "            exclusive_wr_ptr <= 0;\n");
    fprintf(fo, "            exclusive_count_reg <= 8'h0;\n");
    fprintf(fo, "            exclusive_violations <= 8'h0;\n");
    fprintf(fo, "            exclusive_successes <= 8'h0;\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            exclusive_active[%d] <= 1'b0;\n", i);
        fprintf(fo, "            exclusive_granted[%d] <= 1'b0;\n", i);
    }
    fprintf(fo, "        end else if (exclusive_enable) begin\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Clear all exclusive accesses if requested\n");
    fprintf(fo, "            if (exclusive_clear_all) begin\n");
    fprintf(fo, "                exclusive_valid <= {EXCLUSIVE_DEPTH{1'b0}};\n");
    fprintf(fo, "                exclusive_count_reg <= 8'h0;\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                exclusive_active[%d] <= 1'b0;\n", i);
        fprintf(fo, "                exclusive_granted[%d] <= 1'b0;\n", i);
    }
    fprintf(fo, "            end else begin\n");
    fprintf(fo, "                \n");
    
    // Process each master for exclusive read operations
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                // Master %d exclusive read processing\n", i);
        fprintf(fo, "                if (m%d_arvalid && m%d_arready && m%d_arlock) begin\n", i, i, i);
        fprintf(fo, "                    // Record exclusive read\n");
        fprintf(fo, "                    if (!exclusive_valid[exclusive_wr_ptr]) begin\n");
        fprintf(fo, "                        exclusive_addr[exclusive_wr_ptr] <= align_exclusive_addr(m%d_araddr, m%d_arsize);\n", i, i);
        fprintf(fo, "                        exclusive_id[exclusive_wr_ptr] <= m%d_arid;\n", i);
        fprintf(fo, "                        exclusive_master[exclusive_wr_ptr] <= %d;\n", i);
        fprintf(fo, "                        exclusive_size[exclusive_wr_ptr] <= m%d_arsize;\n", i);
        fprintf(fo, "                        exclusive_valid[exclusive_wr_ptr] <= 1'b1;\n");
        fprintf(fo, "                        exclusive_wr_ptr <= (exclusive_wr_ptr + 1) %% EXCLUSIVE_DEPTH;\n");
        fprintf(fo, "                        exclusive_count_reg <= exclusive_count_reg + 1;\n");
        fprintf(fo, "                        exclusive_active[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                \n");
        fprintf(fo, "                // Master %d exclusive write processing\n", i);
        fprintf(fo, "                if (m%d_awvalid && m%d_awready && m%d_awlock) begin\n", i, i, i);
        fprintf(fo, "                    exclusive_granted[%d] <= 1'b0;  // Default to not granted\n", i);
        fprintf(fo, "                    \n");
        fprintf(fo, "                    // Check for matching exclusive read\n");
        fprintf(fo, "                    for (integer j = 0; j < EXCLUSIVE_DEPTH; j = j + 1) begin\n");
        fprintf(fo, "                        if (exclusive_valid[j] && \n");
        fprintf(fo, "                            exclusive_match(exclusive_addr[j], align_exclusive_addr(m%d_awaddr, m%d_awsize),\n", i, i);
        fprintf(fo, "                                          exclusive_id[j], m%d_awid,\n", i);
        fprintf(fo, "                                          exclusive_master[j], %d,\n", i);
        fprintf(fo, "                                          exclusive_size[j], m%d_awsize)) begin\n", i);
        fprintf(fo, "                            // Grant exclusive access\n");
        fprintf(fo, "                            exclusive_granted[%d] <= 1'b1;\n", i);
        fprintf(fo, "                            // Clear the exclusive reservation\n");
        fprintf(fo, "                            exclusive_valid[j] <= 1'b0;\n");
        fprintf(fo, "                            exclusive_count_reg <= exclusive_count_reg - 1;\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                \n");
        fprintf(fo, "                // Master %d write response processing\n", i);
        fprintf(fo, "                if (m%d_bvalid && m%d_bready) begin\n", i, i);
        fprintf(fo, "                    if (exclusive_granted[%d]) begin\n", i);
        fprintf(fo, "                        if (m%d_bresp == 2'b01) begin // EXOKAY\n", i);
        fprintf(fo, "                            exclusive_successes <= exclusive_successes + 1;\n");
        fprintf(fo, "                        end else begin // OKAY or error\n");
        fprintf(fo, "                            exclusive_violations <= exclusive_violations + 1;\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                        exclusive_granted[%d] <= 1'b0;\n", i);
        fprintf(fo, "                        exclusive_active[%d] <= 1'b0;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                \n");
    }
    
    // Clear exclusive reservations on intervening writes
    fprintf(fo, "                // Clear exclusive reservations on intervening normal writes\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                if (m%d_awvalid && m%d_awready && !m%d_awlock) begin\n", i, i, i);
        fprintf(fo, "                    // Clear any exclusive reservations that overlap with this address\n");
        fprintf(fo, "                    for (integer j = 0; j < EXCLUSIVE_DEPTH; j = j + 1) begin\n");
        fprintf(fo, "                        if (exclusive_valid[j] && \n");
        fprintf(fo, "                            (align_exclusive_addr(exclusive_addr[j], exclusive_size[j]) == \n");
        fprintf(fo, "                             align_exclusive_addr(m%d_awaddr, m%d_awsize))) begin\n", i, i);
        fprintf(fo, "                            exclusive_valid[j] <= 1'b0;\n");
        fprintf(fo, "                            exclusive_count_reg <= exclusive_count_reg - 1;\n");
        fprintf(fo, "                            exclusive_violations <= exclusive_violations + 1;\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
    }
    
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    fprintf(fo, "    // Output assignments\n");
    fprintf(fo, "    assign exclusive_count = exclusive_count_reg;\n\n");
    
    fprintf(fo, "endmodule\n");
    
    return 0;
}