//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// Clock Domain Crossing (CDC) Implementation
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "gen_amba_axi.h"
#include "gen_axi_utils.h"

//--------------------------------------------------------
// Generate CDC module for AXI channels
//--------------------------------------------------------
int gen_axi_cdc(unsigned int numM, unsigned int numS,
               char *prefix, axi_features_t *features, FILE *fo)
{
    int i;
    
    if (!features || !features->enable_cdc || features->num_clock_domains < 2) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// AXI Clock Domain Crossing Module\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %saxi_cdc\n", prefix);
    fprintf(fo, "      #(parameter ADDR_WIDTH = 32\n");
    fprintf(fo, "              , DATA_WIDTH = 64\n");
    fprintf(fo, "              , ID_WIDTH   = 4\n");
    fprintf(fo, "              , FIFO_DEPTH = 16\n");
    fprintf(fo, "              , SYNC_STAGES = 3)\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      // Source clock domain\n");
    fprintf(fo, "      input  wire                    src_clk\n");
    fprintf(fo, "    , input  wire                    src_rstn\n");
    fprintf(fo, "      // Destination clock domain\n");
    fprintf(fo, "    , input  wire                    dst_clk\n");
    fprintf(fo, "    , input  wire                    dst_rstn\n");
    
    // AW channel - source side
    fprintf(fo, "      // AW channel - source side\n");
    fprintf(fo, "    , input  wire [ID_WIDTH-1:0]      src_awid\n");
    fprintf(fo, "    , input  wire [ADDR_WIDTH-1:0]    src_awaddr\n");
    fprintf(fo, "    , input  wire [7:0]               src_awlen\n");
    fprintf(fo, "    , input  wire [2:0]               src_awsize\n");
    fprintf(fo, "    , input  wire [1:0]               src_awburst\n");
    fprintf(fo, "    , input  wire                     src_awvalid\n");
    fprintf(fo, "    , output wire                     src_awready\n");
    
    // AW channel - destination side
    fprintf(fo, "      // AW channel - destination side\n");
    fprintf(fo, "    , output reg  [ID_WIDTH-1:0]      dst_awid\n");
    fprintf(fo, "    , output reg  [ADDR_WIDTH-1:0]    dst_awaddr\n");
    fprintf(fo, "    , output reg  [7:0]               dst_awlen\n");
    fprintf(fo, "    , output reg  [2:0]               dst_awsize\n");
    fprintf(fo, "    , output reg  [1:0]               dst_awburst\n");
    fprintf(fo, "    , output reg                      dst_awvalid\n");
    fprintf(fo, "    , input  wire                     dst_awready\n");
    
    // W channel - source side
    fprintf(fo, "      // W channel - source side\n");
    fprintf(fo, "    , input  wire [DATA_WIDTH-1:0]    src_wdata\n");
    fprintf(fo, "    , input  wire [DATA_WIDTH/8-1:0]  src_wstrb\n");
    fprintf(fo, "    , input  wire                     src_wlast\n");
    fprintf(fo, "    , input  wire                     src_wvalid\n");
    fprintf(fo, "    , output wire                     src_wready\n");
    
    // W channel - destination side
    fprintf(fo, "      // W channel - destination side\n");
    fprintf(fo, "    , output reg  [DATA_WIDTH-1:0]    dst_wdata\n");
    fprintf(fo, "    , output reg  [DATA_WIDTH/8-1:0]  dst_wstrb\n");
    fprintf(fo, "    , output reg                      dst_wlast\n");
    fprintf(fo, "    , output reg                      dst_wvalid\n");
    fprintf(fo, "    , input  wire                     dst_wready\n");
    
    fprintf(fo, ");\n\n");
    
    // Gray code conversion functions
    fprintf(fo, "    // Gray code conversion functions\n");
    fprintf(fo, "    function [$clog2(FIFO_DEPTH):0] bin2gray;\n");
    fprintf(fo, "        input [$clog2(FIFO_DEPTH):0] bin;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            bin2gray = bin ^ (bin >> 1);\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    fprintf(fo, "    function [$clog2(FIFO_DEPTH):0] gray2bin;\n");
    fprintf(fo, "        input [$clog2(FIFO_DEPTH):0] gray;\n");
    fprintf(fo, "        integer i;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            gray2bin[$clog2(FIFO_DEPTH)] = gray[$clog2(FIFO_DEPTH)];\n");
    fprintf(fo, "            for (i = $clog2(FIFO_DEPTH)-1; i >= 0; i = i - 1)\n");
    fprintf(fo, "                gray2bin[i] = gray2bin[i+1] ^ gray[i];\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // AW channel CDC FIFO
    fprintf(fo, "    // AW channel async FIFO\n");
    fprintf(fo, "    reg [ADDR_WIDTH+ID_WIDTH+13:0] aw_fifo [0:FIFO_DEPTH-1];\n");
    fprintf(fo, "    reg [$clog2(FIFO_DEPTH):0] aw_wr_ptr, aw_wr_ptr_gray;\n");
    fprintf(fo, "    reg [$clog2(FIFO_DEPTH):0] aw_rd_ptr, aw_rd_ptr_gray;\n");
    fprintf(fo, "    reg [$clog2(FIFO_DEPTH):0] aw_wr_ptr_sync [0:SYNC_STAGES-1];\n");
    fprintf(fo, "    reg [$clog2(FIFO_DEPTH):0] aw_rd_ptr_sync [0:SYNC_STAGES-1];\n\n");
    
    // W channel CDC FIFO
    fprintf(fo, "    // W channel async FIFO\n");
    fprintf(fo, "    reg [DATA_WIDTH+DATA_WIDTH/8:0] w_fifo [0:FIFO_DEPTH-1];\n");
    fprintf(fo, "    reg [$clog2(FIFO_DEPTH):0] w_wr_ptr, w_wr_ptr_gray;\n");
    fprintf(fo, "    reg [$clog2(FIFO_DEPTH):0] w_rd_ptr, w_rd_ptr_gray;\n");
    fprintf(fo, "    reg [$clog2(FIFO_DEPTH):0] w_wr_ptr_sync [0:SYNC_STAGES-1];\n");
    fprintf(fo, "    reg [$clog2(FIFO_DEPTH):0] w_rd_ptr_sync [0:SYNC_STAGES-1];\n\n");
    
    // AW channel write logic
    fprintf(fo, "    // AW channel write domain logic\n");
    fprintf(fo, "    always @(posedge src_clk or negedge src_rstn) begin\n");
    fprintf(fo, "        if (!src_rstn) begin\n");
    fprintf(fo, "            aw_wr_ptr <= 0;\n");
    fprintf(fo, "            aw_wr_ptr_gray <= 0;\n");
    fprintf(fo, "        end else if (src_awvalid && src_awready) begin\n");
    fprintf(fo, "            aw_fifo[aw_wr_ptr[$clog2(FIFO_DEPTH)-1:0]] <= {\n");
    fprintf(fo, "                src_awid, src_awaddr, src_awlen, src_awsize, src_awburst};\n");
    fprintf(fo, "            aw_wr_ptr <= aw_wr_ptr + 1;\n");
    fprintf(fo, "            aw_wr_ptr_gray <= bin2gray(aw_wr_ptr + 1);\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // W channel write logic
    fprintf(fo, "    // W channel write domain logic\n");
    fprintf(fo, "    always @(posedge src_clk or negedge src_rstn) begin\n");
    fprintf(fo, "        if (!src_rstn) begin\n");
    fprintf(fo, "            w_wr_ptr <= 0;\n");
    fprintf(fo, "            w_wr_ptr_gray <= 0;\n");
    fprintf(fo, "        end else if (src_wvalid && src_wready) begin\n");
    fprintf(fo, "            w_fifo[w_wr_ptr[$clog2(FIFO_DEPTH)-1:0]] <= {\n");
    fprintf(fo, "                src_wdata, src_wstrb, src_wlast};\n");
    fprintf(fo, "            w_wr_ptr <= w_wr_ptr + 1;\n");
    fprintf(fo, "            w_wr_ptr_gray <= bin2gray(w_wr_ptr + 1);\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Synchronizers
    fprintf(fo, "    // Synchronizers for AW channel\n");
    fprintf(fo, "    integer i;\n");
    fprintf(fo, "    always @(posedge dst_clk or negedge dst_rstn) begin\n");
    fprintf(fo, "        if (!dst_rstn) begin\n");
    fprintf(fo, "            for (i = 0; i < SYNC_STAGES; i = i + 1)\n");
    fprintf(fo, "                aw_wr_ptr_sync[i] <= 0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            aw_wr_ptr_sync[0] <= aw_wr_ptr_gray;\n");
    fprintf(fo, "            for (i = 1; i < SYNC_STAGES; i = i + 1)\n");
    fprintf(fo, "                aw_wr_ptr_sync[i] <= aw_wr_ptr_sync[i-1];\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // AW channel read logic
    fprintf(fo, "    // AW channel read domain logic\n");
    fprintf(fo, "    wire [$clog2(FIFO_DEPTH):0] aw_wr_ptr_dst = gray2bin(aw_wr_ptr_sync[SYNC_STAGES-1]);\n");
    fprintf(fo, "    wire aw_empty = (aw_rd_ptr == aw_wr_ptr_dst);\n\n");
    
    fprintf(fo, "    always @(posedge dst_clk or negedge dst_rstn) begin\n");
    fprintf(fo, "        if (!dst_rstn) begin\n");
    fprintf(fo, "            aw_rd_ptr <= 0;\n");
    fprintf(fo, "            aw_rd_ptr_gray <= 0;\n");
    fprintf(fo, "            dst_awvalid <= 0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            if (!aw_empty && (!dst_awvalid || dst_awready)) begin\n");
    fprintf(fo, "                {dst_awid, dst_awaddr, dst_awlen, dst_awsize, dst_awburst} <= \n");
    fprintf(fo, "                    aw_fifo[aw_rd_ptr[$clog2(FIFO_DEPTH)-1:0]];\n");
    fprintf(fo, "                dst_awvalid <= 1;\n");
    fprintf(fo, "                aw_rd_ptr <= aw_rd_ptr + 1;\n");
    fprintf(fo, "                aw_rd_ptr_gray <= bin2gray(aw_rd_ptr + 1);\n");
    fprintf(fo, "            end else if (dst_awvalid && dst_awready) begin\n");
    fprintf(fo, "                dst_awvalid <= 0;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Ready signals
    fprintf(fo, "    // Ready signal generation\n");
    fprintf(fo, "    assign src_awready = (aw_wr_ptr + 1 != gray2bin(aw_rd_ptr_sync[SYNC_STAGES-1]));\n");
    fprintf(fo, "    assign src_wready = (w_wr_ptr + 1 != gray2bin(w_rd_ptr_sync[SYNC_STAGES-1]));\n\n");
    
    fprintf(fo, "endmodule\n");
    
    return 0;
}