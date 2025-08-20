//--------------------------------------------------------
// Optimized AXI Generator for Large Matrices (up to 64x64)
// Copyright (c) 2025 - Enhanced for scalability
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include "gen_axi_utils.h"
#include "gen_amba_axi.h"

//--------------------------------------------------------
// Generate optimized AXI interconnect using generate blocks
//--------------------------------------------------------
int gen_axi_amba_optimized(unsigned int numM, unsigned int numS,
                           unsigned int widthAD, unsigned int widthDA,
                           char *module, char *prefix, int axi4,
                           axi_features_t *features, FILE *fo)
{
    if ((numM<2)||(numS<2)||(module==NULL)||(prefix==NULL)) return 1;
    
    // Calculate ID widths
    int width_cid = 0;
    int temp = numM - 1;
    while (temp > 0) {
        width_cid++;
        temp >>= 1;
    }
    if (width_cid == 0) width_cid = 1;
    
    // Adjust ID width for large matrices
    int width_id = (numM > 16) ? 8 : 4;
    
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "// Optimized AXI Interconnect for %dx%d Matrix\n", numM, numS);
    fprintf(fo, "// Using generate blocks for scalability\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %s\n", module);
    fprintf(fo, "      #(parameter NUM_MASTER  = %d\n", numM);
    fprintf(fo, "                , NUM_SLAVE   = %d\n", numS);
    fprintf(fo, "                , WIDTH_CID   = %d // Calculated for %d masters\n", width_cid, numM);
    fprintf(fo, "                , WIDTH_ID    = %d // Extended for large matrices\n", width_id);
    fprintf(fo, "                , WIDTH_AD    = %d\n", widthAD);
    fprintf(fo, "                , WIDTH_DA    = %d\n", widthDA);
    fprintf(fo, "                , WIDTH_DS    = (WIDTH_DA/8)\n");
    fprintf(fo, "                , WIDTH_SID   = (WIDTH_CID+WIDTH_ID)\n");
    
    // Add feature parameters if enabled
    if (features) {
        if (features->enable_qos) {
            fprintf(fo, "                , WIDTH_QOS   = %d\n", features->width_qos);
        }
        if (features->enable_region) {
            fprintf(fo, "                , WIDTH_REGION = %d\n", features->width_region);
        }
        if (features->enable_user) {
            fprintf(fo, "                , WIDTH_USER  = %d\n", features->width_user);
        }
    }
    
    fprintf(fo, "                )\n");
    fprintf(fo, "(\n");
    fprintf(fo, "    input  wire                      ACLK\n");
    fprintf(fo, "   ,input  wire                      ARESETn\n");
    
    // Master interfaces - using concatenated buses for Verilog-2001 compatibility
    fprintf(fo, "\n    // Master interfaces (concatenated for Verilog compatibility)\n");
    fprintf(fo, "   ,input  wire [NUM_MASTER*WIDTH_ID-1:0]    M_AWID_BUS\n");
    fprintf(fo, "   ,input  wire [NUM_MASTER*WIDTH_AD-1:0]    M_AWADDR_BUS\n");
    fprintf(fo, "   ,input  wire [7:0]                M_AWLEN   [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire [2:0]                M_AWSIZE  [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire [1:0]                M_AWBURST [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire                       M_AWVALID [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,output wire                       M_AWREADY [NUM_MASTER-1:0]\n");
    
    fprintf(fo, "   ,input  wire [WIDTH_DA-1:0]       M_WDATA   [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire [WIDTH_DS-1:0]       M_WSTRB   [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire                       M_WLAST   [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire                       M_WVALID  [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,output wire                       M_WREADY  [NUM_MASTER-1:0]\n");
    
    fprintf(fo, "   ,output wire [WIDTH_ID-1:0]       M_BID     [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,output wire [1:0]                M_BRESP   [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,output wire                       M_BVALID  [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire                       M_BREADY  [NUM_MASTER-1:0]\n");
    
    fprintf(fo, "   ,input  wire [WIDTH_ID-1:0]       M_ARID    [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire [WIDTH_AD-1:0]       M_ARADDR  [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire [7:0]                M_ARLEN   [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire [2:0]                M_ARSIZE  [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire [1:0]                M_ARBURST [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire                       M_ARVALID [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,output wire                       M_ARREADY [NUM_MASTER-1:0]\n");
    
    fprintf(fo, "   ,output wire [WIDTH_ID-1:0]       M_RID     [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,output wire [WIDTH_DA-1:0]       M_RDATA   [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,output wire [1:0]                M_RRESP   [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,output wire                       M_RLAST   [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,output wire                       M_RVALID  [NUM_MASTER-1:0]\n");
    fprintf(fo, "   ,input  wire                       M_RREADY  [NUM_MASTER-1:0]\n");
    
    fprintf(fo, "\n    // Slave interfaces (using arrays for scalability)\n");
    fprintf(fo, "   ,output wire [WIDTH_SID-1:0]      S_AWID    [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire [WIDTH_AD-1:0]       S_AWADDR  [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire [7:0]                S_AWLEN   [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire [2:0]                S_AWSIZE  [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire [1:0]                S_AWBURST [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire                       S_AWVALID [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,input  wire                       S_AWREADY [NUM_SLAVE-1:0]\n");
    
    fprintf(fo, "   ,output wire [WIDTH_DA-1:0]       S_WDATA   [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire [WIDTH_DS-1:0]       S_WSTRB   [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire                       S_WLAST   [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire                       S_WVALID  [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,input  wire                       S_WREADY  [NUM_SLAVE-1:0]\n");
    
    fprintf(fo, "   ,input  wire [WIDTH_SID-1:0]      S_BID     [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,input  wire [1:0]                S_BRESP   [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,input  wire                       S_BVALID  [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire                       S_BREADY  [NUM_SLAVE-1:0]\n");
    
    fprintf(fo, "   ,output wire [WIDTH_SID-1:0]      S_ARID    [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire [WIDTH_AD-1:0]       S_ARADDR  [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire [7:0]                S_ARLEN   [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire [2:0]                S_ARSIZE  [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire [1:0]                S_ARBURST [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire                       S_ARVALID [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,input  wire                       S_ARREADY [NUM_SLAVE-1:0]\n");
    
    fprintf(fo, "   ,input  wire [WIDTH_SID-1:0]      S_RID     [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,input  wire [WIDTH_DA-1:0]       S_RDATA   [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,input  wire [1:0]                S_RRESP   [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,input  wire                       S_RLAST   [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,input  wire                       S_RVALID  [NUM_SLAVE-1:0]\n");
    fprintf(fo, "   ,output wire                       S_RREADY  [NUM_SLAVE-1:0]\n");
    
    fprintf(fo, ");\n\n");
    
    // Internal signals
    fprintf(fo, "    // Internal arbitration signals\n");
    fprintf(fo, "    wire [NUM_SLAVE-1:0]  aw_select [NUM_MASTER-1:0];\n");
    fprintf(fo, "    wire [NUM_SLAVE-1:0]  ar_select [NUM_MASTER-1:0];\n");
    fprintf(fo, "    wire [NUM_MASTER-1:0] aw_grant  [NUM_SLAVE-1:0];\n");
    fprintf(fo, "    wire [NUM_MASTER-1:0] ar_grant  [NUM_SLAVE-1:0];\n");
    fprintf(fo, "    wire [NUM_MASTER-1:0] w_grant   [NUM_SLAVE-1:0];\n\n");
    
    // Address decoder using generate
    fprintf(fo, "    // Address decoder (optimized with generate)\n");
    fprintf(fo, "    genvar m, s;\n");
    fprintf(fo, "    generate\n");
    fprintf(fo, "        for (m = 0; m < NUM_MASTER; m = m + 1) begin : master_decode\n");
    fprintf(fo, "            // Simple address decode - can be customized\n");
    fprintf(fo, "            assign aw_select[m] = (M_AWADDR[m][31:28] < NUM_SLAVE) ? \n");
    fprintf(fo, "                                  (1 << M_AWADDR[m][31:28]) : 0;\n");
    fprintf(fo, "            assign ar_select[m] = (M_ARADDR[m][31:28] < NUM_SLAVE) ? \n");
    fprintf(fo, "                                  (1 << M_ARADDR[m][31:28]) : 0;\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endgenerate\n\n");
    
    // Enhanced arbitration with multiple schemes
    fprintf(fo, "    // Arbitration scheme: Round-Robin, Fixed Priority, or QoS-based\n");
    fprintf(fo, "    parameter ARB_SCHEME = \"ROUND_ROBIN\"; // Options: \"ROUND_ROBIN\", \"FIXED_PRIORITY\", \"QOS_PRIORITY\"\n");
    fprintf(fo, "    parameter [NUM_MASTER*4-1:0] MASTER_PRIORITY = {NUM_MASTER{4'd8}}; // Default priority\n\n");
    
    fprintf(fo, "    generate\n");
    fprintf(fo, "        for (s = 0; s < NUM_SLAVE; s = s + 1) begin : slave_arb\n");
    fprintf(fo, "            // Round-robin pointers\n");
    fprintf(fo, "            reg [$clog2(NUM_MASTER)-1:0] rr_ptr_aw;\n");
    fprintf(fo, "            reg [$clog2(NUM_MASTER)-1:0] rr_ptr_ar;\n");
    fprintf(fo, "            reg [NUM_MASTER-1:0] aw_request;\n");
    fprintf(fo, "            reg [NUM_MASTER-1:0] ar_request;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Collect requests\n");
    fprintf(fo, "            always @(*) begin\n");
    fprintf(fo, "                integer m;\n");
    fprintf(fo, "                for (m = 0; m < NUM_MASTER; m = m + 1) begin\n");
    fprintf(fo, "                    aw_request[m] = aw_select[m][s] && M_AWVALID[m];\n");
    fprintf(fo, "                    ar_request[m] = ar_select[m][s] && M_ARVALID[m];\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Update round-robin pointers\n");
    fprintf(fo, "            always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "                if (!ARESETn) begin\n");
    fprintf(fo, "                    rr_ptr_aw <= 0;\n");
    fprintf(fo, "                    rr_ptr_ar <= 0;\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    // Move pointer after grant\n");
    fprintf(fo, "                    if (|aw_grant[s]) begin\n");
    fprintf(fo, "                        integer i;\n");
    fprintf(fo, "                        for (i = 0; i < NUM_MASTER; i = i + 1)\n");
    fprintf(fo, "                            if (aw_grant[s][i]) rr_ptr_aw <= (i + 1) %% NUM_MASTER;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    if (|ar_grant[s]) begin\n");
    fprintf(fo, "                        integer i;\n");
    fprintf(fo, "                        for (i = 0; i < NUM_MASTER; i = i + 1)\n");
    fprintf(fo, "                            if (ar_grant[s][i]) rr_ptr_ar <= (i + 1) %% NUM_MASTER;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Grant generation based on arbitration scheme\n");
    fprintf(fo, "            always @(*) begin\n");
    fprintf(fo, "                integer i, j;\n");
    fprintf(fo, "                reg found_aw, found_ar;\n");
    fprintf(fo, "                aw_grant[s] = 0;\n");
    fprintf(fo, "                ar_grant[s] = 0;\n");
    fprintf(fo, "                found_aw = 0;\n");
    fprintf(fo, "                found_ar = 0;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                if (ARB_SCHEME == \"ROUND_ROBIN\") begin\n");
    fprintf(fo, "                    // True round-robin arbitration\n");
    fprintf(fo, "                    for (i = 0; i < NUM_MASTER && !found_aw; i = i + 1) begin\n");
    fprintf(fo, "                        j = (rr_ptr_aw + i) %% NUM_MASTER;\n");
    fprintf(fo, "                        if (aw_request[j]) begin\n");
    fprintf(fo, "                            aw_grant[s][j] = 1'b1;\n");
    fprintf(fo, "                            found_aw = 1'b1;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    for (i = 0; i < NUM_MASTER && !found_ar; i = i + 1) begin\n");
    fprintf(fo, "                        j = (rr_ptr_ar + i) %% NUM_MASTER;\n");
    fprintf(fo, "                        if (ar_request[j]) begin\n");
    fprintf(fo, "                            ar_grant[s][j] = 1'b1;\n");
    fprintf(fo, "                            found_ar = 1'b1;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end else if (ARB_SCHEME == \"FIXED_PRIORITY\") begin\n");
    fprintf(fo, "                    // Fixed priority based on MASTER_PRIORITY\n");
    fprintf(fo, "                    reg [3:0] max_pri_aw, max_pri_ar;\n");
    fprintf(fo, "                    reg [$clog2(NUM_MASTER)-1:0] winner_aw, winner_ar;\n");
    fprintf(fo, "                    max_pri_aw = 0;\n");
    fprintf(fo, "                    max_pri_ar = 0;\n");
    fprintf(fo, "                    for (i = 0; i < NUM_MASTER; i = i + 1) begin\n");
    fprintf(fo, "                        if (aw_request[i] && MASTER_PRIORITY[i*4 +: 4] >= max_pri_aw) begin\n");
    fprintf(fo, "                            max_pri_aw = MASTER_PRIORITY[i*4 +: 4];\n");
    fprintf(fo, "                            winner_aw = i;\n");
    fprintf(fo, "                            found_aw = 1'b1;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                        if (ar_request[i] && MASTER_PRIORITY[i*4 +: 4] >= max_pri_ar) begin\n");
    fprintf(fo, "                            max_pri_ar = MASTER_PRIORITY[i*4 +: 4];\n");
    fprintf(fo, "                            winner_ar = i;\n");
    fprintf(fo, "                            found_ar = 1'b1;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    if (found_aw) aw_grant[s][winner_aw] = 1'b1;\n");
    fprintf(fo, "                    if (found_ar) ar_grant[s][winner_ar] = 1'b1;\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    // Default: simple priority (master 0 highest)\n");
    fprintf(fo, "                    for (i = 0; i < NUM_MASTER; i = i + 1) begin\n");
    fprintf(fo, "                        if (aw_request[i] && !found_aw) begin\n");
    fprintf(fo, "                            aw_grant[s][i] = 1'b1;\n");
    fprintf(fo, "                            found_aw = 1'b1;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                        if (ar_request[i] && !found_ar) begin\n");
    fprintf(fo, "                            ar_grant[s][i] = 1'b1;\n");
    fprintf(fo, "                            found_ar = 1'b1;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endgenerate\n\n");
    
    // Connection matrix using generate
    fprintf(fo, "    // Connection matrix (optimized with generate)\n");
    fprintf(fo, "    generate\n");
    fprintf(fo, "        // Master to Slave connections\n");
    fprintf(fo, "        for (s = 0; s < NUM_SLAVE; s = s + 1) begin : slave_conn\n");
    fprintf(fo, "            // Mux master signals to slave\n");
    fprintf(fo, "            always @(*) begin\n");
    fprintf(fo, "                S_AWID[s]    = 0;\n");
    fprintf(fo, "                S_AWADDR[s]  = 0;\n");
    fprintf(fo, "                S_AWLEN[s]   = 0;\n");
    fprintf(fo, "                S_AWSIZE[s]  = 0;\n");
    fprintf(fo, "                S_AWBURST[s] = 0;\n");
    fprintf(fo, "                S_AWVALID[s] = 0;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                for (integer m = 0; m < NUM_MASTER; m = m + 1) begin\n");
    fprintf(fo, "                    if (aw_grant[s][m]) begin\n");
    fprintf(fo, "                        S_AWID[s]    = {m[WIDTH_CID-1:0], M_AWID[m]};\n");
    fprintf(fo, "                        S_AWADDR[s]  = M_AWADDR[m];\n");
    fprintf(fo, "                        S_AWLEN[s]   = M_AWLEN[m];\n");
    fprintf(fo, "                        S_AWSIZE[s]  = M_AWSIZE[m];\n");
    fprintf(fo, "                        S_AWBURST[s] = M_AWBURST[m];\n");
    fprintf(fo, "                        S_AWVALID[s] = M_AWVALID[m];\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Similar for AR, W channels\n");
    fprintf(fo, "            always @(*) begin\n");
    fprintf(fo, "                S_ARID[s]    = 0;\n");
    fprintf(fo, "                S_ARADDR[s]  = 0;\n");
    fprintf(fo, "                S_ARLEN[s]   = 0;\n");
    fprintf(fo, "                S_ARSIZE[s]  = 0;\n");
    fprintf(fo, "                S_ARBURST[s] = 0;\n");
    fprintf(fo, "                S_ARVALID[s] = 0;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                for (integer m = 0; m < NUM_MASTER; m = m + 1) begin\n");
    fprintf(fo, "                    if (ar_grant[s][m]) begin\n");
    fprintf(fo, "                        S_ARID[s]    = {m[WIDTH_CID-1:0], M_ARID[m]};\n");
    fprintf(fo, "                        S_ARADDR[s]  = M_ARADDR[m];\n");
    fprintf(fo, "                        S_ARLEN[s]   = M_ARLEN[m];\n");
    fprintf(fo, "                        S_ARSIZE[s]  = M_ARSIZE[m];\n");
    fprintf(fo, "                        S_ARBURST[s] = M_ARBURST[m];\n");
    fprintf(fo, "                        S_ARVALID[s] = M_ARVALID[m];\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "        \n");
    fprintf(fo, "        // Slave to Master response connections\n");
    fprintf(fo, "        for (m = 0; m < NUM_MASTER; m = m + 1) begin : master_resp\n");
    fprintf(fo, "            // Response demux\n");
    fprintf(fo, "            always @(*) begin\n");
    fprintf(fo, "                M_BID[m]     = 0;\n");
    fprintf(fo, "                M_BRESP[m]   = 0;\n");
    fprintf(fo, "                M_BVALID[m]  = 0;\n");
    fprintf(fo, "                M_RID[m]     = 0;\n");
    fprintf(fo, "                M_RDATA[m]   = 0;\n");
    fprintf(fo, "                M_RRESP[m]   = 0;\n");
    fprintf(fo, "                M_RLAST[m]   = 0;\n");
    fprintf(fo, "                M_RVALID[m]  = 0;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                for (integer s = 0; s < NUM_SLAVE; s = s + 1) begin\n");
    fprintf(fo, "                    if (S_BVALID[s] && (S_BID[s][WIDTH_SID-1:WIDTH_ID] == m)) begin\n");
    fprintf(fo, "                        M_BID[m]    = S_BID[s][WIDTH_ID-1:0];\n");
    fprintf(fo, "                        M_BRESP[m]  = S_BRESP[s];\n");
    fprintf(fo, "                        M_BVALID[m] = S_BVALID[s];\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    if (S_RVALID[s] && (S_RID[s][WIDTH_SID-1:WIDTH_ID] == m)) begin\n");
    fprintf(fo, "                        M_RID[m]    = S_RID[s][WIDTH_ID-1:0];\n");
    fprintf(fo, "                        M_RDATA[m]  = S_RDATA[s];\n");
    fprintf(fo, "                        M_RRESP[m]  = S_RRESP[s];\n");
    fprintf(fo, "                        M_RLAST[m]  = S_RLAST[s];\n");
    fprintf(fo, "                        M_RVALID[m] = S_RVALID[s];\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Ready signal routing\n");
    fprintf(fo, "            always @(*) begin\n");
    fprintf(fo, "                M_AWREADY[m] = 0;\n");
    fprintf(fo, "                M_WREADY[m]  = 0;\n");
    fprintf(fo, "                M_ARREADY[m] = 0;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                for (integer s = 0; s < NUM_SLAVE; s = s + 1) begin\n");
    fprintf(fo, "                    if (aw_grant[s][m]) M_AWREADY[m] = S_AWREADY[s];\n");
    fprintf(fo, "                    if (w_grant[s][m])  M_WREADY[m]  = S_WREADY[s];\n");
    fprintf(fo, "                    if (ar_grant[s][m]) M_ARREADY[m] = S_ARREADY[s];\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endgenerate\n");
    
    fprintf(fo, "\nendmodule\n");
    
    return 0;
}