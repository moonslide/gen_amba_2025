//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// QoS (Quality of Service) Implementation
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "gen_amba_axi.h"
#include "gen_axi_utils.h"

//--------------------------------------------------------
// Generate QoS arbiter module
//--------------------------------------------------------
int gen_axi_qos_arbiter(unsigned int numM, unsigned int numS, 
                        char *prefix, axi_features_t *features, FILE *fo)
{
    int i, j;
    
    if (!features || !features->enable_qos) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// QoS Arbiter Module\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %saxi_qos_arbiter\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_QOS  = %d\n", features->width_qos);
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , WIDTH_AD   = 32)\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                    clk\n");
    fprintf(fo, "    , input  wire                    rst_n\n");
    
    // QoS inputs from masters
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    , input  wire [WIDTH_QOS-1:0]   m%d_awqos\n", i);
        fprintf(fo, "    , input  wire [WIDTH_QOS-1:0]   m%d_arqos\n", i);
        fprintf(fo, "    , input  wire                   m%d_awvalid\n", i);
        fprintf(fo, "    , input  wire                   m%d_arvalid\n", i);
    }
    
    // Grant outputs
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]  aw_grant\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]  ar_grant\n");
    fprintf(fo, ");\n\n");
    
    // QoS arbitration logic
    fprintf(fo, "    // QoS priority comparison\n");
    fprintf(fo, "    reg [WIDTH_QOS-1:0] aw_max_qos;\n");
    fprintf(fo, "    reg [WIDTH_QOS-1:0] ar_max_qos;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] aw_qos_mask;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] ar_qos_mask;\n\n");
    
    // Write channel QoS arbitration
    fprintf(fo, "    // Write channel QoS arbitration with starvation prevention\n");
    fprintf(fo, "    reg [WIDTH_QOS-1:0] aw_effective_qos [0:NUM_MASTER-1];\n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        aw_max_qos = 0;\n");
    fprintf(fo, "        aw_qos_mask = 0;\n");
    fprintf(fo, "        \n");
    fprintf(fo, "        // Calculate effective QoS (boost if starved)\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        aw_effective_qos[%d] = m%d_awqos;\n", i, i);
        fprintf(fo, "        if (aw_wait_cnt[%d] == STARVATION_THRESHOLD) begin\n", i);
        fprintf(fo, "            aw_effective_qos[%d] = {WIDTH_QOS{1'b1}}; // Max priority if starved\n", i);
        fprintf(fo, "        end\n");
    }
    fprintf(fo, "        \n");
    fprintf(fo, "        // Find maximum QoS value\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        if (m%d_awvalid && aw_effective_qos[%d] > aw_max_qos) begin\n", i, i);
        fprintf(fo, "            aw_max_qos = aw_effective_qos[%d];\n", i);
        fprintf(fo, "        end\n");
    }
    fprintf(fo, "        \n");
    fprintf(fo, "        // Create mask for masters with max QoS\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        if (m%d_awvalid && aw_effective_qos[%d] == aw_max_qos) begin\n", i, i);
        fprintf(fo, "            aw_qos_mask[%d] = 1'b1;\n", i);
        fprintf(fo, "        end\n");
    }
    fprintf(fo, "    end\n\n");
    
    // Read channel QoS arbitration
    fprintf(fo, "    // Read channel QoS arbitration with starvation prevention\n");
    fprintf(fo, "    reg [WIDTH_QOS-1:0] ar_effective_qos [0:NUM_MASTER-1];\n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        ar_max_qos = 0;\n");
    fprintf(fo, "        ar_qos_mask = 0;\n");
    fprintf(fo, "        \n");
    fprintf(fo, "        // Calculate effective QoS (boost if starved)\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        ar_effective_qos[%d] = m%d_arqos;\n", i, i);
        fprintf(fo, "        if (ar_wait_cnt[%d] == STARVATION_THRESHOLD) begin\n", i);
        fprintf(fo, "            ar_effective_qos[%d] = {WIDTH_QOS{1'b1}}; // Max priority if starved\n", i);
        fprintf(fo, "        end\n");
    }
    fprintf(fo, "        \n");
    fprintf(fo, "        // Find maximum QoS value\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        if (m%d_arvalid && ar_effective_qos[%d] > ar_max_qos) begin\n", i, i);
        fprintf(fo, "            ar_max_qos = ar_effective_qos[%d];\n", i);
        fprintf(fo, "        end\n");
    }
    fprintf(fo, "        \n");
    fprintf(fo, "        // Create mask for masters with max QoS\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        if (m%d_arvalid && ar_effective_qos[%d] == ar_max_qos) begin\n", i, i);
        fprintf(fo, "            ar_qos_mask[%d] = 1'b1;\n", i);
        fprintf(fo, "        end\n");
    }
    fprintf(fo, "    end\n\n");
    
    // Starvation prevention counters
    fprintf(fo, "    // Starvation prevention - boost priority after waiting too long\n");
    fprintf(fo, "    reg [7:0] aw_wait_cnt [0:NUM_MASTER-1];\n");
    fprintf(fo, "    reg [7:0] ar_wait_cnt [0:NUM_MASTER-1];\n");
    fprintf(fo, "    localparam STARVATION_THRESHOLD = 8'd255;\n\n");
    
    // Round-robin within same QoS level
    fprintf(fo, "    // Round-robin arbitration within same QoS level\n");
    int width_master = calc_width(numM);
    fprintf(fo, "    reg [%d:0] aw_rr_ptr; // log2(%d masters)\n", width_master-1, numM);
    fprintf(fo, "    reg [%d:0] ar_rr_ptr;\n\n", width_master-1);
    
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            aw_grant <= 0;\n");
    fprintf(fo, "            ar_grant <= 0;\n");
    fprintf(fo, "            aw_rr_ptr <= 0;\n");
    fprintf(fo, "            ar_rr_ptr <= 0;\n");
    fprintf(fo, "            for (integer i = 0; i < NUM_MASTER; i = i + 1) begin\n");
    fprintf(fo, "                aw_wait_cnt[i] <= 8'd0;\n");
    fprintf(fo, "                ar_wait_cnt[i] <= 8'd0;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            // Write channel grant\n");
    fprintf(fo, "            aw_grant <= 0;\n");
    fprintf(fo, "            for (integer i = 0; i < NUM_MASTER; i = i + 1) begin\n");
    fprintf(fo, "                integer idx = (aw_rr_ptr + i) %% NUM_MASTER;\n");
    fprintf(fo, "                if (aw_qos_mask[idx]) begin\n");
    fprintf(fo, "                    aw_grant[idx] <= 1'b1;\n");
    fprintf(fo, "                    aw_rr_ptr <= (idx + 1) %% NUM_MASTER;\n");
    fprintf(fo, "                    break;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Read channel grant\n");
    fprintf(fo, "            ar_grant <= 0;\n");
    fprintf(fo, "            for (integer i = 0; i < NUM_MASTER; i = i + 1) begin\n");
    fprintf(fo, "                integer idx = (ar_rr_ptr + i) %% NUM_MASTER;\n");
    fprintf(fo, "                if (ar_qos_mask[idx]) begin\n");
    fprintf(fo, "                    ar_grant[idx] <= 1'b1;\n");
    fprintf(fo, "                    ar_rr_ptr <= (idx + 1) %% NUM_MASTER;\n");
    fprintf(fo, "                    break;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Update starvation prevention counters\n");
    fprintf(fo, "            for (integer i = 0; i < NUM_MASTER; i = i + 1) begin\n");
    fprintf(fo, "                if (aw_grant[i]) begin\n");
    fprintf(fo, "                    aw_wait_cnt[i] <= 8'd0;\n");
    fprintf(fo, "                end else if (aw_qos_mask[i] && aw_wait_cnt[i] < STARVATION_THRESHOLD) begin\n");
    fprintf(fo, "                    aw_wait_cnt[i] <= aw_wait_cnt[i] + 1;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                if (ar_grant[i]) begin\n");
    fprintf(fo, "                    ar_wait_cnt[i] <= 8'd0;\n");
    fprintf(fo, "                end else if (ar_qos_mask[i] && ar_wait_cnt[i] < STARVATION_THRESHOLD) begin\n");
    fprintf(fo, "                    ar_wait_cnt[i] <= ar_wait_cnt[i] + 1;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Add QoS monitoring outputs
    fprintf(fo, "    // QoS monitoring signals for debug\n");
    fprintf(fo, "    `ifdef QOS_DEBUG\n");
    fprintf(fo, "    always @(posedge clk) begin\n");
    fprintf(fo, "        if (|aw_grant) begin\n");
    fprintf(fo, "            // $display(\"[QOS] Write grant with QoS %%d\", aw_max_qos); // Simplified\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "        if (|ar_grant) begin\n");
    fprintf(fo, "            // $display(\"[QOS] Read grant with QoS %%d\", ar_max_qos); // Simplified\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n");
    fprintf(fo, "    `endif\n\n");
    
    fprintf(fo, "endmodule\n");
    
    return 0;
}

//--------------------------------------------------------
// Add QoS signals to port connections
//--------------------------------------------------------
int gen_axi_qos_connections(unsigned int numM, unsigned int numS,
                            char *prefix, axi_features_t *features, FILE *fo)
{
    int i;
    
    if (!features || !features->enable_qos) return 0;
    
    fprintf(fo, "\n    // QoS signal connections\n");
    
    // Generate QoS arbiter instantiation
    fprintf(fo, "    %saxi_qos_arbiter #(\n", prefix);
    fprintf(fo, "        .NUM_MASTER(%d),\n", numM);
    fprintf(fo, "        .NUM_SLAVE(%d),\n", numS);
    fprintf(fo, "        .WIDTH_QOS(%d)\n", features->width_qos);
    fprintf(fo, "    ) u_qos_arbiter (\n");
    fprintf(fo, "        .clk(ACLK),\n");
    fprintf(fo, "        .rst_n(ARESETn),\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        .m%d_awqos(M%d_AWQOS),\n", i, i);
        fprintf(fo, "        .m%d_arqos(M%d_ARQOS),\n", i, i);
        fprintf(fo, "        .m%d_awvalid(M%d_AWVALID),\n", i, i);
        fprintf(fo, "        .m%d_arvalid(M%d_ARVALID),\n", i, i);
    }
    
    fprintf(fo, "        .aw_grant(qos_aw_grant),\n");
    fprintf(fo, "        .ar_grant(qos_ar_grant)\n");
    fprintf(fo, "    );\n\n");
    
    // Wire declarations for QoS grants
    fprintf(fo, "    wire [%d:0] qos_aw_grant;\n", numM-1);
    fprintf(fo, "    wire [%d:0] qos_ar_grant;\n\n", numM-1);
    
    return 0;
}