//--------------------------------------------------------
// Optimized Arbitration for Large AXI Matrices (64x64)
// Supports Round-Robin, Fixed Priority, and QoS-based
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "gen_amba_axi.h"
#include "gen_axi_utils.h"

//--------------------------------------------------------
// Generate enhanced arbitration with multiple schemes
//--------------------------------------------------------
int gen_axi_arbiter_enhanced(unsigned int numM, unsigned int numS,
                             char *prefix, axi_features_t *features, FILE *fo)
{
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// Enhanced Arbitration for %dx%d Matrix\n", numM, numS);
    fprintf(fo, "// Supports: Round-Robin, Fixed Priority, QoS-based Priority\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n\n");
    
    // Parameters for arbitration schemes
    fprintf(fo, "    // Arbitration scheme selection\n");
    fprintf(fo, "    parameter ARB_SCHEME = \"ROUND_ROBIN\"; // \"ROUND_ROBIN\", \"FIXED_PRIORITY\", \"QOS_PRIORITY\"\n");
    fprintf(fo, "    parameter [NUM_MASTER-1:0] MASTER_PRIORITY = {NUM_MASTER{1'b1}}; // For fixed priority\n\n");
    
    // Generate arbitration logic for each slave
    fprintf(fo, "    generate\n");
    fprintf(fo, "        for (s = 0; s < NUM_SLAVE; s = s + 1) begin : enhanced_arb\n");
    fprintf(fo, "            // Per-slave arbitration state\n");
    fprintf(fo, "            reg [$clog2(NUM_MASTER)-1:0] rr_ptr_aw; // Round-robin pointer for AW\n");
    fprintf(fo, "            reg [$clog2(NUM_MASTER)-1:0] rr_ptr_ar; // Round-robin pointer for AR\n");
    fprintf(fo, "            reg [$clog2(NUM_MASTER)-1:0] last_grant_aw;\n");
    fprintf(fo, "            reg [$clog2(NUM_MASTER)-1:0] last_grant_ar;\n");
    fprintf(fo, "            reg [NUM_MASTER-1:0] aw_request;\n");
    fprintf(fo, "            reg [NUM_MASTER-1:0] ar_request;\n");
    fprintf(fo, "            \n");
    
    // Collect requests
    fprintf(fo, "            // Collect requests from all masters\n");
    fprintf(fo, "            always @(*) begin\n");
    fprintf(fo, "                integer m;\n");
    fprintf(fo, "                for (m = 0; m < NUM_MASTER; m = m + 1) begin\n");
    fprintf(fo, "                    aw_request[m] = aw_select[m][s] && M_AWVALID[m];\n");
    fprintf(fo, "                    ar_request[m] = ar_select[m][s] && M_ARVALID[m];\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n\n");
    
    // Round-robin arbitration
    fprintf(fo, "            // Round-robin arbitration logic\n");
    fprintf(fo, "            always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "                if (!ARESETn) begin\n");
    fprintf(fo, "                    rr_ptr_aw <= 0;\n");
    fprintf(fo, "                    rr_ptr_ar <= 0;\n");
    fprintf(fo, "                    last_grant_aw <= 0;\n");
    fprintf(fo, "                    last_grant_ar <= 0;\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    if (|aw_grant[s]) begin\n");
    fprintf(fo, "                        // Update round-robin pointer after grant\n");
    fprintf(fo, "                        integer i;\n");
    fprintf(fo, "                        for (i = 0; i < NUM_MASTER; i = i + 1) begin\n");
    fprintf(fo, "                            if (aw_grant[s][i]) begin\n");
    fprintf(fo, "                                last_grant_aw <= i;\n");
    fprintf(fo, "                                rr_ptr_aw <= (i == NUM_MASTER-1) ? 0 : i + 1;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    if (|ar_grant[s]) begin\n");
    fprintf(fo, "                        integer i;\n");
    fprintf(fo, "                        for (i = 0; i < NUM_MASTER; i = i + 1) begin\n");
    fprintf(fo, "                            if (ar_grant[s][i]) begin\n");
    fprintf(fo, "                                last_grant_ar <= i;\n");
    fprintf(fo, "                                ar_ptr <= (i == NUM_MASTER-1) ? 0 : i + 1;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n\n");
    
    // Grant generation based on scheme
    fprintf(fo, "            // Grant generation based on arbitration scheme\n");
    fprintf(fo, "            always @(*) begin\n");
    fprintf(fo, "                integer i, j;\n");
    fprintf(fo, "                reg found_aw, found_ar;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                aw_grant[s] = 0;\n");
    fprintf(fo, "                ar_grant[s] = 0;\n");
    fprintf(fo, "                found_aw = 0;\n");
    fprintf(fo, "                found_ar = 0;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                case (ARB_SCHEME)\n");
    
    // Round-robin scheme
    fprintf(fo, "                    \"ROUND_ROBIN\": begin\n");
    fprintf(fo, "                        // AW channel round-robin\n");
    fprintf(fo, "                        for (i = 0; i < NUM_MASTER && !found_aw; i = i + 1) begin\n");
    fprintf(fo, "                            j = (rr_ptr_aw + i) %% NUM_MASTER;\n");
    fprintf(fo, "                            if (aw_request[j] && !found_aw) begin\n");
    fprintf(fo, "                                aw_grant[s][j] = 1'b1;\n");
    fprintf(fo, "                                found_aw = 1'b1;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                        // AR channel round-robin\n");
    fprintf(fo, "                        for (i = 0; i < NUM_MASTER && !found_ar; i = i + 1) begin\n");
    fprintf(fo, "                            j = (rr_ptr_ar + i) %% NUM_MASTER;\n");
    fprintf(fo, "                            if (ar_request[j] && !found_ar) begin\n");
    fprintf(fo, "                                ar_grant[s][j] = 1'b1;\n");
    fprintf(fo, "                                found_ar = 1'b1;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    
    // Fixed priority scheme
    fprintf(fo, "                    \"FIXED_PRIORITY\": begin\n");
    fprintf(fo, "                        // Grant to highest priority requesting master\n");
    fprintf(fo, "                        for (i = 0; i < NUM_MASTER; i = i + 1) begin\n");
    fprintf(fo, "                            if (aw_request[i] && !found_aw && MASTER_PRIORITY[i]) begin\n");
    fprintf(fo, "                                aw_grant[s][i] = 1'b1;\n");
    fprintf(fo, "                                found_aw = 1'b1;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                            if (ar_request[i] && !found_ar && MASTER_PRIORITY[i]) begin\n");
    fprintf(fo, "                                ar_grant[s][i] = 1'b1;\n");
    fprintf(fo, "                                found_ar = 1'b1;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    
    // QoS-based priority (if QoS is enabled)
    if (features && features->enable_qos) {
        fprintf(fo, "                    \"QOS_PRIORITY\": begin\n");
        fprintf(fo, "                        // Find highest QoS request\n");
        fprintf(fo, "                        reg [3:0] max_qos_aw, max_qos_ar;\n");
        fprintf(fo, "                        reg [$clog2(NUM_MASTER)-1:0] max_qos_master_aw, max_qos_master_ar;\n");
        fprintf(fo, "                        \n");
        fprintf(fo, "                        max_qos_aw = 0;\n");
        fprintf(fo, "                        max_qos_ar = 0;\n");
        fprintf(fo, "                        max_qos_master_aw = 0;\n");
        fprintf(fo, "                        max_qos_master_ar = 0;\n");
        fprintf(fo, "                        \n");
        fprintf(fo, "                        // Find highest QoS for AW\n");
        fprintf(fo, "                        for (i = 0; i < NUM_MASTER; i = i + 1) begin\n");
        fprintf(fo, "                            if (aw_request[i] && (M_AWQOS[i] >= max_qos_aw)) begin\n");
        fprintf(fo, "                                max_qos_aw = M_AWQOS[i];\n");
        fprintf(fo, "                                max_qos_master_aw = i;\n");
        fprintf(fo, "                            end\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                        if (|aw_request) aw_grant[s][max_qos_master_aw] = 1'b1;\n");
        fprintf(fo, "                        \n");
        fprintf(fo, "                        // Find highest QoS for AR\n");
        fprintf(fo, "                        for (i = 0; i < NUM_MASTER; i = i + 1) begin\n");
        fprintf(fo, "                            if (ar_request[i] && (M_ARQOS[i] >= max_qos_ar)) begin\n");
        fprintf(fo, "                                max_qos_ar = M_ARQOS[i];\n");
        fprintf(fo, "                                max_qos_master_ar = i;\n");
        fprintf(fo, "                            end\n");
        fprintf(fo, "                        end\n");
        fprintf(fo, "                        if (|ar_request) ar_grant[s][max_qos_master_ar] = 1'b1;\n");
        fprintf(fo, "                    end\n");
    }
    
    fprintf(fo, "                    default: begin\n");
    fprintf(fo, "                        // Default to simple priority\n");
    fprintf(fo, "                        for (i = 0; i < NUM_MASTER; i = i + 1) begin\n");
    fprintf(fo, "                            if (aw_request[i] && !found_aw) begin\n");
    fprintf(fo, "                                aw_grant[s][i] = 1'b1;\n");
    fprintf(fo, "                                found_aw = 1'b1;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                            if (ar_request[i] && !found_ar) begin\n");
    fprintf(fo, "                                ar_grant[s][i] = 1'b1;\n");
    fprintf(fo, "                                found_ar = 1'b1;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                endcase\n");
    fprintf(fo, "            end\n\n");
    
    // Starvation prevention
    fprintf(fo, "            // Starvation prevention counter\n");
    fprintf(fo, "            reg [7:0] starvation_cnt [NUM_MASTER-1:0];\n");
    fprintf(fo, "            always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "                if (!ARESETn) begin\n");
    fprintf(fo, "                    integer k;\n");
    fprintf(fo, "                    for (k = 0; k < NUM_MASTER; k = k + 1)\n");
    fprintf(fo, "                        starvation_cnt[k] <= 0;\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    integer k;\n");
    fprintf(fo, "                    for (k = 0; k < NUM_MASTER; k = k + 1) begin\n");
    fprintf(fo, "                        if (aw_request[k] && !aw_grant[s][k]) begin\n");
    fprintf(fo, "                            // Increment starvation counter\n");
    fprintf(fo, "                            if (starvation_cnt[k] < 255)\n");
    fprintf(fo, "                                starvation_cnt[k] <= starvation_cnt[k] + 1;\n");
    fprintf(fo, "                        end else if (aw_grant[s][k]) begin\n");
    fprintf(fo, "                            // Reset on grant\n");
    fprintf(fo, "                            starvation_cnt[k] <= 0;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    
    fprintf(fo, "        end\n");
    fprintf(fo, "    endgenerate\n\n");
    
    return 0;
}

//--------------------------------------------------------
// Generate parameterizable priority settings
//--------------------------------------------------------
int gen_axi_priority_config(unsigned int numM, FILE *fo)
{
    int i;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// Priority Configuration for %d Masters\n", numM);
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    
    // Generate default priority settings
    fprintf(fo, "    // Master priority settings (higher value = higher priority)\n");
    fprintf(fo, "    parameter [3:0] PRIORITY_M0 = 4'd8;  // Default medium priority\n");
    
    for (i = 1; i < numM && i < 16; i++) {
        fprintf(fo, "    parameter [3:0] PRIORITY_M%d = 4'd%d;\n", i, (8 - (i % 8)));
    }
    
    if (numM > 16) {
        fprintf(fo, "    // For masters 16-%d, use generate block\n", numM-1);
        fprintf(fo, "    genvar p;\n");
        fprintf(fo, "    generate\n");
        fprintf(fo, "        for (p = 16; p < NUM_MASTER; p = p + 1) begin : priority_cfg\n");
        fprintf(fo, "            parameter [3:0] PRIORITY = 4'd4; // Lower priority for higher numbered masters\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "    endgenerate\n");
    }
    
    fprintf(fo, "\n    // Priority encoder for fast arbitration\n");
    fprintf(fo, "    function [$clog2(NUM_MASTER)-1:0] find_highest_priority;\n");
    fprintf(fo, "        input [NUM_MASTER-1:0] requests;\n");
    fprintf(fo, "        input [NUM_MASTER*4-1:0] priorities;\n");
    fprintf(fo, "        integer i;\n");
    fprintf(fo, "        reg [3:0] max_pri;\n");
    fprintf(fo, "        reg [$clog2(NUM_MASTER)-1:0] winner;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            max_pri = 0;\n");
    fprintf(fo, "            winner = 0;\n");
    fprintf(fo, "            for (i = 0; i < NUM_MASTER; i = i + 1) begin\n");
    fprintf(fo, "                if (requests[i] && (priorities[i*4 +: 4] > max_pri)) begin\n");
    fprintf(fo, "                    max_pri = priorities[i*4 +: 4];\n");
    fprintf(fo, "                    winner = i;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            find_highest_priority = winner;\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    return 0;
}