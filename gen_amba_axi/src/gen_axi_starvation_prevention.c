//--------------------------------------------------------
// AXI Starvation Prevention Mechanisms
// Prevents masters from locking slaves indefinitely
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "gen_amba_axi.h"
#include "gen_axi_utils.h"

//--------------------------------------------------------
// Generate starvation prevention logic for arbiters
//--------------------------------------------------------
int gen_axi_starvation_prevention(unsigned int numM, unsigned int numS,
                                  char *prefix, axi_features_t *features, FILE *fo)
{
    int i, j;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// Starvation Prevention for %dx%d Matrix\n", numM, numS);
    fprintf(fo, "// Prevents masters from monopolizing slaves\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n\n");
    
    // Configurable timeout parameters
    fprintf(fo, "    // Starvation prevention parameters\n");
    fprintf(fo, "    parameter STARVATION_TIMEOUT = 16'd1024; // Cycles before forced unlock\n");
    fprintf(fo, "    parameter STARVATION_THRESHOLD = 8'd64;  // Max wait time difference\n");
    fprintf(fo, "    parameter ENABLE_STARVATION_PREVENTION = 1'b1;\n\n");
    
    // Generate per-slave starvation prevention
    fprintf(fo, "    generate\n");
    fprintf(fo, "        for (genvar s = 0; s < NUM_SLAVE; s = s + 1) begin : slave_starvation_prev\n");
    fprintf(fo, "            // Per-master request tracking for this slave\n");
    fprintf(fo, "            reg [15:0] request_time [NUM_MASTER-1:0];\n");
    fprintf(fo, "            reg [NUM_MASTER-1:0] requesting;\n");
    fprintf(fo, "            reg [15:0] current_grant_time;\n");
    fprintf(fo, "            reg [$clog2(NUM_MASTER)-1:0] current_master;\n");
    fprintf(fo, "            reg starvation_override;\n");
    fprintf(fo, "            reg [15:0] global_timer;\n\n");
    
    // Global timer
    fprintf(fo, "            // Global timer for timeout tracking\n");
    fprintf(fo, "            always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "                if (!ARESETn) begin\n");
    fprintf(fo, "                    global_timer <= 16'd0;\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    global_timer <= global_timer + 1;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n\n");
    
    // Request tracking
    fprintf(fo, "            // Track when each master starts requesting this slave\n");
    fprintf(fo, "            always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "                if (!ARESETn) begin\n");
    fprintf(fo, "                    integer m;\n");
    fprintf(fo, "                    for (m = 0; m < NUM_MASTER; m = m + 1) begin\n");
    fprintf(fo, "                        request_time[m] <= 16'd0;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    requesting <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    current_grant_time <= 16'd0;\n");
    fprintf(fo, "                    current_master <= 0;\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    integer m;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Update request timestamps\n");
    fprintf(fo, "                    for (m = 0; m < NUM_MASTER; m = m + 1) begin\n");
    fprintf(fo, "                        // Master starts requesting\n");
    fprintf(fo, "                        if ((aw_select[m][s] && M_AWVALID[m]) || \n");
    fprintf(fo, "                            (ar_select[m][s] && M_ARVALID[m])) begin\n");
    fprintf(fo, "                            if (!requesting[m]) begin\n");
    fprintf(fo, "                                request_time[m] <= global_timer;\n");
    fprintf(fo, "                                requesting[m] <= 1'b1;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end else begin\n");
    fprintf(fo, "                            // Master stops requesting\n");
    fprintf(fo, "                            requesting[m] <= 1'b0;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Track current grant\n");
    fprintf(fo, "                    if (|aw_grant[s] || |ar_grant[s]) begin\n");
    fprintf(fo, "                        for (m = 0; m < NUM_MASTER; m = m + 1) begin\n");
    fprintf(fo, "                            if (aw_grant[s][m] || ar_grant[s][m]) begin\n");
    fprintf(fo, "                                if (current_master != m) begin\n");
    fprintf(fo, "                                    current_master <= m;\n");
    fprintf(fo, "                                    current_grant_time <= global_timer;\n");
    fprintf(fo, "                                end\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n\n");
    
    // Starvation detection
    fprintf(fo, "            // Starvation detection logic\n");
    fprintf(fo, "            always @(*) begin\n");
    fprintf(fo, "                integer m;\n");
    fprintf(fo, "                reg timeout_detected;\n");
    fprintf(fo, "                reg [15:0] max_wait_time;\n");
    fprintf(fo, "                reg [$clog2(NUM_MASTER)-1:0] starved_master;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                timeout_detected = 1'b0;\n");
    fprintf(fo, "                max_wait_time = 16'd0;\n");
    fprintf(fo, "                starved_master = 0;\n");
    fprintf(fo, "                starvation_override = 1'b0;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                if (ENABLE_STARVATION_PREVENTION) begin\n");
    fprintf(fo, "                    // Check for timeout\n");
    fprintf(fo, "                    if ((global_timer - current_grant_time) > STARVATION_TIMEOUT) begin\n");
    fprintf(fo, "                        timeout_detected = 1'b1;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Find longest waiting master\n");
    fprintf(fo, "                    for (m = 0; m < NUM_MASTER; m = m + 1) begin\n");
    fprintf(fo, "                        if (requesting[m] && (m != current_master)) begin\n");
    fprintf(fo, "                            if ((global_timer - request_time[m]) > max_wait_time) begin\n");
    fprintf(fo, "                                max_wait_time = global_timer - request_time[m];\n");
    fprintf(fo, "                                starved_master = m;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Trigger starvation override\n");
    fprintf(fo, "                    if (timeout_detected || (max_wait_time > STARVATION_THRESHOLD)) begin\n");
    fprintf(fo, "                        if (requesting[starved_master]) begin\n");
    fprintf(fo, "                            starvation_override = 1'b1;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n\n");
    
    // Override grant generation
    fprintf(fo, "            // Override normal arbitration during starvation\n");
    fprintf(fo, "            wire [NUM_MASTER-1:0] starvation_aw_grant;\n");
    fprintf(fo, "            wire [NUM_MASTER-1:0] starvation_ar_grant;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            assign starvation_aw_grant = starvation_override ? \n");
    fprintf(fo, "                                        (1 << starved_master) : aw_grant[s];\n");
    fprintf(fo, "            assign starvation_ar_grant = starvation_override ? \n");
    fprintf(fo, "                                        (1 << starved_master) : ar_grant[s];\n\n");
    
    // Debug output
    fprintf(fo, "            // Debug monitoring (synthesis will optimize away if unused)\n");
    fprintf(fo, "            reg starvation_event;\n");
    fprintf(fo, "            always @(posedge ACLK) begin\n");
    fprintf(fo, "                if (starvation_override) begin\n");
    fprintf(fo, "                    starvation_event <= 1'b1;\n");
    fprintf(fo, "                    // $display(\"[STARVATION] Slave %%d: Override grant to master %%d (waited %%d cycles)\",\n");
    fprintf(fo, "                    //          s, starved_master, max_wait_time);\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    starvation_event <= 1'b0;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    
    fprintf(fo, "        end\n");
    fprintf(fo, "    endgenerate\n\n");
    
    // Statistics counters (optional)
    fprintf(fo, "    // Starvation prevention statistics (optional)\n");
    fprintf(fo, "    `ifdef STARVATION_STATS\n");
    fprintf(fo, "    reg [31:0] total_starvation_events;\n");
    fprintf(fo, "    reg [31:0] max_observed_wait_time;\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "        if (!ARESETn) begin\n");
    fprintf(fo, "            total_starvation_events <= 32'd0;\n");
    fprintf(fo, "            max_observed_wait_time <= 32'd0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            if (|starvation_event) begin\n");
    fprintf(fo, "                total_starvation_events <= total_starvation_events + 1;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            if (max_wait_time > max_observed_wait_time) begin\n");
    fprintf(fo, "                max_observed_wait_time <= max_wait_time;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n");
    fprintf(fo, "    `endif\n\n");
    
    return 0;
}

//--------------------------------------------------------
// Generate simplified timeout-based unlock mechanism
//--------------------------------------------------------
int gen_axi_timeout_unlock(unsigned int numM, unsigned int numS, 
                           char *prefix, FILE *fo)
{
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// Timeout-based Unlock Mechanism\n");
    fprintf(fo, "// Simple timeout to prevent indefinite locks\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n\n");
    
    fprintf(fo, "    // Timeout parameters\n");
    fprintf(fo, "    parameter LOCK_TIMEOUT = 16'd2048; // Maximum lock duration in cycles\n");
    fprintf(fo, "    parameter ENABLE_TIMEOUT_UNLOCK = 1'b1;\n\n");
    
    fprintf(fo, "    // Global timeout counter\n");
    fprintf(fo, "    reg [15:0] timeout_counter;\n");
    fprintf(fo, "    reg timeout_unlock;\n\n");
    
    fprintf(fo, "    always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "        if (!ARESETn) begin\n");
    fprintf(fo, "            timeout_counter <= 16'd0;\n");
    fprintf(fo, "            timeout_unlock <= 1'b0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            if (ENABLE_TIMEOUT_UNLOCK) begin\n");
    fprintf(fo, "                // Increment counter when any lock is active\n");
    fprintf(fo, "                if (locked) begin\n");
    fprintf(fo, "                    timeout_counter <= timeout_counter + 1;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Force unlock on timeout\n");
    fprintf(fo, "                    if (timeout_counter >= LOCK_TIMEOUT) begin\n");
    fprintf(fo, "                        timeout_unlock <= 1'b1;\n");
    fprintf(fo, "                        // $display(\"[TIMEOUT] Forced unlock after %%d cycles\", timeout_counter);\n");
    fprintf(fo, "                    end else begin\n");
    fprintf(fo, "                        timeout_unlock <= 1'b0;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    // Reset counter when not locked\n");
    fprintf(fo, "                    timeout_counter <= 16'd0;\n");
    fprintf(fo, "                    timeout_unlock <= 1'b0;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end else begin\n");
    fprintf(fo, "                timeout_unlock <= 1'b0;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    fprintf(fo, "    // Override unlock signal to include timeout\n");
    fprintf(fo, "    wire enhanced_unlock = unlock || timeout_unlock;\n\n");
    
    return 0;
}