//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite Barrier Synchronization Module Generator
// Memory and synchronization barrier handling
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "../../gen_amba_axi.h"
#include "../../gen_axi_utils.h"

//--------------------------------------------------------
// Generate ACE-Lite barrier synchronization module
//--------------------------------------------------------
int gen_ace_lite_barrier_sync(unsigned int numM, unsigned int numS, unsigned int widthAD, unsigned int widthDA,
                              char *prefix, axi_features_t *features, FILE *fo)
{
    int i;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite Barrier Synchronization\n");
    fprintf(fo, "// Memory and synchronization barrier transaction handling\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %sace_lite_barrier_sync\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , BARRIER_TIMEOUT = 1000) // Timeout cycles\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                       clk\n");
    fprintf(fo, "    , input  wire                       rst_n\n");
    
    // Master barrier interface inputs
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d barrier interface\n", i);
        fprintf(fo, "    , input  wire [1:0]                m%d_awbar\n", i);
        fprintf(fo, "    , input  wire [1:0]                m%d_arbar\n", i);
        fprintf(fo, "    , input  wire                      m%d_awvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_awready\n", i);
        fprintf(fo, "    , input  wire                      m%d_arvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_arready\n", i);
        fprintf(fo, "    , input  wire                      m%d_bvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_bready\n", i);
        fprintf(fo, "    , input  wire                      m%d_rvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_rready\n", i);
        fprintf(fo, "    , input  wire                      m%d_rlast\n", i);
    }
    
    // Barrier control inputs
    fprintf(fo, "    // Barrier control\n");
    fprintf(fo, "    , input  wire                       barrier_enable\n");
    fprintf(fo, "    , input  wire                       global_barrier_request\n");
    fprintf(fo, "    , input  wire [NUM_MASTER-1:0]      master_barrier_override\n");
    
    // Barrier status outputs
    fprintf(fo, "    // Barrier status outputs\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       barrier_active\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       barrier_block\n");
    fprintf(fo, "    , output reg                         global_barrier_active\n");
    fprintf(fo, "    , output wire [NUM_MASTER-1:0]       barrier_timeout\n");
    fprintf(fo, "    , output reg  [15:0]                 pending_transactions [NUM_MASTER-1:0]\n");
    
    fprintf(fo, ");\n\n");
    
    // Barrier type encodings
    fprintf(fo, "    // Barrier type encodings (ACE-Lite)\n");
    fprintf(fo, "    localparam [1:0] BAR_NORMAL_ACCESS = 2'b00;\n");
    fprintf(fo, "    localparam [1:0] BAR_MEMORY_BARRIER = 2'b01;\n");
    fprintf(fo, "    localparam [1:0] BAR_RESERVED = 2'b10;\n");
    fprintf(fo, "    localparam [1:0] BAR_SYNC_BARRIER = 2'b11;\n\n");
    
    // Barrier state encodings
    fprintf(fo, "    // Barrier state machine encodings\n");
    fprintf(fo, "    localparam [2:0] BARRIER_IDLE = 3'b000;\n");
    fprintf(fo, "    localparam [2:0] BARRIER_PENDING = 3'b001;\n");
    fprintf(fo, "    localparam [2:0] BARRIER_DRAINING = 3'b010;\n");
    fprintf(fo, "    localparam [2:0] BARRIER_ACTIVE = 3'b011;\n");
    fprintf(fo, "    localparam [2:0] BARRIER_COMPLETE = 3'b100;\n");
    fprintf(fo, "    localparam [2:0] BARRIER_TIMEOUT_STATE = 3'b111;\n\n");
    
    // Master barrier state tracking
    fprintf(fo, "    // Master barrier state tracking\n");
    fprintf(fo, "    reg [2:0] barrier_state [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [1:0] barrier_type [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [15:0] outstanding_writes [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [15:0] outstanding_reads [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [15:0] barrier_timeout_counter [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] barrier_timeout_flag;\n\n");
    
    // Global barrier coordination
    fprintf(fo, "    // Global barrier coordination\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] global_barrier_participants;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] global_barrier_ready;\n");
    fprintf(fo, "    reg global_barrier_state;\n");
    fprintf(fo, "    wire all_masters_barrier_ready = &(global_barrier_ready | ~global_barrier_participants);\n\n");
    
    // Outstanding transaction counters
    fprintf(fo, "    // Outstanding transaction tracking\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d transaction tracking\n", i);
        fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
        fprintf(fo, "        if (!rst_n) begin\n");
        fprintf(fo, "            outstanding_writes[%d] <= 16'h0;\n", i);
        fprintf(fo, "            outstanding_reads[%d] <= 16'h0;\n", i);
        fprintf(fo, "        end else begin\n");
        fprintf(fo, "            // Write transaction tracking\n");
        fprintf(fo, "            case ({m%d_awvalid & m%d_awready, m%d_bvalid & m%d_bready})\n", i, i, i, i);
        fprintf(fo, "                2'b10: outstanding_writes[%d] <= outstanding_writes[%d] + 1; // New write\n", i, i);
        fprintf(fo, "                2'b01: outstanding_writes[%d] <= outstanding_writes[%d] - 1; // Write complete\n", i, i);
        fprintf(fo, "                2'b11: outstanding_writes[%d] <= outstanding_writes[%d];     // Both\n", i, i);
        fprintf(fo, "                default: outstanding_writes[%d] <= outstanding_writes[%d];   // No change\n", i, i);
        fprintf(fo, "            endcase\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Read transaction tracking\n");
        fprintf(fo, "            case ({m%d_arvalid & m%d_arready, m%d_rvalid & m%d_rready & m%d_rlast})\n", i, i, i, i, i);
        fprintf(fo, "                2'b10: outstanding_reads[%d] <= outstanding_reads[%d] + 1; // New read\n", i, i);
        fprintf(fo, "                2'b01: outstanding_reads[%d] <= outstanding_reads[%d] - 1; // Read complete\n", i, i);
        fprintf(fo, "                2'b11: outstanding_reads[%d] <= outstanding_reads[%d];     // Both\n", i, i);
        fprintf(fo, "                default: outstanding_reads[%d] <= outstanding_reads[%d];   // No change\n", i, i);
        fprintf(fo, "            endcase\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "    end\n\n");
    }
    
    // Barrier state machines for each master
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d barrier state machine\n", i);
        fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
        fprintf(fo, "        if (!rst_n) begin\n");
        fprintf(fo, "            barrier_state[%d] <= BARRIER_IDLE;\n", i);
        fprintf(fo, "            barrier_type[%d] <= BAR_NORMAL_ACCESS;\n", i);
        fprintf(fo, "            barrier_timeout_counter[%d] <= 16'h0;\n", i);
        fprintf(fo, "            barrier_timeout_flag[%d] <= 1'b0;\n", i);
        fprintf(fo, "        end else begin\n");
        fprintf(fo, "            case (barrier_state[%d])\n", i);
        
        // IDLE state
        fprintf(fo, "                BARRIER_IDLE: begin\n");
        fprintf(fo, "                    barrier_timeout_counter[%d] <= 16'h0;\n", i);
        fprintf(fo, "                    barrier_timeout_flag[%d] <= 1'b0;\n", i);
        fprintf(fo, "                    // Detect barrier transaction\n");
        fprintf(fo, "                    if ((m%d_awvalid && m%d_awbar != BAR_NORMAL_ACCESS) ||\n", i, i);
        fprintf(fo, "                        (m%d_arvalid && m%d_arbar != BAR_NORMAL_ACCESS)) begin\n", i, i);
        fprintf(fo, "                        barrier_state[%d] <= BARRIER_PENDING;\n", i);
        fprintf(fo, "                        barrier_type[%d] <= m%d_awvalid ? m%d_awbar : m%d_arbar;\n", i, i, i, i);
        fprintf(fo, "                    end else if (global_barrier_request && !master_barrier_override[%d]) begin\n", i);
        fprintf(fo, "                        barrier_state[%d] <= BARRIER_DRAINING;\n", i);
        fprintf(fo, "                        barrier_type[%d] <= BAR_SYNC_BARRIER;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        
        // PENDING state
        fprintf(fo, "                BARRIER_PENDING: begin\n");
        fprintf(fo, "                    // Wait for barrier transaction to be accepted\n");
        fprintf(fo, "                    if ((m%d_awvalid && m%d_awready) || (m%d_arvalid && m%d_arready)) begin\n", i, i, i, i);
        fprintf(fo, "                        barrier_state[%d] <= BARRIER_DRAINING;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    barrier_timeout_counter[%d] <= barrier_timeout_counter[%d] + 1;\n", i, i);
        fprintf(fo, "                    if (barrier_timeout_counter[%d] >= BARRIER_TIMEOUT) begin\n", i);
        fprintf(fo, "                        barrier_state[%d] <= BARRIER_TIMEOUT_STATE;\n", i);
        fprintf(fo, "                        barrier_timeout_flag[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        
        // DRAINING state
        fprintf(fo, "                BARRIER_DRAINING: begin\n");
        fprintf(fo, "                    // Wait for all outstanding transactions to complete\n");
        fprintf(fo, "                    if (barrier_type[%d] == BAR_MEMORY_BARRIER) begin\n", i);
        fprintf(fo, "                        // Memory barrier: drain writes only\n");
        fprintf(fo, "                        if (outstanding_writes[%d] == 16'h0) begin\n", i);
        fprintf(fo, "                            barrier_state[%d] <= BARRIER_ACTIVE;\n", i);
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end else if (barrier_type[%d] == BAR_SYNC_BARRIER) begin\n", i);
        fprintf(fo, "                        // Sync barrier: drain all transactions\n");
        fprintf(fo, "                        if ((outstanding_writes[%d] == 16'h0) && (outstanding_reads[%d] == 16'h0)) begin\n", i, i);
        fprintf(fo, "                            barrier_state[%d] <= BARRIER_ACTIVE;\n", i);
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end\n");
        fprintf(fo, "                    barrier_timeout_counter[%d] <= barrier_timeout_counter[%d] + 1;\n", i, i);
        fprintf(fo, "                    if (barrier_timeout_counter[%d] >= BARRIER_TIMEOUT) begin\n", i);
        fprintf(fo, "                        barrier_state[%d] <= BARRIER_TIMEOUT_STATE;\n", i);
        fprintf(fo, "                        barrier_timeout_flag[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        
        // ACTIVE state
        fprintf(fo, "                BARRIER_ACTIVE: begin\n");
        fprintf(fo, "                    // Barrier is active, block new transactions\n");
        fprintf(fo, "                    if (barrier_type[%d] == BAR_SYNC_BARRIER && global_barrier_request) begin\n", i);
        fprintf(fo, "                        // Wait for global barrier completion\n");
        fprintf(fo, "                        if (all_masters_barrier_ready) begin\n");
        fprintf(fo, "                            barrier_state[%d] <= BARRIER_COMPLETE;\n", i);
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end else begin\n");
        fprintf(fo, "                        // Local barrier completes immediately after draining\n");
        fprintf(fo, "                        barrier_state[%d] <= BARRIER_COMPLETE;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        
        // COMPLETE state
        fprintf(fo, "                BARRIER_COMPLETE: begin\n");
        fprintf(fo, "                    // Barrier complete, return to idle\n");
        fprintf(fo, "                    barrier_state[%d] <= BARRIER_IDLE;\n", i);
        fprintf(fo, "                end\n");
        
        // TIMEOUT state
        fprintf(fo, "                BARRIER_TIMEOUT_STATE: begin\n");
        fprintf(fo, "                    // Barrier timeout, force completion\n");
        fprintf(fo, "                    barrier_state[%d] <= BARRIER_IDLE;\n", i);
        fprintf(fo, "                end\n");
        
        fprintf(fo, "                default: barrier_state[%d] <= BARRIER_IDLE;\n", i);
        fprintf(fo, "            endcase\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "    end\n\n");
    }
    
    // Global barrier coordination logic
    fprintf(fo, "    // Global barrier coordination\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            global_barrier_participants <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            global_barrier_ready <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            global_barrier_state <= 1'b0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            if (global_barrier_request && !global_barrier_state) begin\n");
    fprintf(fo, "                // Start global barrier\n");
    fprintf(fo, "                global_barrier_participants <= ~master_barrier_override;\n");
    fprintf(fo, "                global_barrier_state <= 1'b1;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Track which masters are ready\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            if (global_barrier_participants[%d]) begin\n", i);
        fprintf(fo, "                global_barrier_ready[%d] <= (barrier_state[%d] == BARRIER_ACTIVE);\n", i, i);
        fprintf(fo, "            end\n");
    }
    fprintf(fo, "            \n");
    fprintf(fo, "            // Complete global barrier when all participants ready\n");
    fprintf(fo, "            if (global_barrier_state && all_masters_barrier_ready) begin\n");
    fprintf(fo, "                global_barrier_state <= 1'b0;\n");
    fprintf(fo, "                global_barrier_participants <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                global_barrier_ready <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Output assignments
    fprintf(fo, "    // Output signal assignments\n");
    fprintf(fo, "    assign barrier_timeout = barrier_timeout_flag;\n");
    fprintf(fo, "    assign global_barrier_active = global_barrier_state;\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Barrier status per master\n");
    fprintf(fo, "    always @(*) begin\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        barrier_active[%d] = (barrier_state[%d] == BARRIER_ACTIVE) || \n", i, i);
        fprintf(fo, "                            (barrier_state[%d] == BARRIER_DRAINING);\n", i);
        fprintf(fo, "        barrier_block[%d] = barrier_active[%d] && barrier_enable;\n", i, i);
        fprintf(fo, "        pending_transactions[%d] = outstanding_writes[%d] + outstanding_reads[%d];\n", i, i, i);
    }
    fprintf(fo, "    end\n\n");
    
    fprintf(fo, "endmodule\n");
    
    return 0;
}