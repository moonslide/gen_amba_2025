//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite System Coordinator Implementation
// Manages system-level coherency, global barriers, and cross-master coordination
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "../../gen_amba_axi.h"
#include "../../gen_axi_utils.h"

//--------------------------------------------------------
// Generate System Coordinator logic
// Implements global barrier coordination, system-level transaction ordering,
// and inter-master communication for ACE-Lite systems
//--------------------------------------------------------
int gen_ace_lite_system_coordinator(unsigned int numM, unsigned int numS, 
                                    unsigned int widthAD, unsigned int widthDA,
                                    char *prefix, axi_features_t *features, FILE *fo)
{
    int i, j;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite System Coordinator\n");
    fprintf(fo, "// Manages system-level coherency, global barriers, and cross-master coordination\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %sace_lite_system_coordinator\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , GLOBAL_BARRIER_TIMEOUT = 65536)  // Global barrier timeout cycles\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                    clk\n");
    fprintf(fo, "    , input  wire                    rst_n\n");
    
    // Add master interface connections for system coordination
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d system coordination interface\n", i);
        fprintf(fo, "    , input  wire                   m%d_barrier_req    // Barrier request\n", i);
        fprintf(fo, "    , input  wire [1:0]             m%d_barrier_type   // Barrier type (00=Normal, 01=Memory, 10=Reserved, 11=Sync)\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]    m%d_barrier_id     // Barrier transaction ID\n", i);
        fprintf(fo, "    , output reg                    m%d_barrier_ack    // Barrier acknowledge\n", i);
        fprintf(fo, "    , output reg                    m%d_barrier_stall  // Stall new transactions\n", i);
        fprintf(fo, "    \n");
        fprintf(fo, "    , input  wire                   m%d_txn_active     // Transaction active\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]    m%d_txn_id         // Active transaction ID\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]    m%d_txn_addr       // Transaction address\n", i);
        fprintf(fo, "    , input  wire [1:0]             m%d_coherency_req  // Coherency requirement\n", i);
        fprintf(fo, "    , output reg                    m%d_coherency_grant // Coherency grant\n", i);
        fprintf(fo, "    , output reg                    m%d_priority_boost  // Priority boost\n", i);
    }
    
    fprintf(fo, "    // Global system status outputs\n");
    fprintf(fo, "    , output reg                    global_barrier_active   // Global barrier in progress\n");
    fprintf(fo, "    , output reg  [31:0]            total_barriers          // Total barrier operations\n");
    fprintf(fo, "    , output reg  [31:0]            system_violations       // System-level violations\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0] master_stall_status     // Per-master stall status\n");
    fprintf(fo, "    , output reg  [31:0]            global_performance_counter // Global performance metric\n");
    fprintf(fo, ");\n\n");
    
    // System coordination state definitions
    fprintf(fo, "    // System Coordination State Definitions\n");
    fprintf(fo, "    localparam [2:0] SYS_IDLE              = 3'b000;  // System idle\n");
    fprintf(fo, "    localparam [2:0] SYS_BARRIER_COLLECT   = 3'b001;  // Collecting barrier requests\n");
    fprintf(fo, "    localparam [2:0] SYS_BARRIER_SYNC      = 3'b010;  // Synchronizing barriers\n");
    fprintf(fo, "    localparam [2:0] SYS_BARRIER_COMPLETE  = 3'b011;  // Completing barriers\n");
    fprintf(fo, "    localparam [2:0] SYS_COHERENCY_MANAGE  = 3'b100;  // Managing coherency\n");
    fprintf(fo, "    localparam [2:0] SYS_DEADLOCK_RESOLVE  = 3'b101;  // Resolving deadlocks\n");
    fprintf(fo, "    localparam [2:0] SYS_ERROR_RECOVERY    = 3'b110;  // Error recovery\n");
    fprintf(fo, "    localparam [2:0] SYS_PERFORMANCE_OPT   = 3'b111;  // Performance optimization\n\n");
    
    // Barrier types
    fprintf(fo, "    // Barrier Type Definitions\n");
    fprintf(fo, "    localparam [1:0] BARRIER_NORMAL        = 2'b00;   // Normal access\n");
    fprintf(fo, "    localparam [1:0] BARRIER_MEMORY        = 2'b01;   // Memory barrier\n");
    fprintf(fo, "    localparam [1:0] BARRIER_RESERVED      = 2'b10;   // Reserved\n");
    fprintf(fo, "    localparam [1:0] BARRIER_SYNC          = 2'b11;   // Synchronization barrier\n\n");
    
    // System coordination state registers
    fprintf(fo, "    // System Coordination State Registers\n");
    fprintf(fo, "    reg [2:0] system_state;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] barrier_requests_pending;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] barrier_acks_pending;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] transaction_outstanding;\n");
    fprintf(fo, "    reg [15:0] global_barrier_timeout_counter;\n");
    fprintf(fo, "    reg global_barrier_timeout_error;\n");
    fprintf(fo, "    \n");
    
    // Global barrier coordination tracking
    fprintf(fo, "    // Global Barrier Coordination Tracking\n");
    fprintf(fo, "    reg [1:0] active_barrier_type;\n");
    fprintf(fo, "    reg [WIDTH_ID-1:0] barrier_id_tracker [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] barrier_participants;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] barrier_completed;\n");
    fprintf(fo, "    \n");
    
    // Cross-master dependency tracking
    fprintf(fo, "    // Cross-Master Dependency Tracking\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] dependency_matrix [NUM_MASTER-1:0]; // Master dependencies\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] coherency_conflicts;\n");
    fprintf(fo, "    reg [15:0] dependency_age [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] deadlock_candidates;\n");
    fprintf(fo, "    \n");
    
    // Performance monitoring
    fprintf(fo, "    // Performance Monitoring and Statistics\n");
    fprintf(fo, "    reg [31:0] barrier_latency_accumulator;\n");
    fprintf(fo, "    reg [15:0] current_barrier_cycles;\n");
    fprintf(fo, "    reg [31:0] coherency_operations;\n");
    fprintf(fo, "    reg [31:0] deadlock_resolutions;\n");
    fprintf(fo, "    \n");
    
    // System coordination state machine
    fprintf(fo, "    // System Coordination State Machine\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            system_state <= SYS_IDLE;\n");
    fprintf(fo, "            barrier_requests_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            barrier_acks_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            transaction_outstanding <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            global_barrier_timeout_counter <= 16'h0000;\n");
    fprintf(fo, "            global_barrier_timeout_error <= 1'b0;\n");
    fprintf(fo, "            global_barrier_active <= 1'b0;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Initialize tracking structures\n");
    fprintf(fo, "            active_barrier_type <= BARRIER_NORMAL;\n");
    fprintf(fo, "            barrier_participants <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            barrier_completed <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            coherency_conflicts <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            deadlock_candidates <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Initialize statistics\n");
    fprintf(fo, "            total_barriers <= 32'h00000000;\n");
    fprintf(fo, "            system_violations <= 32'h00000000;\n");
    fprintf(fo, "            barrier_latency_accumulator <= 32'h00000000;\n");
    fprintf(fo, "            current_barrier_cycles <= 16'h0000;\n");
    fprintf(fo, "            coherency_operations <= 32'h00000000;\n");
    fprintf(fo, "            deadlock_resolutions <= 32'h00000000;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Initialize per-master states\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d initialization\n", i);
        fprintf(fo, "            m%d_barrier_ack <= 1'b0;\n", i);
        fprintf(fo, "            m%d_barrier_stall <= 1'b0;\n", i);
        fprintf(fo, "            m%d_coherency_grant <= 1'b1;\n", i);
        fprintf(fo, "            m%d_priority_boost <= 1'b0;\n", i);
        fprintf(fo, "            barrier_id_tracker[%d] <= {WIDTH_ID{1'b0}};\n", i);
        fprintf(fo, "            dependency_age[%d] <= 16'h0000;\n", i);
        fprintf(fo, "            \n");
        fprintf(fo, "            // Clear dependency matrix row %d\n", i);
        fprintf(fo, "            dependency_matrix[%d] <= {NUM_MASTER{1'b0}};\n", i);
    }
    
    fprintf(fo, "            master_stall_status <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            global_performance_counter <= 32'h00000000;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            case (system_state)\n");
    fprintf(fo, "                SYS_IDLE: begin\n");
    fprintf(fo, "                    global_barrier_active <= 1'b0;\n");
    fprintf(fo, "                    current_barrier_cycles <= 16'h0000;\n");
    fprintf(fo, "                    global_barrier_timeout_error <= 1'b0;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Check for barrier requests from any master\n");
    fprintf(fo, "                    barrier_requests_pending <= {NUM_MASTER{1'b0}};\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    if (m%d_barrier_req) begin\n", i);
        fprintf(fo, "                        barrier_requests_pending[%d] <= 1'b1;\n", i);
        fprintf(fo, "                        barrier_id_tracker[%d] <= m%d_barrier_id;\n", i, i);
        fprintf(fo, "                        active_barrier_type <= m%d_barrier_type;\n", i);
        fprintf(fo, "                    end\n");
    }
    
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Transition to barrier collection if any requests\n");
    fprintf(fo, "                    if (|barrier_requests_pending) begin\n");
    fprintf(fo, "                        system_state <= SYS_BARRIER_COLLECT;\n");
    fprintf(fo, "                        global_barrier_active <= 1'b1;\n");
    fprintf(fo, "                        total_barriers <= total_barriers + 1;\n");
    fprintf(fo, "                    end else if (|coherency_conflicts) begin\n");
    fprintf(fo, "                        system_state <= SYS_COHERENCY_MANAGE;\n");
    fprintf(fo, "                    end else if (|deadlock_candidates) begin\n");
    fprintf(fo, "                        system_state <= SYS_DEADLOCK_RESOLVE;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SYS_BARRIER_COLLECT: begin\n");
    fprintf(fo, "                    // Collect barrier requests and determine participants\n");
    fprintf(fo, "                    current_barrier_cycles <= current_barrier_cycles + 1;\n");
    fprintf(fo, "                    global_barrier_timeout_counter <= global_barrier_timeout_counter + 1;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Determine barrier participants based on barrier type\n");
    fprintf(fo, "                    case (active_barrier_type)\n");
    fprintf(fo, "                        BARRIER_MEMORY: begin\n");
    fprintf(fo, "                            // Memory barriers affect all masters with outstanding transactions\n");
    fprintf(fo, "                            barrier_participants <= transaction_outstanding;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                        \n");
    fprintf(fo, "                        BARRIER_SYNC: begin\n");
    fprintf(fo, "                            // Sync barriers affect all masters\n");
    fprintf(fo, "                            barrier_participants <= {NUM_MASTER{1'b1}};\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                        \n");
    fprintf(fo, "                        default: begin\n");
    fprintf(fo, "                            // Normal barriers only affect requesting masters\n");
    fprintf(fo, "                            barrier_participants <= barrier_requests_pending;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    endcase\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    system_state <= SYS_BARRIER_SYNC;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SYS_BARRIER_SYNC: begin\n");
    fprintf(fo, "                    // Synchronize barrier across all participants\n");
    fprintf(fo, "                    current_barrier_cycles <= current_barrier_cycles + 1;\n");
    fprintf(fo, "                    global_barrier_timeout_counter <= global_barrier_timeout_counter + 1;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Stall new transactions on participating masters\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    m%d_barrier_stall <= barrier_participants[%d];\n", i, i);
        fprintf(fo, "                    master_stall_status[%d] <= barrier_participants[%d];\n", i, i);
        fprintf(fo, "                    \n");
        fprintf(fo, "                    // Check if master %d has completed its part\n", i);
        fprintf(fo, "                    if (barrier_participants[%d] && !m%d_txn_active) begin\n", i, i);
        fprintf(fo, "                        barrier_completed[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end\n");
    }
    
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Check if all participants have completed\n");
    fprintf(fo, "                    if ((barrier_completed & barrier_participants) == barrier_participants) begin\n");
    fprintf(fo, "                        system_state <= SYS_BARRIER_COMPLETE;\n");
    fprintf(fo, "                    end else if (global_barrier_timeout_counter > GLOBAL_BARRIER_TIMEOUT) begin\n");
    fprintf(fo, "                        // Barrier timeout\n");
    fprintf(fo, "                        global_barrier_timeout_error <= 1'b1;\n");
    fprintf(fo, "                        system_violations <= system_violations + 1;\n");
    fprintf(fo, "                        system_state <= SYS_ERROR_RECOVERY;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SYS_BARRIER_COMPLETE: begin\n");
    fprintf(fo, "                    // Complete barrier operation\n");
    fprintf(fo, "                    current_barrier_cycles <= current_barrier_cycles + 1;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Send acknowledgments to requesting masters\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    if (barrier_requests_pending[%d]) begin\n", i);
        fprintf(fo, "                        m%d_barrier_ack <= 1'b1;\n", i);
        fprintf(fo, "                        m%d_barrier_stall <= 1'b0;\n", i);
        fprintf(fo, "                    end\n");
    }
    
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Update performance statistics\n");
    fprintf(fo, "                    barrier_latency_accumulator <= barrier_latency_accumulator + current_barrier_cycles;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Clear barrier state and return to idle\n");
    fprintf(fo, "                    barrier_requests_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    barrier_participants <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    barrier_completed <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    master_stall_status <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    global_barrier_timeout_counter <= 16'h0000;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    system_state <= SYS_IDLE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SYS_COHERENCY_MANAGE: begin\n");
    fprintf(fo, "                    // Manage coherency conflicts between masters\n");
    fprintf(fo, "                    coherency_operations <= coherency_operations + 1;\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    // Handle coherency for master %d\n", i);
        fprintf(fo, "                    if (coherency_conflicts[%d]) begin\n", i);
        fprintf(fo, "                        // Grant coherency based on priority or fairness\n");
        fprintf(fo, "                        if (dependency_age[%d] > 16'hF000) begin\n", i);
        fprintf(fo, "                            m%d_coherency_grant <= 1'b1;\n", i);
        fprintf(fo, "                            m%d_priority_boost <= 1'b1;\n", i);
        fprintf(fo, "                            coherency_conflicts[%d] <= 1'b0;\n", i);
        fprintf(fo, "                        end else begin\n");
        fprintf(fo, "                            m%d_coherency_grant <= 1'b0;\n", i);
        fprintf(fo, "                        end\n");
        fprintf(fo, "                    end else begin\n");
        fprintf(fo, "                        m%d_coherency_grant <= 1'b1;\n", i);
        fprintf(fo, "                        m%d_priority_boost <= 1'b0;\n", i);
        fprintf(fo, "                    end\n");
    }
    
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Return to idle when no conflicts remain\n");
    fprintf(fo, "                    if (!|coherency_conflicts) begin\n");
    fprintf(fo, "                        system_state <= SYS_IDLE;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SYS_DEADLOCK_RESOLVE: begin\n");
    fprintf(fo, "                    // Resolve potential deadlocks\n");
    fprintf(fo, "                    deadlock_resolutions <= deadlock_resolutions + 1;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Apply priority boosting to resolve deadlocks\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    if (deadlock_candidates[%d]) begin\n", i);
        fprintf(fo, "                        m%d_priority_boost <= 1'b1;\n", i);
        fprintf(fo, "                        m%d_coherency_grant <= 1'b1;\n", i);
        fprintf(fo, "                        deadlock_candidates[%d] <= 1'b0;\n", i);
        fprintf(fo, "                    end\n");
    }
    
    fprintf(fo, "                    \n");
    fprintf(fo, "                    system_state <= SYS_IDLE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SYS_ERROR_RECOVERY: begin\n");
    fprintf(fo, "                    // Recover from system-level errors\n");
    fprintf(fo, "                    system_violations <= system_violations + 1;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Clear all barrier states and stalls\n");
    fprintf(fo, "                    barrier_requests_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    barrier_participants <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    barrier_completed <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    master_stall_status <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    \n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    m%d_barrier_ack <= 1'b0;\n", i);
        fprintf(fo, "                    m%d_barrier_stall <= 1'b0;\n", i);
        fprintf(fo, "                    m%d_coherency_grant <= 1'b1;\n", i);
        fprintf(fo, "                    m%d_priority_boost <= 1'b0;\n", i);
    }
    
    fprintf(fo, "                    \n");
    fprintf(fo, "                    system_state <= SYS_IDLE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SYS_PERFORMANCE_OPT: begin\n");
    fprintf(fo, "                    // Performance optimization mode (placeholder)\n");
    fprintf(fo, "                    system_state <= SYS_IDLE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                default: begin\n");
    fprintf(fo, "                    system_state <= SYS_IDLE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            endcase\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Update dependency ages and detect deadlocks\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d dependency tracking\n", i);
        fprintf(fo, "            if (m%d_txn_active) begin\n", i);
        fprintf(fo, "                transaction_outstanding[%d] <= 1'b1;\n", i);
        fprintf(fo, "                if (dependency_age[%d] < 16'hFFFF) begin\n", i);
        fprintf(fo, "                    dependency_age[%d] <= dependency_age[%d] + 1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "                \n");
        fprintf(fo, "                // Detect potential deadlock\n");
        fprintf(fo, "                if (dependency_age[%d] > 16'hFF00) begin\n", i);
        fprintf(fo, "                    deadlock_candidates[%d] <= 1'b1;\n", i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            end else begin\n");
        fprintf(fo, "                transaction_outstanding[%d] <= 1'b0;\n", i);
        fprintf(fo, "                dependency_age[%d] <= 16'h0000;\n", i);
        fprintf(fo, "                deadlock_candidates[%d] <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Update coherency conflicts\n");
        fprintf(fo, "            if (m%d_coherency_req != 2'b00 && !m%d_coherency_grant) begin\n", i, i);
        fprintf(fo, "                coherency_conflicts[%d] <= 1'b1;\n", i);
        fprintf(fo, "            end else begin\n");
        fprintf(fo, "                coherency_conflicts[%d] <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Clear acknowledgments after one cycle\n");
        fprintf(fo, "            if (m%d_barrier_ack) begin\n", i);
        fprintf(fo, "                m%d_barrier_ack <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
    }
    
    fprintf(fo, "            // Update global performance counter\n");
    fprintf(fo, "            global_performance_counter <= global_performance_counter + 1;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // System health monitoring
    fprintf(fo, "    // System Health Monitoring\n");
    fprintf(fo, "    // Tracks system-wide metrics and health indicators\n");
    fprintf(fo, "    reg [31:0] system_efficiency_metric;\n");
    fprintf(fo, "    reg [15:0] average_barrier_latency;\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            system_efficiency_metric <= 32'h64646464; // Start at 100%% efficiency\n");
    fprintf(fo, "            average_barrier_latency <= 16'h0000;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            // Update efficiency based on stalls and violations\n");
    fprintf(fo, "            if (|master_stall_status) begin\n");
    fprintf(fo, "                if (system_efficiency_metric > 32'h00000000) begin\n");
    fprintf(fo, "                    system_efficiency_metric <= system_efficiency_metric - 1;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end else if (system_efficiency_metric < 32'h64646464) begin\n");
    fprintf(fo, "                system_efficiency_metric <= system_efficiency_metric + 1;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Calculate average barrier latency\n");
    fprintf(fo, "            if (total_barriers > 0) begin\n");
    fprintf(fo, "                average_barrier_latency <= barrier_latency_accumulator / total_barriers;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    fprintf(fo, "endmodule\n\n");
    
    return 0;
}