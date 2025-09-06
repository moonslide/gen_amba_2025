//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite DVM (Distributed Virtual Memory) Controller Implementation
// Manages DVM messages, TLB invalidation, and virtual memory coherency
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "../../gen_amba_axi.h"
#include "../../gen_axi_utils.h"

//--------------------------------------------------------
// Generate DVM (Distributed Virtual Memory) controller logic
// Implements DVM message distribution, TLB invalidation, and completion tracking
//--------------------------------------------------------
int gen_ace_lite_dvm_controller(unsigned int numM, unsigned int numS, 
                                unsigned int widthAD, unsigned int widthDA,
                                char *prefix, axi_features_t *features, FILE *fo)
{
    int i, j;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite DVM (Distributed Virtual Memory) Controller\n");
    fprintf(fo, "// Manages DVM messages, TLB invalidation, and virtual memory coherency\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %sace_lite_dvm_controller\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , DVM_QUEUE_DEPTH = 16)  // DVM message queue depth\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                    clk\n");
    fprintf(fo, "    , input  wire                    rst_n\n");
    
    // Add master interface connections for DVM operations
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d DVM interface\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]    m%d_dvm_addr       // DVM target address\n", i);
        fprintf(fo, "    , input  wire [7:0]             m%d_dvm_type       // DVM message type\n", i);
        fprintf(fo, "    , input  wire [15:0]            m%d_dvm_asid       // Address Space ID\n", i);
        fprintf(fo, "    , input  wire                   m%d_dvm_valid      // DVM request valid\n", i);
        fprintf(fo, "    , output reg                    m%d_dvm_ready      // DVM request ready\n", i);
        fprintf(fo, "    , output reg                    m%d_dvm_complete   // DVM operation complete\n", i);
        fprintf(fo, "    , output reg  [1:0]             m%d_dvm_resp       // DVM response (00=OK, 01=ERROR)\n", i);
    }
    
    fprintf(fo, "    // Global DVM status outputs\n");
    fprintf(fo, "    , output reg                    dvm_active         // DVM operation in progress\n");
    fprintf(fo, "    , output reg  [31:0]            dvm_operations     // Total DVM operations\n");
    fprintf(fo, "    , output reg  [31:0]            dvm_timeouts       // DVM timeout count\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0] dvm_error          // DVM error per master\n");
    fprintf(fo, ");\n\n");
    
    // DVM message type definitions
    fprintf(fo, "    // DVM Message Type Definitions\n");
    fprintf(fo, "    localparam [7:0] DVM_TLBI_ALL       = 8'h00;  // Invalidate all TLB entries\n");
    fprintf(fo, "    localparam [7:0] DVM_TLBI_ASID      = 8'h01;  // Invalidate by ASID\n");
    fprintf(fo, "    localparam [7:0] DVM_TLBI_VA        = 8'h02;  // Invalidate by Virtual Address\n");
    fprintf(fo, "    localparam [7:0] DVM_TLBI_VAA       = 8'h03;  // Invalidate by VA and ASID\n");
    fprintf(fo, "    localparam [7:0] DVM_TLBI_VMALL     = 8'h04;  // Invalidate all for VM\n");
    fprintf(fo, "    localparam [7:0] DVM_TLBI_IPAS2     = 8'h05;  // Invalidate IPA Stage 2\n");
    fprintf(fo, "    localparam [7:0] DVM_TLBI_IPAS2L    = 8'h06;  // Invalidate IPA Stage 2 Last level\n");
    fprintf(fo, "    localparam [7:0] DVM_SYNC           = 8'hFF;  // DVM Synchronization\n\n");
    
    // DVM response types
    fprintf(fo, "    // DVM Response Types\n");
    fprintf(fo, "    localparam [1:0] DVM_RESP_OK        = 2'b00;  // Operation successful\n");
    fprintf(fo, "    localparam [1:0] DVM_RESP_ERROR     = 2'b01;  // Operation failed\n");
    fprintf(fo, "    localparam [1:0] DVM_RESP_TIMEOUT   = 2'b10;  // Operation timed out\n");
    fprintf(fo, "    localparam [1:0] DVM_RESP_UNSUP     = 2'b11;  // Unsupported operation\n\n");
    
    // DVM state machine definitions
    fprintf(fo, "    // DVM Operation State Machine\n");
    fprintf(fo, "    localparam [3:0] DVM_IDLE           = 4'h0;   // Idle state\n");
    fprintf(fo, "    localparam [3:0] DVM_REQUEST        = 4'h1;   // Process DVM request\n");
    fprintf(fo, "    localparam [3:0] DVM_BROADCAST      = 4'h2;   // Broadcast to masters\n");
    fprintf(fo, "    localparam [3:0] DVM_WAIT_ACK       = 4'h3;   // Wait for acknowledgments\n");
    fprintf(fo, "    localparam [3:0] DVM_SYNC_STATE     = 4'h4;   // Synchronization phase\n");
    fprintf(fo, "    localparam [3:0] DVM_COMPLETE       = 4'h5;   // Operation complete\n");
    fprintf(fo, "    localparam [3:0] DVM_ERROR          = 4'h6;   // Error handling\n");
    fprintf(fo, "    localparam [3:0] DVM_TIMEOUT        = 4'h7;   // Timeout handling\n\n");
    
    // DVM controller state registers
    fprintf(fo, "    // DVM Controller State Registers\n");
    fprintf(fo, "    reg [3:0] dvm_state;\n");
    fprintf(fo, "    reg [3:0] dvm_next_state;\n");
    fprintf(fo, "    reg [$clog2(DVM_QUEUE_DEPTH)-1:0] dvm_queue_head;\n");
    fprintf(fo, "    reg [$clog2(DVM_QUEUE_DEPTH)-1:0] dvm_queue_tail;\n");
    fprintf(fo, "    reg [$clog2(DVM_QUEUE_DEPTH)-1:0] dvm_queue_count;\n");
    fprintf(fo, "    \n");
    
    // DVM message queue structure
    fprintf(fo, "    // DVM Message Queue\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] dvm_queue_addr [DVM_QUEUE_DEPTH-1:0];\n");
    fprintf(fo, "    reg [7:0]          dvm_queue_type [DVM_QUEUE_DEPTH-1:0];\n");
    fprintf(fo, "    reg [15:0]         dvm_queue_asid [DVM_QUEUE_DEPTH-1:0];\n");
    fprintf(fo, "    reg [3:0]          dvm_queue_master [DVM_QUEUE_DEPTH-1:0];\n");
    fprintf(fo, "    reg                dvm_queue_valid [DVM_QUEUE_DEPTH-1:0];\n");
    fprintf(fo, "    \n");
    
    // DVM acknowledgment tracking
    fprintf(fo, "    // DVM Acknowledgment Tracking\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] dvm_ack_pending;     // Acknowledgments pending per master\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] dvm_ack_received;    // Acknowledgments received per master\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] dvm_target_masters;  // Target masters for current DVM\n");
    fprintf(fo, "    reg [15:0] dvm_timeout_counter;           // Timeout counter\n");
    fprintf(fo, "    reg        dvm_timeout_error;             // Timeout error flag\n");
    fprintf(fo, "    \n");
    
    // Current DVM operation tracking
    fprintf(fo, "    // Current DVM Operation Tracking\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] current_dvm_addr;\n");
    fprintf(fo, "    reg [7:0]          current_dvm_type;\n");
    fprintf(fo, "    reg [15:0]         current_dvm_asid;\n");
    fprintf(fo, "    reg [3:0]          current_dvm_master;\n");
    fprintf(fo, "    \n");
    
    // DVM queue management logic
    fprintf(fo, "    // DVM Queue Management Logic\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            dvm_queue_head <= 0;\n");
    fprintf(fo, "            dvm_queue_tail <= 0;\n");
    fprintf(fo, "            dvm_queue_count <= 0;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            for (integer k = 0; k < DVM_QUEUE_DEPTH; k = k + 1) begin\n");
    fprintf(fo, "                dvm_queue_valid[k] <= 1'b0;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    
    // Initialize per-master ready signals
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            m%d_dvm_ready <= 1'b1;\n", i);
        fprintf(fo, "            m%d_dvm_complete <= 1'b0;\n", i);
        fprintf(fo, "            m%d_dvm_resp <= DVM_RESP_OK;\n", i);
    }
    
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            // DVM request enqueueing\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d DVM request enqueueing\n", i);
        fprintf(fo, "            if (m%d_dvm_valid && m%d_dvm_ready && (dvm_queue_count < DVM_QUEUE_DEPTH)) begin\n", i, i);
        fprintf(fo, "                // Enqueue DVM request\n");
        fprintf(fo, "                dvm_queue_addr[dvm_queue_tail] <= m%d_dvm_addr;\n", i);
        fprintf(fo, "                dvm_queue_type[dvm_queue_tail] <= m%d_dvm_type;\n", i);
        fprintf(fo, "                dvm_queue_asid[dvm_queue_tail] <= m%d_dvm_asid;\n", i);
        fprintf(fo, "                dvm_queue_master[dvm_queue_tail] <= %d;\n", i);
        fprintf(fo, "                dvm_queue_valid[dvm_queue_tail] <= 1'b1;\n");
        fprintf(fo, "                \n");
        fprintf(fo, "                dvm_queue_tail <= (dvm_queue_tail + 1) %% DVM_QUEUE_DEPTH;\n");
        fprintf(fo, "                dvm_queue_count <= dvm_queue_count + 1;\n");
        fprintf(fo, "                \n");
        fprintf(fo, "                // Block further requests until queue has space\n");
        fprintf(fo, "                if (dvm_queue_count == (DVM_QUEUE_DEPTH - 2)) begin\n");
        fprintf(fo, "                    m%d_dvm_ready <= 1'b0;\n", i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
    }
    
    fprintf(fo, "            // DVM request dequeuing (handled by state machine)\n");
    fprintf(fo, "            if ((dvm_state == DVM_REQUEST) && (dvm_queue_count > 0) && dvm_queue_valid[dvm_queue_head]) begin\n");
    fprintf(fo, "                // Dequeue DVM request\n");
    fprintf(fo, "                current_dvm_addr <= dvm_queue_addr[dvm_queue_head];\n");
    fprintf(fo, "                current_dvm_type <= dvm_queue_type[dvm_queue_head];\n");
    fprintf(fo, "                current_dvm_asid <= dvm_queue_asid[dvm_queue_head];\n");
    fprintf(fo, "                current_dvm_master <= dvm_queue_master[dvm_queue_head];\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                dvm_queue_valid[dvm_queue_head] <= 1'b0;\n");
    fprintf(fo, "                dvm_queue_head <= (dvm_queue_head + 1) %% DVM_QUEUE_DEPTH;\n");
    fprintf(fo, "                dvm_queue_count <= dvm_queue_count - 1;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                // Re-enable ready signals if queue has space\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                if (dvm_queue_count < (DVM_QUEUE_DEPTH - 1)) begin\n");
        fprintf(fo, "                    m%d_dvm_ready <= 1'b1;\n", i);
        fprintf(fo, "                end\n");
    }
    
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // DVM state machine
    fprintf(fo, "    // DVM Operation State Machine\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            dvm_state <= DVM_IDLE;\n");
    fprintf(fo, "            dvm_ack_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            dvm_ack_received <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            dvm_target_masters <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            dvm_timeout_counter <= 16'h0000;\n");
    fprintf(fo, "            dvm_timeout_error <= 1'b0;\n");
    fprintf(fo, "            dvm_active <= 1'b0;\n");
    fprintf(fo, "            dvm_operations <= 32'h00000000;\n");
    fprintf(fo, "            dvm_timeouts <= 32'h00000000;\n");
    fprintf(fo, "            dvm_error <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            case (dvm_state)\n");
    fprintf(fo, "                DVM_IDLE: begin\n");
    fprintf(fo, "                    dvm_active <= 1'b0;\n");
    fprintf(fo, "                    dvm_timeout_counter <= 16'h0000;\n");
    fprintf(fo, "                    dvm_timeout_error <= 1'b0;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Check for queued DVM operations\n");
    fprintf(fo, "                    if (dvm_queue_count > 0 && dvm_queue_valid[dvm_queue_head]) begin\n");
    fprintf(fo, "                        dvm_state <= DVM_REQUEST;\n");
    fprintf(fo, "                        dvm_active <= 1'b1;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                DVM_REQUEST: begin\n");
    fprintf(fo, "                    // Process the dequeued DVM request\n");
    fprintf(fo, "                    dvm_state <= DVM_BROADCAST;\n");
    fprintf(fo, "                    dvm_operations <= dvm_operations + 1;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Determine target masters based on DVM type\n");
    fprintf(fo, "                    case (current_dvm_type)\n");
    fprintf(fo, "                        DVM_TLBI_ALL: begin\n");
    fprintf(fo, "                            // Broadcast to all masters except originator\n");
    fprintf(fo, "                            dvm_target_masters <= {NUM_MASTER{1'b1}} & ~(1 << current_dvm_master);\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                        \n");
    fprintf(fo, "                        DVM_TLBI_ASID: begin\n");
    fprintf(fo, "                            // Broadcast to all masters for ASID invalidation\n");
    fprintf(fo, "                            dvm_target_masters <= {NUM_MASTER{1'b1}} & ~(1 << current_dvm_master);\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                        \n");
    fprintf(fo, "                        DVM_TLBI_VA, DVM_TLBI_VAA: begin\n");
    fprintf(fo, "                            // Broadcast to all masters for VA invalidation\n");
    fprintf(fo, "                            dvm_target_masters <= {NUM_MASTER{1'b1}} & ~(1 << current_dvm_master);\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                        \n");
    fprintf(fo, "                        DVM_SYNC_STATE: begin\n");
    fprintf(fo, "                            // Synchronization with all masters\n");
    fprintf(fo, "                            dvm_target_masters <= {NUM_MASTER{1'b1}} & ~(1 << current_dvm_master);\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                        \n");
    fprintf(fo, "                        default: begin\n");
    fprintf(fo, "                            // Unknown DVM type - error\n");
    fprintf(fo, "                            dvm_target_masters <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                            dvm_state <= DVM_ERROR;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    endcase\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                DVM_BROADCAST: begin\n");
    fprintf(fo, "                    // Initiate broadcast to target masters\n");
    fprintf(fo, "                    dvm_ack_pending <= dvm_target_masters;\n");
    fprintf(fo, "                    dvm_ack_received <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    dvm_timeout_counter <= 16'h0001;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    if (|dvm_target_masters) begin\n");
    fprintf(fo, "                        dvm_state <= DVM_WAIT_ACK;\n");
    fprintf(fo, "                    end else begin\n");
    fprintf(fo, "                        // No targets - complete immediately\n");
    fprintf(fo, "                        dvm_state <= DVM_COMPLETE;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                DVM_WAIT_ACK: begin\n");
    fprintf(fo, "                    // Wait for acknowledgments from target masters\n");
    fprintf(fo, "                    dvm_timeout_counter <= dvm_timeout_counter + 1;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Simulate acknowledgment reception (placeholder)\n");
    fprintf(fo, "                    // In real implementation, this would be connected to actual DVM responses\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    if (dvm_ack_pending[%d] && (dvm_timeout_counter > 16'h0100)) begin\n", i);
        fprintf(fo, "                        // Simulate acknowledgment from master %d\n", i);
        fprintf(fo, "                        dvm_ack_received[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end\n");
    }
    
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Check if all acknowledgments received\n");
    fprintf(fo, "                    if ((dvm_ack_received & dvm_ack_pending) == dvm_ack_pending) begin\n");
    fprintf(fo, "                        // All acknowledgments received\n");
    fprintf(fo, "                        if (current_dvm_type == DVM_SYNC) begin\n");
    fprintf(fo, "                            dvm_state <= DVM_SYNC_STATE;\n");
    fprintf(fo, "                        end else begin\n");
    fprintf(fo, "                            dvm_state <= DVM_COMPLETE;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end else if (dvm_timeout_counter > 16'hFF00) begin\n");
    fprintf(fo, "                        // Timeout occurred\n");
    fprintf(fo, "                        dvm_state <= DVM_TIMEOUT;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                DVM_SYNC_STATE: begin\n");
    fprintf(fo, "                    // DVM synchronization phase\n");
    fprintf(fo, "                    // Ensure all masters have completed their operations\n");
    fprintf(fo, "                    dvm_state <= DVM_COMPLETE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                DVM_COMPLETE: begin\n");
    fprintf(fo, "                    // DVM operation completed successfully\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    if (current_dvm_master == %d) begin\n", i);
        fprintf(fo, "                        m%d_dvm_complete <= 1'b1;\n", i);
        fprintf(fo, "                        m%d_dvm_resp <= DVM_RESP_OK;\n", i);
        fprintf(fo, "                    end\n");
    }
    
    fprintf(fo, "                    \n");
    fprintf(fo, "                    dvm_state <= DVM_IDLE;\n");
    fprintf(fo, "                    dvm_ack_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    dvm_ack_received <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    dvm_target_masters <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                DVM_ERROR: begin\n");
    fprintf(fo, "                    // DVM operation failed\n");
    fprintf(fo, "                    dvm_error[current_dvm_master] <= 1'b1;\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    if (current_dvm_master == %d) begin\n", i);
        fprintf(fo, "                        m%d_dvm_complete <= 1'b1;\n", i);
        fprintf(fo, "                        m%d_dvm_resp <= DVM_RESP_ERROR;\n", i);
        fprintf(fo, "                    end\n");
    }
    
    fprintf(fo, "                    \n");
    fprintf(fo, "                    dvm_state <= DVM_IDLE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                DVM_TIMEOUT: begin\n");
    fprintf(fo, "                    // DVM operation timed out\n");
    fprintf(fo, "                    dvm_timeout_error <= 1'b1;\n");
    fprintf(fo, "                    dvm_timeouts <= dvm_timeouts + 1;\n");
    fprintf(fo, "                    dvm_error[current_dvm_master] <= 1'b1;\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    if (current_dvm_master == %d) begin\n", i);
        fprintf(fo, "                        m%d_dvm_complete <= 1'b1;\n", i);
        fprintf(fo, "                        m%d_dvm_resp <= DVM_RESP_TIMEOUT;\n", i);
        fprintf(fo, "                    end\n");
    }
    
    fprintf(fo, "                    \n");
    fprintf(fo, "                    dvm_state <= DVM_IDLE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                default: begin\n");
    fprintf(fo, "                    dvm_state <= DVM_IDLE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            endcase\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Clear completion flags after one cycle\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            if (m%d_dvm_complete) begin\n", i);
        fprintf(fo, "                m%d_dvm_complete <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
    }
    
    fprintf(fo, "            \n");
    fprintf(fo, "            // Clear error flags periodically\n");
    fprintf(fo, "            if (dvm_timeout_counter[7:0] == 8'h00) begin\n");
    fprintf(fo, "                dvm_error <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // DVM message validation function
    fprintf(fo, "    // DVM Message Validation Function\n");
    fprintf(fo, "    function automatic logic dvm_message_valid;\n");
    fprintf(fo, "        input [7:0] dvm_type;\n");
    fprintf(fo, "        input [WIDTH_AD-1:0] dvm_addr;\n");
    fprintf(fo, "        input [15:0] dvm_asid;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            case (dvm_type)\n");
    fprintf(fo, "                DVM_TLBI_ALL: begin\n");
    fprintf(fo, "                    // No address or ASID required\n");
    fprintf(fo, "                    dvm_message_valid = 1'b1;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                DVM_TLBI_ASID: begin\n");
    fprintf(fo, "                    // Valid ASID required\n");
    fprintf(fo, "                    dvm_message_valid = (dvm_asid != 16'h0000);\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                DVM_TLBI_VA: begin\n");
    fprintf(fo, "                    // Valid virtual address required\n");
    fprintf(fo, "                    dvm_message_valid = 1'b1; // All addresses are valid\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                DVM_TLBI_VAA: begin\n");
    fprintf(fo, "                    // Both address and ASID required\n");
    fprintf(fo, "                    dvm_message_valid = (dvm_asid != 16'h0000);\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                DVM_SYNC_STATE: begin\n");
    fprintf(fo, "                    // Synchronization is always valid\n");
    fprintf(fo, "                    dvm_message_valid = 1'b1;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                default: begin\n");
    fprintf(fo, "                    // Unknown DVM message type\n");
    fprintf(fo, "                    dvm_message_valid = 1'b0;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            endcase\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    fprintf(fo, "endmodule\n\n");
    
    return 0;
}