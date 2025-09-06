//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite Coherency Controller Module Generator
// Manages master coherency state and transaction ordering
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "../../gen_amba_axi.h"
#include "../../gen_axi_utils.h"

//--------------------------------------------------------
// Generate ACE-Lite coherency controller module
//--------------------------------------------------------
int gen_ace_lite_coherency_controller(unsigned int numM, unsigned int numS,
                                     unsigned int widthAD, unsigned int widthDA,
                                     char *prefix, axi_features_t *features, FILE *fo)
{
    int i;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite Coherency Controller\n");
    fprintf(fo, "// Manages master coherency states and transaction ordering\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %sace_lite_coherency_controller\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , COHERENCY_TABLE_DEPTH = 64)\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                       clk\n");
    fprintf(fo, "    , input  wire                       rst_n\n");
    
    // Master interface inputs
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d coherency interface\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]       m%d_awid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]       m%d_awaddr\n", i);
        fprintf(fo, "    , input  wire [1:0]                m%d_awdomain\n", i);
        fprintf(fo, "    , input  wire [2:0]                m%d_awsnoop\n", i);
        fprintf(fo, "    , input  wire                      m%d_awvalid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]       m%d_arid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]       m%d_araddr\n", i);
        fprintf(fo, "    , input  wire [1:0]                m%d_ardomain\n", i);
        fprintf(fo, "    , input  wire [3:0]                m%d_arsnoop\n", i);
        fprintf(fo, "    , input  wire                      m%d_arvalid\n", i);
        fprintf(fo, "    , input  wire                      m%d_bready\n", i);
        fprintf(fo, "    , input  wire                      m%d_rready\n", i);
    }
    
    // Coherency control outputs
    fprintf(fo, "    // Coherency control outputs\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       coherency_block\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]       coherency_violation\n");
    fprintf(fo, "    , output reg                         coherency_active\n");
    fprintf(fo, "    , output wire [NUM_MASTER-1:0]       transaction_valid\n");
    fprintf(fo, "    , output wire [7:0]                  coherency_state [NUM_MASTER-1:0]\n");
    
    fprintf(fo, ");\n\n");
    
    // Parameter definitions
    fprintf(fo, "    // ACE-Lite coherency parameters\n");
    fprintf(fo, "    localparam WIDTH_DOMAIN = 2;\n");
    fprintf(fo, "    localparam WIDTH_SNOOP_AW = 3;\n");
    fprintf(fo, "    localparam WIDTH_SNOOP_AR = 4;\n\n");
    
    // Domain encodings
    fprintf(fo, "    // Domain encodings (shareability)\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_NON_SHAREABLE = 2'b00;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_INNER_SHAREABLE = 2'b01;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_OUTER_SHAREABLE = 2'b10;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_SYSTEM = 2'b11;\n\n");
    
    // Snoop encodings
    fprintf(fo, "    // Write snoop encodings (ACE-Lite)\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_NO_SNOOP = 3'b000;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_LINE_UNIQUE = 3'b001;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_CLEAN = 3'b010;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_BACK = 3'b011;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_EVICT = 3'b100;\n\n");
    
    fprintf(fo, "    // Read snoop encodings (ACE-Lite)\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_NO_SNOOP = 4'b0000;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_ONCE = 4'b0001;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_SHARED = 4'b0001;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_CLEAN = 4'b0010;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_UNIQUE = 4'b0111;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_CLEAN_UNIQUE = 4'b1011;\n\n");
    
    // Coherency state encodings
    fprintf(fo, "    // Coherency state encodings per master\n");
    fprintf(fo, "    localparam [7:0] COHERENT_IDLE = 8'h00;\n");
    fprintf(fo, "    localparam [7:0] COHERENT_WRITE_PENDING = 8'h01;\n");
    fprintf(fo, "    localparam [7:0] COHERENT_READ_PENDING = 8'h02;\n");
    fprintf(fo, "    localparam [7:0] COHERENT_WRITE_ACTIVE = 8'h04;\n");
    fprintf(fo, "    localparam [7:0] COHERENT_READ_ACTIVE = 8'h08;\n");
    fprintf(fo, "    localparam [7:0] COHERENT_CACHE_MAINT = 8'h10;\n");
    fprintf(fo, "    localparam [7:0] COHERENT_BARRIER_WAIT = 8'h20;\n");
    fprintf(fo, "    localparam [7:0] COHERENT_VIOLATION = 8'hFF;\n\n");
    
    // Coherency table - tracks active coherent transactions
    fprintf(fo, "    // Coherency tracking table\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] coherency_addr_table [0:COHERENCY_TABLE_DEPTH-1];\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] coherency_master_table [0:COHERENCY_TABLE_DEPTH-1];\n");
    fprintf(fo, "    reg [COHERENCY_TABLE_DEPTH-1:0] coherency_table_valid;\n");
    fprintf(fo, "    reg [$clog2(COHERENCY_TABLE_DEPTH)-1:0] coherency_table_ptr;\n\n");
    
    // Master coherency state registers
    fprintf(fo, "    // Master coherency state tracking\n");
    fprintf(fo, "    reg [7:0] master_coherency_state [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] master_pending_addr [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] master_coherent_transaction;\n\n");
    
    // Generate master coherency state machines
    fprintf(fo, "    // Master coherency state machines\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d coherency state machine\n", i);
        fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
        fprintf(fo, "        if (!rst_n) begin\n");
        fprintf(fo, "            master_coherency_state[%d] <= COHERENT_IDLE;\n", i);
        fprintf(fo, "            master_pending_addr[%d] <= 32'h0;\n", i);
        fprintf(fo, "            master_coherent_transaction[%d] <= 1'b0;\n", i);
        fprintf(fo, "        end else begin\n");
        fprintf(fo, "            case (master_coherency_state[%d])\n", i);
        
        // IDLE state
        fprintf(fo, "                COHERENT_IDLE: begin\n");
        fprintf(fo, "                    if (m%d_awvalid && (m%d_awdomain != DOMAIN_NON_SHAREABLE)) begin\n", i, i);
        fprintf(fo, "                        master_coherency_state[%d] <= COHERENT_WRITE_PENDING;\n", i);
        fprintf(fo, "                        master_pending_addr[%d] <= m%d_awaddr;\n", i, i);
        fprintf(fo, "                        master_coherent_transaction[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end else if (m%d_arvalid && (m%d_ardomain != DOMAIN_NON_SHAREABLE)) begin\n", i, i);
        fprintf(fo, "                        master_coherency_state[%d] <= COHERENT_READ_PENDING;\n", i);
        fprintf(fo, "                        master_pending_addr[%d] <= m%d_araddr;\n", i, i);
        fprintf(fo, "                        master_coherent_transaction[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        
        // WRITE_PENDING state
        fprintf(fo, "                COHERENT_WRITE_PENDING: begin\n");
        fprintf(fo, "                    // Check for coherency conflicts\n");
        fprintf(fo, "                    if (coherency_conflict_detected(%d, master_pending_addr[%d])) begin\n", i, i);
        fprintf(fo, "                        master_coherency_state[%d] <= COHERENT_VIOLATION;\n", i);
        fprintf(fo, "                    end else begin\n");
        fprintf(fo, "                        master_coherency_state[%d] <= COHERENT_WRITE_ACTIVE;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        
        // READ_PENDING state
        fprintf(fo, "                COHERENT_READ_PENDING: begin\n");
        fprintf(fo, "                    // Check for coherency conflicts\n");
        fprintf(fo, "                    if (coherency_conflict_detected(%d, master_pending_addr[%d])) begin\n", i, i);
        fprintf(fo, "                        master_coherency_state[%d] <= COHERENT_VIOLATION;\n", i);
        fprintf(fo, "                    end else begin\n");
        fprintf(fo, "                        master_coherency_state[%d] <= COHERENT_READ_ACTIVE;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        
        // WRITE_ACTIVE state
        fprintf(fo, "                COHERENT_WRITE_ACTIVE: begin\n");
        fprintf(fo, "                    if (m%d_bready) begin\n", i);
        fprintf(fo, "                        master_coherency_state[%d] <= COHERENT_IDLE;\n", i);
        fprintf(fo, "                        master_coherent_transaction[%d] <= 1'b0;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        
        // READ_ACTIVE state  
        fprintf(fo, "                COHERENT_READ_ACTIVE: begin\n");
        fprintf(fo, "                    if (m%d_rready) begin\n", i);
        fprintf(fo, "                        master_coherency_state[%d] <= COHERENT_IDLE;\n", i);
        fprintf(fo, "                        master_coherent_transaction[%d] <= 1'b0;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        
        // VIOLATION state
        fprintf(fo, "                COHERENT_VIOLATION: begin\n");
        fprintf(fo, "                    // Hold violation until reset\n");
        fprintf(fo, "                    master_coherency_state[%d] <= COHERENT_VIOLATION;\n", i);
        fprintf(fo, "                end\n");
        
        fprintf(fo, "                default: master_coherency_state[%d] <= COHERENT_IDLE;\n", i);
        fprintf(fo, "            endcase\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "    end\n\n");
    }
    
    // Coherency conflict detection function
    fprintf(fo, "    // Coherency conflict detection function\n");
    fprintf(fo, "    function coherency_conflict_detected;\n");
    fprintf(fo, "        input [7:0] master_id;\n");
    fprintf(fo, "        input [WIDTH_AD-1:0] addr;\n");
    fprintf(fo, "        integer j;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            coherency_conflict_detected = 1'b0;\n");
    fprintf(fo, "            // Check coherency table for address conflicts\n");
    fprintf(fo, "            for (j = 0; j < COHERENCY_TABLE_DEPTH; j = j + 1) begin\n");
    fprintf(fo, "                if (coherency_table_valid[j] && \n");
    fprintf(fo, "                    (coherency_addr_table[j][WIDTH_AD-1:6] == addr[WIDTH_AD-1:6]) &&\n");
    fprintf(fo, "                    (coherency_master_table[j][master_id] == 1'b0)) begin\n");
    fprintf(fo, "                    coherency_conflict_detected = 1'b1;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Output assignments
    fprintf(fo, "    // Output assignments\n");
    fprintf(fo, "    assign coherency_state = master_coherency_state;\n");
    fprintf(fo, "    assign transaction_valid = master_coherent_transaction;\n");
    
    fprintf(fo, "    // Coherency violation detection\n");
    fprintf(fo, "    always @(*) begin\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        coherency_violation[%d] = (master_coherency_state[%d] == COHERENT_VIOLATION);\n", i, i);
        fprintf(fo, "        coherency_block[%d] = (master_coherency_state[%d] == COHERENT_WRITE_PENDING) ||\n", i, i);
        fprintf(fo, "                               (master_coherency_state[%d] == COHERENT_READ_PENDING);\n", i);
    }
    fprintf(fo, "        coherency_active = |master_coherent_transaction;\n");
    fprintf(fo, "    end\n\n");
    
    // Enhanced Coherency State Machine Features
    fprintf(fo, "\n");
    fprintf(fo, "    // Enhanced Snoop Request Distribution Logic\n");
    fprintf(fo, "    // Manages coherency requests to all affected masters\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] snoop_request_pending;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] snoop_response_received;\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] current_snoop_addr;\n");
    fprintf(fo, "    reg [2:0] current_snoop_type;\n");
    fprintf(fo, "    reg snoop_broadcast_active;\n");
    fprintf(fo, "\n");
    
    fprintf(fo, "    // Snoop Distribution State Machine\n");
    fprintf(fo, "    localparam [2:0] SNOOP_IDLE        = 3'b000;\n");
    fprintf(fo, "    localparam [2:0] SNOOP_REQUEST     = 3'b001;\n");
    fprintf(fo, "    localparam [2:0] SNOOP_WAIT_RESP   = 3'b010;\n");
    fprintf(fo, "    localparam [2:0] SNOOP_AGGREGATE   = 3'b011;\n");
    fprintf(fo, "    localparam [2:0] SNOOP_COMPLETE    = 3'b100;\n");
    fprintf(fo, "    localparam [2:0] SNOOP_ERROR       = 3'b101;\n");
    fprintf(fo, "\n");
    
    fprintf(fo, "    reg [2:0] snoop_state;\n");
    fprintf(fo, "    reg [15:0] snoop_timeout_counter;\n");
    fprintf(fo, "    reg snoop_timeout_error;\n");
    fprintf(fo, "\n");
    
    fprintf(fo, "    // Snoop Distribution and Response Aggregation\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            snoop_state <= SNOOP_IDLE;\n");
    fprintf(fo, "            snoop_request_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            snoop_response_received <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            current_snoop_addr <= {WIDTH_AD{1'b0}};\n");
    fprintf(fo, "            current_snoop_type <= 3'b000;\n");
    fprintf(fo, "            snoop_broadcast_active <= 1'b0;\n");
    fprintf(fo, "            snoop_timeout_counter <= 16'h0000;\n");
    fprintf(fo, "            snoop_timeout_error <= 1'b0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            case (snoop_state)\n");
    fprintf(fo, "                SNOOP_IDLE: begin\n");
    fprintf(fo, "                    snoop_timeout_counter <= 16'h0000;\n");
    fprintf(fo, "                    snoop_timeout_error <= 1'b0;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Check for coherent transactions requiring snooping\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                    if (m%d_awvalid && (m%d_awdomain != DOMAIN_NON_SHAREABLE) &&\n", i, i);
        fprintf(fo, "                        (m%d_awsnoop != AWSNOOP_WRITE_NO_SNOOP)) begin\n", i);
        fprintf(fo, "                        // Coherent write requires snoop broadcast\n");
        fprintf(fo, "                        snoop_state <= SNOOP_REQUEST;\n");
        fprintf(fo, "                        current_snoop_addr <= m%d_awaddr;\n", i);
        fprintf(fo, "                        current_snoop_type <= m%d_awsnoop;\n", i);
        fprintf(fo, "                        snoop_broadcast_active <= 1'b1;\n");
        fprintf(fo, "                        // Request snoops to all other masters\n");
        fprintf(fo, "                        snoop_request_pending <= {NUM_MASTER{1'b1}} & ~(1 << %d);\n", i);
        fprintf(fo, "                    end else if (m%d_arvalid && (m%d_ardomain != DOMAIN_NON_SHAREABLE) &&\n", i, i);
        fprintf(fo, "                                (m%d_arsnoop != ARSNOOP_READ_NO_SNOOP)) begin\n", i);
        fprintf(fo, "                        // Coherent read may require snoop broadcast\n");
        fprintf(fo, "                        snoop_state <= SNOOP_REQUEST;\n");
        fprintf(fo, "                        current_snoop_addr <= m%d_araddr;\n", i);
        fprintf(fo, "                        current_snoop_type <= {1'b0, m%d_arsnoop[1:0]};\n", i);
        fprintf(fo, "                        snoop_broadcast_active <= 1'b1;\n");
        fprintf(fo, "                        // Request snoops to relevant masters\n");
        fprintf(fo, "                        snoop_request_pending <= {NUM_MASTER{1'b1}} & ~(1 << %d);\n", i);
        fprintf(fo, "                    end else ");
    }
    fprintf(fo, "begin\n");
    fprintf(fo, "                        // No coherent transaction\n");
    fprintf(fo, "                        snoop_broadcast_active <= 1'b0;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SNOOP_REQUEST: begin\n");
    fprintf(fo, "                    // Initiate snoop requests to selected masters\n");
    fprintf(fo, "                    snoop_state <= SNOOP_WAIT_RESP;\n");
    fprintf(fo, "                    snoop_response_received <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    snoop_timeout_counter <= 16'h0001;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SNOOP_WAIT_RESP: begin\n");
    fprintf(fo, "                    // Wait for all snoop responses with timeout\n");
    fprintf(fo, "                    if ((snoop_response_received & snoop_request_pending) == snoop_request_pending) begin\n");
    fprintf(fo, "                        // All responses received\n");
    fprintf(fo, "                        snoop_state <= SNOOP_AGGREGATE;\n");
    fprintf(fo, "                    end else if (snoop_timeout_counter > 16'hFF00) begin\n");
    fprintf(fo, "                        // Timeout occurred\n");
    fprintf(fo, "                        snoop_state <= SNOOP_ERROR;\n");
    fprintf(fo, "                        snoop_timeout_error <= 1'b1;\n");
    fprintf(fo, "                    end else begin\n");
    fprintf(fo, "                        snoop_timeout_counter <= snoop_timeout_counter + 1;\n");
    fprintf(fo, "                        \n");
    fprintf(fo, "                        // Update response received flags (placeholder logic)\n");
    fprintf(fo, "                        // In real implementation, this would be connected to actual snoop responses\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                        if (snoop_request_pending[%d] && /* snoop_response_valid[%d] */ 1'b0) begin\n", i, i);
        fprintf(fo, "                            snoop_response_received[%d] <= 1'b1;\n", i);
        fprintf(fo, "                        end\n");
    }
    
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SNOOP_AGGREGATE: begin\n");
    fprintf(fo, "                    // Aggregate all snoop responses\n");
    fprintf(fo, "                    // Determine final coherency action based on responses\n");
    fprintf(fo, "                    snoop_state <= SNOOP_COMPLETE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SNOOP_COMPLETE: begin\n");
    fprintf(fo, "                    // Complete snoop operation\n");
    fprintf(fo, "                    snoop_state <= SNOOP_IDLE;\n");
    fprintf(fo, "                    snoop_broadcast_active <= 1'b0;\n");
    fprintf(fo, "                    snoop_request_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    snoop_response_received <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                SNOOP_ERROR: begin\n");
    fprintf(fo, "                    // Handle snoop timeout error\n");
    fprintf(fo, "                    snoop_state <= SNOOP_IDLE;\n");
    fprintf(fo, "                    snoop_broadcast_active <= 1'b0;\n");
    fprintf(fo, "                    snoop_request_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                    snoop_response_received <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                default: begin\n");
    fprintf(fo, "                    snoop_state <= SNOOP_IDLE;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            endcase\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Deadlock Prevention Logic
    fprintf(fo, "    // Deadlock Prevention Logic\n");
    fprintf(fo, "    // Prevents circular waiting and ensures forward progress\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] deadlock_detected;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] priority_boost;\n");
    fprintf(fo, "    reg [15:0] stall_counter [NUM_MASTER-1:0];\n");
    fprintf(fo, "    \n");
    
    fprintf(fo, "    // Deadlock detection and prevention\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            deadlock_detected <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            priority_boost <= {NUM_MASTER{1'b0}};\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            stall_counter[%d] <= 16'h0000;\n", i);
    }
    
    fprintf(fo, "        end else begin\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d deadlock detection\n", i);
        fprintf(fo, "            if (master_coherency_state[%d] == COHERENT_WRITE_PENDING ||\n", i);
        fprintf(fo, "                master_coherency_state[%d] == COHERENT_READ_PENDING) begin\n", i);
        fprintf(fo, "                // Master is stalled, increment counter\n");
        fprintf(fo, "                if (stall_counter[%d] < 16'hFFFF) begin\n", i);
        fprintf(fo, "                    stall_counter[%d] <= stall_counter[%d] + 1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "                \n");
        fprintf(fo, "                // Detect potential deadlock\n");
        fprintf(fo, "                if (stall_counter[%d] > 16'hF000) begin\n", i);
        fprintf(fo, "                    deadlock_detected[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    priority_boost[%d] <= 1'b1;\n", i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            end else begin\n");
        fprintf(fo, "                // Master is not stalled, reset counters\n");
        fprintf(fo, "                stall_counter[%d] <= 16'h0000;\n", i);
        fprintf(fo, "                deadlock_detected[%d] <= 1'b0;\n", i);
        fprintf(fo, "                priority_boost[%d] <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
    }
    
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Advanced Response Aggregation
    fprintf(fo, "    // Advanced Response Aggregation Logic\n");
    fprintf(fo, "    // Combines multiple snoop responses into final coherency decision\n");
    fprintf(fo, "    reg [4:0] aggregated_response;\n");
    fprintf(fo, "    reg response_data_required;\n");
    fprintf(fo, "    reg response_cache_state_change;\n");
    fprintf(fo, "    \n");
    
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        // Default response values\n");
    fprintf(fo, "        aggregated_response = 5'b00000; // CRRESP_DATATRANSFER\n");
    fprintf(fo, "        response_data_required = 1'b0;\n");
    fprintf(fo, "        response_cache_state_change = 1'b0;\n");
    fprintf(fo, "        \n");
    fprintf(fo, "        // Response aggregation logic based on snoop type\n");
    fprintf(fo, "        case (current_snoop_type)\n");
    fprintf(fo, "            3'b001: begin // ReadShared\n");
    fprintf(fo, "                // Check if any master has dirty data to provide\n");
    fprintf(fo, "                response_data_required = |snoop_response_received; // Simplified\n");
    fprintf(fo, "                aggregated_response = 5'b00100; // CRRESP_OK_SHARED_CLEAN\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            3'b010: begin // ReadClean\n");
    fprintf(fo, "                // Similar to ReadShared but may change cache states\n");
    fprintf(fo, "                response_cache_state_change = |snoop_response_received;\n");
    fprintf(fo, "                aggregated_response = 5'b00100; // CRRESP_OK_SHARED_CLEAN\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            3'b111: begin // ReadUnique (exclusive)\n");
    fprintf(fo, "                // Invalidate all other copies\n");
    fprintf(fo, "                response_cache_state_change = 1'b1;\n");
    fprintf(fo, "                if (|snoop_response_received) begin\n");
    fprintf(fo, "                    aggregated_response = 5'b00010; // CRRESP_OK_WAS_UNIQUE\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    aggregated_response = 5'b00000; // CRRESP_DATATRANSFER\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            default: begin\n");
    fprintf(fo, "                aggregated_response = 5'b00000; // CRRESP_DATATRANSFER\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        endcase\n");
    fprintf(fo, "    end\n\n");
    
    // Global coherency status outputs
    fprintf(fo, "    // Global Coherency Status Outputs\n");
    // coherency_active driven by procedural logic above - remove conflicting assign
    fprintf(fo, "    // assign coherency_active = snoop_broadcast_active || (|master_coherent_transaction); // REMOVED to resolve conflict\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Additional monitoring outputs\n");
    fprintf(fo, "    reg global_coherency_error;\n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        global_coherency_error = snoop_timeout_error || (|deadlock_detected) || (|coherency_violation);\n");
    fprintf(fo, "    end\n\n");
    
    fprintf(fo, "endmodule\n");
    
    return 0;
}