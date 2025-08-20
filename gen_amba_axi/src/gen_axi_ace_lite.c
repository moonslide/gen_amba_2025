//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite (AXI Coherency Extensions Lite) Implementation
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "gen_amba_axi.h"
#include "gen_axi_utils.h"

//--------------------------------------------------------
// Generate ACE-Lite signals for interconnect
//--------------------------------------------------------
int gen_axi_ace_lite(unsigned int numM, unsigned int numS, 
                     char *prefix, axi_features_t *features, FILE *fo)
{
    int i;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite Coherency Signals\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite adds coherency support for I/O coherent masters\n");
    fprintf(fo, "// These signals enable cache coherent transactions\n\n");
    
    // Generate parameter definitions
    fprintf(fo, "    // ACE-Lite parameters\n");
    fprintf(fo, "    localparam WIDTH_DOMAIN = %d;  // Shareability domain\n", features->width_domain);
    fprintf(fo, "    localparam WIDTH_SNOOP_AW = %d; // Write snoop type\n", features->width_snoop_aw);
    fprintf(fo, "    localparam WIDTH_SNOOP_AR = %d; // Read snoop type\n", features->width_snoop_ar);
    fprintf(fo, "    localparam WIDTH_BAR = %d;     // Barrier type\n\n", features->width_bar);
    
    // Domain encoding definitions
    fprintf(fo, "    // Domain encodings (shareability)\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_NON_SHAREABLE = 2'b00;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_INNER_SHAREABLE = 2'b01;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_OUTER_SHAREABLE = 2'b10;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_SYSTEM = 2'b11;\n\n");
    
    // Snoop encoding definitions for writes
    fprintf(fo, "    // Write snoop encodings (ACE-Lite subset)\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_NO_SNOOP = 3'b000;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_LINE_UNIQUE = 3'b001;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_CLEAN = 3'b010;\n");
    fprintf(fo, "    // Additional ACE-Lite write snoops\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_BACK = 3'b011;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_EVICT = 3'b100;\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_EVICT = 3'b101;\n\n");
    
    // Snoop encoding definitions for reads
    fprintf(fo, "    // Read snoop encodings (ACE-Lite subset)\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_NO_SNOOP = 4'b0000;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_ONCE = 4'b0001;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_SHARED = 4'b0001;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_CLEAN = 4'b0010;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_NOT_SHARED_DIRTY = 4'b0011;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_UNIQUE = 4'b0111;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_CLEAN_UNIQUE = 4'b1011;\n\n");
    
    // Barrier encoding definitions
    fprintf(fo, "    // Barrier type encodings\n");
    fprintf(fo, "    localparam [1:0] BAR_NORMAL_ACCESS = 2'b00;\n");
    fprintf(fo, "    localparam [1:0] BAR_MEMORY_BARRIER = 2'b01;\n");
    fprintf(fo, "    localparam [1:0] BAR_RESERVED = 2'b10;\n");
    fprintf(fo, "    localparam [1:0] BAR_SYNC_BARRIER = 2'b11;\n\n");
    
    // Generate ACE-Lite signals for each master
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d ACE-Lite signals\n", i);
        fprintf(fo, "    wire [WIDTH_DOMAIN-1:0] M%d_AWDOMAIN;\n", i);
        fprintf(fo, "    wire [WIDTH_SNOOP_AW-1:0] M%d_AWSNOOP;\n", i);
        fprintf(fo, "    wire [WIDTH_BAR-1:0] M%d_AWBAR;\n", i);
        fprintf(fo, "    wire [WIDTH_DOMAIN-1:0] M%d_ARDOMAIN;\n", i);
        fprintf(fo, "    wire [WIDTH_SNOOP_AR-1:0] M%d_ARSNOOP;\n", i);
        fprintf(fo, "    wire [WIDTH_BAR-1:0] M%d_ARBAR;\n\n", i);
    }
    
    // Generate ACE-Lite signals for each slave
    for (i = 0; i < numS; i++) {
        fprintf(fo, "    // Slave %d ACE-Lite signals\n", i);
        fprintf(fo, "    wire [WIDTH_DOMAIN-1:0] S%d_AWDOMAIN;\n", i);
        fprintf(fo, "    wire [WIDTH_SNOOP_AW-1:0] S%d_AWSNOOP;\n", i);
        fprintf(fo, "    wire [WIDTH_BAR-1:0] S%d_AWBAR;\n", i);
        fprintf(fo, "    wire [WIDTH_DOMAIN-1:0] S%d_ARDOMAIN;\n", i);
        fprintf(fo, "    wire [WIDTH_SNOOP_AR-1:0] S%d_ARSNOOP;\n", i);
        fprintf(fo, "    wire [WIDTH_BAR-1:0] S%d_ARBAR;\n\n", i);
    }
    
    // Generate coherency checking logic
    fprintf(fo, "    // Coherency checking logic\n");
    fprintf(fo, "    // This ensures coherent transactions are handled correctly\n");
    fprintf(fo, "    reg coherency_error;\n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        coherency_error = 1'b0;\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        // Check Master %d coherency\n", i);
        fprintf(fo, "        if (M%d_AWVALID && M%d_AWDOMAIN != DOMAIN_NON_SHAREABLE) begin\n", i, i);
        fprintf(fo, "            // Coherent write transaction\n");
        fprintf(fo, "            if (M%d_AWSNOOP == AWSNOOP_WRITE_NO_SNOOP) begin\n", i);
        fprintf(fo, "                // Error: Shareable domain but no snoop\n");
        fprintf(fo, "                coherency_error = 1'b1;\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
    }
    
    fprintf(fo, "    end\n\n");
    
    // Generate interconnect routing for ACE-Lite signals
    fprintf(fo, "    // ACE-Lite signal routing through interconnect\n");
    fprintf(fo, "    // These signals must be preserved through the interconnect\n");
    fprintf(fo, "    // to maintain coherency information\n\n");
    
    // Generate routing logic for master-to-slave connections
    fprintf(fo, "    // Master-to-Slave ACE-Lite signal routing\n");
    for (i = 0; i < numS; i++) {
        fprintf(fo, "    // Routing to Slave %d\n", i);
        fprintf(fo, "    always @(*) begin\n");
        fprintf(fo, "        // Default assignments\n");
        fprintf(fo, "        S%d_AWDOMAIN = 2'b00;\n", i);
        fprintf(fo, "        S%d_AWSNOOP = 3'b000;\n", i);
        fprintf(fo, "        S%d_AWBAR = 2'b00;\n", i);
        fprintf(fo, "        S%d_ARDOMAIN = 2'b00;\n", i);
        fprintf(fo, "        S%d_ARSNOOP = 4'b0000;\n", i);
        fprintf(fo, "        S%d_ARBAR = 2'b00;\n", i);
        fprintf(fo, "        \n");
        fprintf(fo, "        // Route from active master based on arbiter selection\n");
        fprintf(fo, "        case (1'b1) // synthesis parallel_case\n");
        
        for (int j = 0; j < numM; j++) {
            fprintf(fo, "            AWSELECT_OUT[%d][%d]: begin\n", i, j);
            fprintf(fo, "                S%d_AWDOMAIN = M%d_AWDOMAIN;\n", i, j);
            fprintf(fo, "                S%d_AWSNOOP = M%d_AWSNOOP;\n", i, j);
            fprintf(fo, "                S%d_AWBAR = M%d_AWBAR;\n", i, j);
            fprintf(fo, "            end\n");
        }
        fprintf(fo, "        endcase\n");
        
        fprintf(fo, "        \n");
        fprintf(fo, "        case (1'b1) // synthesis parallel_case\n");
        for (int j = 0; j < numM; j++) {
            fprintf(fo, "            ARSELECT_OUT[%d][%d]: begin\n", i, j);
            fprintf(fo, "                S%d_ARDOMAIN = M%d_ARDOMAIN;\n", i, j);
            fprintf(fo, "                S%d_ARSNOOP = M%d_ARSNOOP;\n", i, j);
            fprintf(fo, "                S%d_ARBAR = M%d_ARBAR;\n", i, j);
            fprintf(fo, "            end\n");
        }
        fprintf(fo, "        endcase\n");
        fprintf(fo, "    end\n\n");
    }
    
    // Generate cache maintenance operation detection
    fprintf(fo, "    // Cache maintenance operation detection\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] cache_maint_wr;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] cache_maint_rd;\n");
    fprintf(fo, "    always @(*) begin\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        cache_maint_wr[%d] = (M%d_AWSNOOP == AWSNOOP_WRITE_CLEAN) ||\n", i, i);
        fprintf(fo, "                              (M%d_AWSNOOP == AWSNOOP_WRITE_LINE_UNIQUE) ||\n", i);
        fprintf(fo, "                              (M%d_AWSNOOP == AWSNOOP_EVICT);\n", i);
        fprintf(fo, "        cache_maint_rd[%d] = (M%d_ARSNOOP == ARSNOOP_READ_CLEAN) ||\n", i, i);
        fprintf(fo, "                              (M%d_ARSNOOP == ARSNOOP_CLEAN_UNIQUE);\n", i);
    }
    fprintf(fo, "    end\n\n");
    
    // Generate barrier transaction handling
    fprintf(fo, "    // Barrier transaction handling\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] barrier_pending;\n");
    fprintf(fo, "    always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "        if (!ARESETn) begin\n");
    fprintf(fo, "            barrier_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "        end else begin\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            if (M%d_AWVALID && (M%d_AWBAR != BAR_NORMAL_ACCESS)) begin\n", i, i);
        fprintf(fo, "                barrier_pending[%d] <= 1'b1;\n", i);
        fprintf(fo, "            end else if (M%d_BVALID && M%d_BREADY) begin\n", i, i);
        fprintf(fo, "                barrier_pending[%d] <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
    }
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    return 0;
}

//--------------------------------------------------------
// Add ACE-Lite ports to master interface
//--------------------------------------------------------
int gen_axi_ace_lite_mport(char *prefix, char *otype, axi_features_t *features, FILE *fo)
{
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "     `ifdef AMBA_ACE_LITE\n");
    fprintf(fo, "     // ACE-Lite coherency signals\n");
    fprintf(fo, "     , input  %s  [1:0]              %sAWDOMAIN\n", otype, prefix);
    fprintf(fo, "     , input  %s  [2:0]              %sAWSNOOP\n", otype, prefix);
    fprintf(fo, "     , input  %s  [1:0]              %sAWBAR\n", otype, prefix);
    fprintf(fo, "     , input  %s  [1:0]              %sARDOMAIN\n", otype, prefix);
    fprintf(fo, "     , input  %s  [3:0]              %sARSNOOP\n", otype, prefix);
    fprintf(fo, "     , input  %s  [1:0]              %sARBAR\n", otype, prefix);
    fprintf(fo, "     `endif\n");
    
    return 0;
}

//--------------------------------------------------------
// Add ACE-Lite ports to slave interface
//--------------------------------------------------------
int gen_axi_ace_lite_sport(char *prefix, char *otype, axi_features_t *features, FILE *fo)
{
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "     `ifdef AMBA_ACE_LITE\n");
    fprintf(fo, "     // ACE-Lite coherency signals\n");
    fprintf(fo, "     , output %s  [1:0]              %sAWDOMAIN\n", otype, prefix);
    fprintf(fo, "     , output %s  [2:0]              %sAWSNOOP\n", otype, prefix);
    fprintf(fo, "     , output %s  [1:0]              %sAWBAR\n", otype, prefix);
    fprintf(fo, "     , output %s  [1:0]              %sARDOMAIN\n", otype, prefix);
    fprintf(fo, "     , output %s  [3:0]              %sARSNOOP\n", otype, prefix);
    fprintf(fo, "     , output %s  [1:0]              %sARBAR\n", otype, prefix);
    fprintf(fo, "     // ACE-Lite response signals\n");
    fprintf(fo, "     , input  %s                     %sRACK\n", otype, prefix);
    fprintf(fo, "     , input  %s                     %sWACK\n", otype, prefix);
    fprintf(fo, "     `endif\n");
    
    return 0;
}

//--------------------------------------------------------
// Generate ACE-Lite snoop channel handlers
//--------------------------------------------------------
int gen_axi_ace_lite_snoop_handler(unsigned int numM, unsigned int numS, 
                                   char *prefix, axi_features_t *features, FILE *fo)
{
    int i;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite Snoop Channel Handler\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "// Manages snoop requests and responses for cache coherency\n\n");
    
    // Generate snoop request tracking
    fprintf(fo, "    // Snoop request tracking\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] snoop_pending;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] snoop_complete;\n");
    fprintf(fo, "    reg [WIDTH_ID-1:0] snoop_id [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] snoop_addr [NUM_MASTER-1:0];\n\n");
    
    // Generate snoop request detection logic
    fprintf(fo, "    // Snoop request detection and tracking\n");
    fprintf(fo, "    always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "        if (!ARESETn) begin\n");
    fprintf(fo, "            snoop_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            snoop_complete <= {NUM_MASTER{1'b0}};\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            snoop_id[%d] <= {WIDTH_ID{1'b0}};\n", i);
        fprintf(fo, "            snoop_addr[%d] <= {WIDTH_AD{1'b0}};\n", i);
    }
    fprintf(fo, "        end else begin\n");
    
    // Write snoop handling
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d write snoop\n", i);
        fprintf(fo, "            if (M%d_AWVALID && M%d_AWREADY && ", i, i);
        fprintf(fo, "(M%d_AWSNOOP != AWSNOOP_WRITE_NO_SNOOP)) begin\n", i);
        fprintf(fo, "                snoop_pending[%d] <= 1'b1;\n", i);
        fprintf(fo, "                snoop_id[%d] <= M%d_AWID;\n", i, i);
        fprintf(fo, "                snoop_addr[%d] <= M%d_AWADDR;\n", i, i);
        fprintf(fo, "            end else if (snoop_pending[%d] && M%d_BVALID && M%d_BREADY) begin\n", i, i, i);
        fprintf(fo, "                snoop_pending[%d] <= 1'b0;\n", i);
        fprintf(fo, "                snoop_complete[%d] <= 1'b1;\n", i);
        fprintf(fo, "            end\n\n");
        
        // Read snoop handling
        fprintf(fo, "            // Master %d read snoop\n", i);
        fprintf(fo, "            if (M%d_ARVALID && M%d_ARREADY && ", i, i);
        fprintf(fo, "(M%d_ARSNOOP != ARSNOOP_READ_NO_SNOOP)) begin\n", i);
        fprintf(fo, "                snoop_pending[%d] <= 1'b1;\n", i);
        fprintf(fo, "                snoop_id[%d] <= M%d_ARID;\n", i, i);
        fprintf(fo, "                snoop_addr[%d] <= M%d_ARADDR;\n", i, i);
        fprintf(fo, "            end else if (snoop_pending[%d] && M%d_RLAST && M%d_RVALID && M%d_RREADY) begin\n", i, i, i, i);
        fprintf(fo, "                snoop_pending[%d] <= 1'b0;\n", i);
        fprintf(fo, "                snoop_complete[%d] <= 1'b1;\n", i);
        fprintf(fo, "            end\n");
    }
    
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Generate snoop response aggregation
    fprintf(fo, "    // Snoop response aggregation\n");
    fprintf(fo, "    // Combines snoop responses from multiple masters\n");
    fprintf(fo, "    reg [1:0] combined_resp;\n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        combined_resp = 2'b00; // OKAY by default\n");
    fprintf(fo, "        // Priority: EXOKAY > OKAY > SLVERR > DECERR\n");
    fprintf(fo, "        // Actual implementation would aggregate based on coherency protocol\n");
    fprintf(fo, "    end\n\n");
    
    return 0;
}

//--------------------------------------------------------
// Generate ACE-Lite barrier synchronization logic
//--------------------------------------------------------
int gen_axi_ace_lite_barrier_sync(unsigned int numM, char *prefix, 
                                  axi_features_t *features, FILE *fo)
{
    int i;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite Barrier Synchronization\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "// Ensures ordering of transactions around barriers\n\n");
    
    // Generate barrier state machine
    fprintf(fo, "    // Barrier state machine for each master\n");
    fprintf(fo, "    localparam [1:0] BARRIER_IDLE = 2'b00;\n");
    fprintf(fo, "    localparam [1:0] BARRIER_WAIT = 2'b01;\n");
    fprintf(fo, "    localparam [1:0] BARRIER_COMPLETE = 2'b10;\n\n");
    
    fprintf(fo, "    reg [1:0] barrier_state [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] barrier_block;\n\n");
    
    fprintf(fo, "    always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "        if (!ARESETn) begin\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            barrier_state[%d] <= BARRIER_IDLE;\n", i);
    }
    fprintf(fo, "            barrier_block <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "        end else begin\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d barrier handling\n", i);
        fprintf(fo, "            case (barrier_state[%d])\n", i);
        fprintf(fo, "                BARRIER_IDLE: begin\n");
        fprintf(fo, "                    if (M%d_AWVALID && (M%d_AWBAR == BAR_MEMORY_BARRIER || ", i, i);
        fprintf(fo, "M%d_AWBAR == BAR_SYNC_BARRIER)) begin\n", i);
        fprintf(fo, "                        barrier_state[%d] <= BARRIER_WAIT;\n", i);
        fprintf(fo, "                        barrier_block[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end else if (M%d_ARVALID && (M%d_ARBAR == BAR_MEMORY_BARRIER || ", i, i);
        fprintf(fo, "M%d_ARBAR == BAR_SYNC_BARRIER)) begin\n", i);
        fprintf(fo, "                        barrier_state[%d] <= BARRIER_WAIT;\n", i);
        fprintf(fo, "                        barrier_block[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                BARRIER_WAIT: begin\n");
        fprintf(fo, "                    // Wait for all previous transactions to complete\n");
        fprintf(fo, "                    if (!snoop_pending[%d] && !M%d_AWVALID && !M%d_ARVALID) begin\n", i, i, i);
        fprintf(fo, "                        barrier_state[%d] <= BARRIER_COMPLETE;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                BARRIER_COMPLETE: begin\n");
        fprintf(fo, "                    barrier_state[%d] <= BARRIER_IDLE;\n", i);
        fprintf(fo, "                    barrier_block[%d] <= 1'b0;\n", i);
        fprintf(fo, "                end\n");
        fprintf(fo, "                default: barrier_state[%d] <= BARRIER_IDLE;\n", i);
        fprintf(fo, "            endcase\n");
    }
    
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Generate barrier enforcement logic
    fprintf(fo, "    // Barrier enforcement - block new transactions during barrier\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    assign M%d_barrier_block = barrier_block[%d];\n", i, i);
    }
    fprintf(fo, "\n");
    
    return 0;
}