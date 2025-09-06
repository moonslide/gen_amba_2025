//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// Security Firewall Implementation - Optimized for Large Matrices
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "gen_amba_axi.h"
#include "gen_axi_utils.h"

//--------------------------------------------------------
// Generate Security Firewall module compatible with optimized interconnect
//--------------------------------------------------------
int gen_axi_firewall_optimized(unsigned int numM, unsigned int numS,
                               char *prefix, axi_features_t *features, FILE *fo)
{
    int i, j;
    
    if (!features || !features->enable_firewall) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// AXI Security Firewall Module - Optimized for Large Matrices\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %saxi_firewall_optimized\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , WIDTH_ID   = 4)\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                    ACLK\n");
    fprintf(fo, "    , input  wire                    ARESETn\n");
    
    // Security configuration - simplified for optimized version
    fprintf(fo, "    // Security configuration\n");
    fprintf(fo, "    , input  wire [NUM_MASTER-1:0]  master_secure\n");
    fprintf(fo, "    , input  wire [NUM_SLAVE-1:0]   slave_secure\n");
    fprintf(fo, "    , input  wire [NUM_SLAVE-1:0]   slave_nonsec_allowed\n");
    
    // Master interfaces - using optimized interconnect naming
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d interface - optimized signals\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]    M%d_AWID\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]    M%d_AWADDR\n", i);
        fprintf(fo, "    , input  wire [7:0]              M%d_AWLEN\n", i);
        fprintf(fo, "    , input  wire [2:0]              M%d_AWPROT\n", i);
        fprintf(fo, "    , input  wire                   M%d_AWVALID\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]    M%d_ARID\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]    M%d_ARADDR\n", i);
        fprintf(fo, "    , input  wire [7:0]              M%d_ARLEN\n", i);
        fprintf(fo, "    , input  wire [2:0]              M%d_ARPROT\n", i);
        fprintf(fo, "    , input  wire                   M%d_ARVALID\n", i);
    }
    
    // Violation outputs
    fprintf(fo, "    // Security violation outputs\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]  aw_violation\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]  ar_violation\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]  aw_block\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]  ar_block\n");
    fprintf(fo, "    , output reg                    security_alert\n");
    
    fprintf(fo, ");\n\n");
    
    // Address decoding - extract slave selection from address  
    fprintf(fo, "    // Internal slave selection decoder\n");
    for (i = 0; i < numM; i++) {
        int width_slave = calc_width(numS);
        fprintf(fo, "    wire [%d:0] m%d_aw_slave_sel;\n", width_slave-1, i);
        fprintf(fo, "    wire [%d:0] m%d_ar_slave_sel;\n", width_slave-1, i);
        // Simple address-based slave selection (can be enhanced)
        fprintf(fo, "    assign m%d_aw_slave_sel = M%d_AWADDR[%d:%d]; // Extract from address\n", 
                i, i, 31, 32-width_slave);
        fprintf(fo, "    assign m%d_ar_slave_sel = M%d_ARADDR[%d:%d];\n", 
                i, i, 31, 32-width_slave);
    }
    fprintf(fo, "\n");
    
    // Internal registers
    fprintf(fo, "    // Violation tracking\n");
    fprintf(fo, "    reg [31:0] violation_count;\n");
    fprintf(fo, "    reg [WIDTH_ID-1:0] last_violation_id;\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] last_violation_addr;\n");
    fprintf(fo, "    reg last_violation_is_write;\n\n");
    
    // Security checking logic for each master - using optimized signals
    fprintf(fo, "    // Security checking logic\n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        aw_violation = 0;\n");
    fprintf(fo, "        ar_violation = 0;\n");
    fprintf(fo, "        aw_block = 0;\n");
    fprintf(fo, "        ar_block = 0;\n");
    fprintf(fo, "        \n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        // Master %d security check\n", i);
        
        // Write channel check - using optimized signal names
        fprintf(fo, "        if (M%d_AWVALID) begin\n", i);
        fprintf(fo, "            // Check if non-secure access to secure slave\n");
        fprintf(fo, "            if (!master_secure[%d] && slave_secure[m%d_aw_slave_sel] && \n", i, i);
        fprintf(fo, "                !slave_nonsec_allowed[m%d_aw_slave_sel]) begin\n", i);
        fprintf(fo, "                aw_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "                aw_block[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            // Check AxPROT[1] for secure/non-secure transaction\n");
        fprintf(fo, "            if (M%d_AWPROT[1] && slave_secure[m%d_aw_slave_sel] && \n", i, i);
        fprintf(fo, "                !slave_nonsec_allowed[m%d_aw_slave_sel]) begin\n", i);
        fprintf(fo, "                aw_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "                aw_block[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
        
        // Read channel check - using optimized signal names
        fprintf(fo, "        if (M%d_ARVALID) begin\n", i);
        fprintf(fo, "            // Check if non-secure access to secure slave\n");
        fprintf(fo, "            if (!master_secure[%d] && slave_secure[m%d_ar_slave_sel] && \n", i, i);
        fprintf(fo, "                !slave_nonsec_allowed[m%d_ar_slave_sel]) begin\n", i);
        fprintf(fo, "                ar_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "                ar_block[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            // Check AxPROT[1] for secure/non-secure transaction\n");
        fprintf(fo, "            if (M%d_ARPROT[1] && slave_secure[m%d_ar_slave_sel] && \n", i, i);
        fprintf(fo, "                !slave_nonsec_allowed[m%d_ar_slave_sel]) begin\n", i);
        fprintf(fo, "                ar_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "                ar_block[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
    }
    
    fprintf(fo, "        \n");
    fprintf(fo, "        // Global security alert\n");
    fprintf(fo, "        security_alert = |aw_violation | |ar_violation;\n");
    fprintf(fo, "    end\n\n");
    
    // Violation logging
    fprintf(fo, "    // Violation logging\n");
    fprintf(fo, "    always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "        if (!ARESETn) begin\n");
    fprintf(fo, "            violation_count <= 32'd0;\n");
    fprintf(fo, "            last_violation_addr <= 0;\n");
    fprintf(fo, "            last_violation_is_write <= 0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            if (|aw_violation) begin\n");
    fprintf(fo, "                violation_count <= violation_count + 1;\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                if (aw_violation[%d]) begin\n", i);
        fprintf(fo, "                    last_violation_addr <= M%d_AWADDR;\n", i);
        fprintf(fo, "                    last_violation_is_write <= 1'b1;\n");
        fprintf(fo, "                end\n");
    }
    fprintf(fo, "            end\n");
    fprintf(fo, "            if (|ar_violation) begin\n");
    fprintf(fo, "                violation_count <= violation_count + 1;\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                if (ar_violation[%d]) begin\n", i);
        fprintf(fo, "                    last_violation_addr <= M%d_ARADDR;\n", i);
        fprintf(fo, "                    last_violation_is_write <= 1'b0;\n");
        fprintf(fo, "                end\n");
    }
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Secure memory regions
    fprintf(fo, "    // Secure memory region definitions\n");
    fprintf(fo, "    localparam SECURE_REGION_START = 32'h8000_0000;\n");
    fprintf(fo, "    localparam SECURE_REGION_END   = 32'h9000_0000;\n\n");
    
    // Additional region-based security
    fprintf(fo, "    // Region-based security checks\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] aw_in_secure_region;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] ar_in_secure_region;\n\n");
    
    fprintf(fo, "    always @(*) begin\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        aw_in_secure_region[%d] = (M%d_AWADDR >= SECURE_REGION_START) && \n", i, i);
        fprintf(fo, "                                  (M%d_AWADDR < SECURE_REGION_END);\n", i);
        fprintf(fo, "        ar_in_secure_region[%d] = (M%d_ARADDR >= SECURE_REGION_START) && \n", i, i);
        fprintf(fo, "                                  (M%d_ARADDR < SECURE_REGION_END);\n", i);
    }
    fprintf(fo, "    end\n\n");
    
    fprintf(fo, "endmodule\n\n");
    
    return 0;
}