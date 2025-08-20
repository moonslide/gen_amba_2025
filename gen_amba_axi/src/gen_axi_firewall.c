//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// Security Firewall Implementation
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "gen_amba_axi.h"
#include "gen_axi_utils.h"

//--------------------------------------------------------
// Generate Security Firewall module
//--------------------------------------------------------
int gen_axi_firewall(unsigned int numM, unsigned int numS,
                    char *prefix, axi_features_t *features, FILE *fo)
{
    int i, j;
    
    if (!features || !features->enable_firewall) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// AXI Security Firewall Module\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %saxi_firewall\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , WIDTH_ID   = 4)\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                    clk\n");
    fprintf(fo, "    , input  wire                    rst_n\n");
    
    // Security configuration
    fprintf(fo, "    // Security configuration\n");
    fprintf(fo, "    , input  wire [NUM_MASTER-1:0]  master_secure\n");
    fprintf(fo, "    , input  wire [NUM_SLAVE-1:0]   slave_secure\n");
    fprintf(fo, "    , input  wire [NUM_SLAVE-1:0]   slave_nonsec_allowed\n");
    
    // Master interfaces
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d interface\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]    m%d_awid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]    m%d_awaddr\n", i);
        fprintf(fo, "    , input  wire [7:0]              m%d_awlen\n", i);
        fprintf(fo, "    , input  wire [2:0]              m%d_awprot\n", i);
        fprintf(fo, "    , input  wire                   m%d_awvalid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]    m%d_arid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]    m%d_araddr\n", i);
        fprintf(fo, "    , input  wire [7:0]              m%d_arlen\n", i);
        fprintf(fo, "    , input  wire [2:0]              m%d_arprot\n", i);
        fprintf(fo, "    , input  wire                   m%d_arvalid\n", i);
    }
    
    // Slave selection inputs
    for (i = 0; i < numM; i++) {
        int width_slave = calc_width(numS);
        fprintf(fo, "    , input  wire [%d:0] m%d_aw_slave_sel // %d slaves\n", width_slave-1, i, numS);
        fprintf(fo, "    , input  wire [%d:0] m%d_ar_slave_sel\n", width_slave-1, i);
    }
    
    // Violation outputs
    fprintf(fo, "    // Security violation outputs\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]  aw_violation\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]  ar_violation\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]  aw_block\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]  ar_block\n");
    fprintf(fo, "    , output reg                    security_alert\n");
    
    // Error response generation
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d error responses\n", i);
        fprintf(fo, "    , output reg  [WIDTH_ID-1:0]    m%d_bid_err\n", i);
        fprintf(fo, "    , output reg  [1:0]              m%d_bresp_err\n", i);
        fprintf(fo, "    , output reg                    m%d_bvalid_err\n", i);
        fprintf(fo, "    , input  wire                   m%d_bready\n", i);
        fprintf(fo, "    , output reg  [WIDTH_ID-1:0]    m%d_rid_err\n", i);
        fprintf(fo, "    , output reg  [WIDTH_DA-1:0]    m%d_rdata_err\n", i);
        fprintf(fo, "    , output reg  [1:0]              m%d_rresp_err\n", i);
        fprintf(fo, "    , output reg                    m%d_rlast_err\n", i);
        fprintf(fo, "    , output reg                    m%d_rvalid_err\n", i);
        fprintf(fo, "    , input  wire                   m%d_rready\n", i);
    }
    
    fprintf(fo, ");\n\n");
    
    // Internal registers
    fprintf(fo, "    // Violation tracking\n");
    fprintf(fo, "    reg [31:0] violation_count;\n");
    fprintf(fo, "    reg [WIDTH_ID-1:0] last_violation_id;\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] last_violation_addr;\n");
    fprintf(fo, "    reg last_violation_is_write;\n\n");
    
    // Security checking logic for each master
    fprintf(fo, "    // Security checking logic\n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        aw_violation = 0;\n");
    fprintf(fo, "        ar_violation = 0;\n");
    fprintf(fo, "        aw_block = 0;\n");
    fprintf(fo, "        ar_block = 0;\n");
    fprintf(fo, "        \n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        // Master %d security check\n", i);
        
        // Write channel check
        fprintf(fo, "        if (m%d_awvalid) begin\n", i);
        fprintf(fo, "            // Check if non-secure access to secure slave\n");
        fprintf(fo, "            if (!master_secure[%d] && slave_secure[m%d_aw_slave_sel] && \n", i, i);
        fprintf(fo, "                !slave_nonsec_allowed[m%d_aw_slave_sel]) begin\n", i);
        fprintf(fo, "                aw_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "                aw_block[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            // Check AxPROT[1] for secure/non-secure transaction\n");
        fprintf(fo, "            if (m%d_awprot[1] && slave_secure[m%d_aw_slave_sel] && \n", i, i);
        fprintf(fo, "                !slave_nonsec_allowed[m%d_aw_slave_sel]) begin\n", i);
        fprintf(fo, "                aw_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "                aw_block[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
        
        // Read channel check
        fprintf(fo, "        if (m%d_arvalid) begin\n", i);
        fprintf(fo, "            // Check if non-secure access to secure slave\n");
        fprintf(fo, "            if (!master_secure[%d] && slave_secure[m%d_ar_slave_sel] && \n", i, i);
        fprintf(fo, "                !slave_nonsec_allowed[m%d_ar_slave_sel]) begin\n", i);
        fprintf(fo, "                ar_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "                ar_block[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            // Check AxPROT[1] for secure/non-secure transaction\n");
        fprintf(fo, "            if (m%d_arprot[1] && slave_secure[m%d_ar_slave_sel] && \n", i, i);
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
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            violation_count <= 32'd0;\n");
    fprintf(fo, "            last_violation_addr <= 0;\n");
    fprintf(fo, "            last_violation_is_write <= 0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            if (|aw_violation) begin\n");
    fprintf(fo, "                violation_count <= violation_count + 1;\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                if (aw_violation[%d]) begin\n", i);
        fprintf(fo, "                    last_violation_addr <= m%d_awaddr;\n", i);
        fprintf(fo, "                    last_violation_is_write <= 1'b1;\n");
        fprintf(fo, "                end\n");
    }
    fprintf(fo, "            end\n");
    fprintf(fo, "            if (|ar_violation) begin\n");
    fprintf(fo, "                violation_count <= violation_count + 1;\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "                if (ar_violation[%d]) begin\n", i);
        fprintf(fo, "                    last_violation_addr <= m%d_araddr;\n", i);
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
        fprintf(fo, "        aw_in_secure_region[%d] = (m%d_awaddr >= SECURE_REGION_START) && \n", i, i);
        fprintf(fo, "                                  (m%d_awaddr < SECURE_REGION_END);\n", i);
        fprintf(fo, "        ar_in_secure_region[%d] = (m%d_araddr >= SECURE_REGION_START) && \n", i, i);
        fprintf(fo, "                                  (m%d_araddr < SECURE_REGION_END);\n", i);
    }
    fprintf(fo, "    end\n\n");
    
    // Error response generation logic
    fprintf(fo, "    // Error response generation for blocked transactions\n");
    fprintf(fo, "    // BRESP = 2'b10 (SLVERR), RRESP = 2'b10 (SLVERR)\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d error response generation\n", i);
        
        // Write response error generation
        fprintf(fo, "    reg m%d_aw_blocked;\n", i);
        fprintf(fo, "    reg [WIDTH_ID-1:0] m%d_awid_blocked;\n", i);
        fprintf(fo, "    reg [7:0] m%d_awlen_blocked;\n", i);
        fprintf(fo, "    \n");
        
        fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
        fprintf(fo, "        if (!rst_n) begin\n");
        fprintf(fo, "            m%d_aw_blocked <= 1'b0;\n", i);
        fprintf(fo, "            m%d_awid_blocked <= 0;\n", i);
        fprintf(fo, "            m%d_awlen_blocked <= 0;\n", i);
        fprintf(fo, "            m%d_bvalid_err <= 1'b0;\n", i);
        fprintf(fo, "            m%d_bid_err <= 0;\n", i);
        fprintf(fo, "            m%d_bresp_err <= 2'b00;\n", i);
        fprintf(fo, "        end else begin\n");
        fprintf(fo, "            // Capture blocked write transaction\n");
        fprintf(fo, "            if (aw_block[%d] && m%d_awvalid) begin\n", i, i);
        fprintf(fo, "                m%d_aw_blocked <= 1'b1;\n", i);
        fprintf(fo, "                m%d_awid_blocked <= m%d_awid;\n", i, i);
        fprintf(fo, "                m%d_awlen_blocked <= m%d_awlen;\n", i, i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Generate BRESP error\n");
        fprintf(fo, "            if (m%d_aw_blocked && !m%d_bvalid_err) begin\n", i, i);
        fprintf(fo, "                m%d_bvalid_err <= 1'b1;\n", i);
        fprintf(fo, "                m%d_bid_err <= m%d_awid_blocked;\n", i, i);
        fprintf(fo, "                m%d_bresp_err <= 2'b10; // SLVERR\n", i);
        fprintf(fo, "            end else if (m%d_bvalid_err && m%d_bready) begin\n", i, i);
        fprintf(fo, "                m%d_bvalid_err <= 1'b0;\n", i);
        fprintf(fo, "                m%d_aw_blocked <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "    end\n\n");
        
        // Read response error generation
        fprintf(fo, "    reg m%d_ar_blocked;\n", i);
        fprintf(fo, "    reg [WIDTH_ID-1:0] m%d_arid_blocked;\n", i);
        fprintf(fo, "    reg [7:0] m%d_arlen_blocked;\n", i);
        fprintf(fo, "    reg [7:0] m%d_rbeat_cnt;\n", i);
        fprintf(fo, "    \n");
        
        fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
        fprintf(fo, "        if (!rst_n) begin\n");
        fprintf(fo, "            m%d_ar_blocked <= 1'b0;\n", i);
        fprintf(fo, "            m%d_arid_blocked <= 0;\n", i);
        fprintf(fo, "            m%d_arlen_blocked <= 0;\n", i);
        fprintf(fo, "            m%d_rvalid_err <= 1'b0;\n", i);
        fprintf(fo, "            m%d_rid_err <= 0;\n", i);
        fprintf(fo, "            m%d_rdata_err <= 0;\n", i);
        fprintf(fo, "            m%d_rresp_err <= 2'b00;\n", i);
        fprintf(fo, "            m%d_rlast_err <= 1'b0;\n", i);
        fprintf(fo, "            m%d_rbeat_cnt <= 0;\n", i);
        fprintf(fo, "        end else begin\n");
        fprintf(fo, "            // Capture blocked read transaction\n");
        fprintf(fo, "            if (ar_block[%d] && m%d_arvalid) begin\n", i, i);
        fprintf(fo, "                m%d_ar_blocked <= 1'b1;\n", i);
        fprintf(fo, "                m%d_arid_blocked <= m%d_arid;\n", i, i);
        fprintf(fo, "                m%d_arlen_blocked <= m%d_arlen;\n", i, i);
        fprintf(fo, "                m%d_rbeat_cnt <= 0;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Generate RRESP error for all beats\n");
        fprintf(fo, "            if (m%d_ar_blocked && !m%d_rvalid_err) begin\n", i, i);
        fprintf(fo, "                m%d_rvalid_err <= 1'b1;\n", i);
        fprintf(fo, "                m%d_rid_err <= m%d_arid_blocked;\n", i, i);
        fprintf(fo, "                m%d_rdata_err <= {WIDTH_DA{1'b0}}; // Return zeros\n", i);
        fprintf(fo, "                m%d_rresp_err <= 2'b10; // SLVERR\n", i);
        fprintf(fo, "                m%d_rlast_err <= (m%d_rbeat_cnt == m%d_arlen_blocked);\n", i, i, i);
        fprintf(fo, "            end else if (m%d_rvalid_err && m%d_rready) begin\n", i, i);
        fprintf(fo, "                if (m%d_rlast_err) begin\n", i);
        fprintf(fo, "                    m%d_rvalid_err <= 1'b0;\n", i);
        fprintf(fo, "                    m%d_ar_blocked <= 1'b0;\n", i);
        fprintf(fo, "                    m%d_rlast_err <= 1'b0;\n", i);
        fprintf(fo, "                end else begin\n");
        fprintf(fo, "                    m%d_rbeat_cnt <= m%d_rbeat_cnt + 1;\n", i, i);
        fprintf(fo, "                    m%d_rlast_err <= (m%d_rbeat_cnt + 1 == m%d_arlen_blocked);\n", i, i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "    end\n\n");
    }
    
    fprintf(fo, "endmodule\n");
    
    return 0;
}