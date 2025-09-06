//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite Domain Manager Module Generator
// Shareability domain routing and management
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "../../gen_amba_axi.h"
#include "../../gen_axi_utils.h"

//--------------------------------------------------------
// Generate ACE-Lite domain manager module
//--------------------------------------------------------
int gen_ace_lite_domain_manager(unsigned int numM, unsigned int numS, unsigned int widthAD, unsigned int widthDA,
                                char *prefix, axi_features_t *features, FILE *fo)
{
    int i, j;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite Domain Manager\n");
    fprintf(fo, "// Shareability domain routing and coherency scope management\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %sace_lite_domain_manager\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , NUM_DOMAINS = 4) // Support up to 4 coherency domains\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                       clk\n");
    fprintf(fo, "    , input  wire                       rst_n\n");
    
    // Master domain interface inputs
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d domain interface\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]       m%d_awaddr\n", i);
        fprintf(fo, "    , input  wire [1:0]                m%d_awdomain\n", i);
        fprintf(fo, "    , input  wire [2:0]                m%d_awsnoop\n", i);
        fprintf(fo, "    , input  wire                      m%d_awvalid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]       m%d_araddr\n", i);
        fprintf(fo, "    , input  wire [1:0]                m%d_ardomain\n", i);
        fprintf(fo, "    , input  wire [3:0]                m%d_arsnoop\n", i);
        fprintf(fo, "    , input  wire                      m%d_arvalid\n", i);
    }
    
    // Domain configuration inputs
    fprintf(fo, "    // Domain configuration\n");
    fprintf(fo, "    , input  wire [WIDTH_AD-1:0]        domain_base_addr [NUM_DOMAINS-1:0]\n");
    fprintf(fo, "    , input  wire [WIDTH_AD-1:0]        domain_addr_mask [NUM_DOMAINS-1:0]\n");
    fprintf(fo, "    , input  wire [NUM_DOMAINS-1:0]     domain_enable\n");
    fprintf(fo, "    , input  wire [1:0]                 domain_type [NUM_DOMAINS-1:0]\n");
    fprintf(fo, "    , input  wire [NUM_MASTER-1:0]      master_domain_membership [NUM_DOMAINS-1:0]\n");
    
    // Domain management outputs
    fprintf(fo, "    // Domain management outputs\n");
    fprintf(fo, "    , output reg  [1:0]                 resolved_awdomain [NUM_MASTER-1:0]\n");
    fprintf(fo, "    , output reg  [1:0]                 resolved_ardomain [NUM_MASTER-1:0]\n");
    fprintf(fo, "    , output wire [NUM_DOMAINS-1:0]     domain_active\n");
    fprintf(fo, "    , output wire [NUM_MASTER-1:0]      coherency_required\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]      domain_violation\n");
    fprintf(fo, "    , output wire [7:0]                 domain_transaction_count [NUM_DOMAINS-1:0]\n");
    
    fprintf(fo, ");\n\n");
    
    // Domain type encodings
    fprintf(fo, "    // Shareability domain encodings\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_NON_SHAREABLE = 2'b00;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_INNER_SHAREABLE = 2'b01;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_OUTER_SHAREABLE = 2'b10;\n");
    fprintf(fo, "    localparam [1:0] DOMAIN_SYSTEM = 2'b11;\n\n");
    
    // Snoop encodings for domain checking
    fprintf(fo, "    // Snoop encodings for domain validation\n");
    fprintf(fo, "    localparam [2:0] AWSNOOP_WRITE_NO_SNOOP = 3'b000;\n");
    fprintf(fo, "    localparam [3:0] ARSNOOP_READ_NO_SNOOP = 4'b0000;\n\n");
    
    // Domain resolution logic
    fprintf(fo, "    // Address to domain mapping function\n");
    fprintf(fo, "    function [1:0] resolve_domain;\n");
    fprintf(fo, "        input [WIDTH_AD-1:0] addr;\n");
    fprintf(fo, "        input [1:0] requested_domain;\n");
    fprintf(fo, "        integer k;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            resolve_domain = DOMAIN_NON_SHAREABLE; // Default\n");
    fprintf(fo, "            // Check if address falls in any configured domain\n");
    fprintf(fo, "            for (k = 0; k < NUM_DOMAINS; k = k + 1) begin\n");
    fprintf(fo, "                if (domain_enable[k] && \n");
    fprintf(fo, "                    ((addr & domain_addr_mask[k]) == domain_base_addr[k])) begin\n");
    fprintf(fo, "                    // Address is in this domain\n");
    fprintf(fo, "                    if (requested_domain <= domain_type[k]) begin\n");
    fprintf(fo, "                        resolve_domain = requested_domain;\n");
    fprintf(fo, "                    end else begin\n");
    fprintf(fo, "                        resolve_domain = domain_type[k]; // Downgrade to max supported\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Master domain membership check
    fprintf(fo, "    // Master domain membership validation\n");
    fprintf(fo, "    function domain_membership_valid;\n");
    fprintf(fo, "        input [7:0] master_id;\n");
    fprintf(fo, "        input [1:0] domain;\n");
    fprintf(fo, "        integer k;\n");
    fprintf(fo, "        begin\n");
    fprintf(fo, "            domain_membership_valid = 1'b1; // Default allow\n");
    fprintf(fo, "            if (domain != DOMAIN_NON_SHAREABLE) begin\n");
    fprintf(fo, "                domain_membership_valid = 1'b0; // Require explicit membership\n");
    fprintf(fo, "                for (k = 0; k < NUM_DOMAINS; k = k + 1) begin\n");
    fprintf(fo, "                    if (domain_enable[k] && (domain_type[k] == domain) &&\n");
    fprintf(fo, "                        master_domain_membership[k][master_id]) begin\n");
    fprintf(fo, "                        domain_membership_valid = 1'b1;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endfunction\n\n");
    
    // Transaction counters per domain
    fprintf(fo, "    // Domain transaction tracking\n");
    fprintf(fo, "    reg [7:0] domain_aw_count [NUM_DOMAINS-1:0];\n");
    fprintf(fo, "    reg [7:0] domain_ar_count [NUM_DOMAINS-1:0];\n");
    
    // Generate domain resolution logic for each master
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d domain resolution\n", i);
        fprintf(fo, "    always @(*) begin\n");
        fprintf(fo, "        // Write address domain resolution\n");
        fprintf(fo, "        resolved_awdomain[%d] = resolve_domain(m%d_awaddr, m%d_awdomain);\n", i, i, i);
        fprintf(fo, "        \n");
        fprintf(fo, "        // Read address domain resolution\n");
        fprintf(fo, "        resolved_ardomain[%d] = resolve_domain(m%d_araddr, m%d_ardomain);\n", i, i, i);
        fprintf(fo, "    end\n\n");
        
        fprintf(fo, "    // Master %d domain violation detection\n", i);
        fprintf(fo, "    always @(*) begin\n");
        fprintf(fo, "        domain_violation[%d] = 1'b0;\n", i);
        fprintf(fo, "        \n");
        fprintf(fo, "        // Check write transaction violations\n");
        fprintf(fo, "        if (m%d_awvalid) begin\n", i);
        fprintf(fo, "            // Check if master is allowed in requested domain\n");
        fprintf(fo, "            if (!domain_membership_valid(%d, m%d_awdomain)) begin\n", i, i);
        fprintf(fo, "                domain_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            // Check snoop consistency with domain\n");
        fprintf(fo, "            if ((m%d_awdomain != DOMAIN_NON_SHAREABLE) && \n", i);
        fprintf(fo, "                (m%d_awsnoop == AWSNOOP_WRITE_NO_SNOOP)) begin\n", i);
        fprintf(fo, "                domain_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "        \n");
        fprintf(fo, "        // Check read transaction violations\n");
        fprintf(fo, "        if (m%d_arvalid) begin\n", i);
        fprintf(fo, "            // Check if master is allowed in requested domain\n");
        fprintf(fo, "            if (!domain_membership_valid(%d, m%d_ardomain)) begin\n", i, i);
        fprintf(fo, "                domain_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            // Check snoop consistency with domain\n");
        fprintf(fo, "            if ((m%d_ardomain != DOMAIN_NON_SHAREABLE) && \n", i);
        fprintf(fo, "                (m%d_arsnoop == ARSNOOP_READ_NO_SNOOP)) begin\n", i);
        fprintf(fo, "                domain_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "    end\n\n");
    }
    
    // Domain activity tracking
    fprintf(fo, "    // Domain activity and transaction counting\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    for (i = 0; i < 4; i++) { // NUM_DOMAINS is parameter, use fixed for loop
        fprintf(fo, "            domain_aw_count[%d] <= 8'h0;\n", i);
        fprintf(fo, "            domain_ar_count[%d] <= 8'h0;\n", i);
    }
    fprintf(fo, "        end else begin\n");
    
    // Count transactions per domain
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d transaction counting\n", i);
        fprintf(fo, "            if (m%d_awvalid && (resolved_awdomain[%d] != DOMAIN_NON_SHAREABLE)) begin\n", i, i);
        fprintf(fo, "                case (resolved_awdomain[%d])\n", i);
        fprintf(fo, "                    DOMAIN_INNER_SHAREABLE: domain_aw_count[1] <= domain_aw_count[1] + 1;\n");
        fprintf(fo, "                    DOMAIN_OUTER_SHAREABLE: domain_aw_count[2] <= domain_aw_count[2] + 1;\n");
        fprintf(fo, "                    DOMAIN_SYSTEM: domain_aw_count[3] <= domain_aw_count[3] + 1;\n");
        fprintf(fo, "                    default: ; // Non-shareable, no counting\n");
        fprintf(fo, "                endcase\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            if (m%d_arvalid && (resolved_ardomain[%d] != DOMAIN_NON_SHAREABLE)) begin\n", i, i);
        fprintf(fo, "                case (resolved_ardomain[%d])\n", i);
        fprintf(fo, "                    DOMAIN_INNER_SHAREABLE: domain_ar_count[1] <= domain_ar_count[1] + 1;\n");
        fprintf(fo, "                    DOMAIN_OUTER_SHAREABLE: domain_ar_count[2] <= domain_ar_count[2] + 1;\n");
        fprintf(fo, "                    DOMAIN_SYSTEM: domain_ar_count[3] <= domain_ar_count[3] + 1;\n");
        fprintf(fo, "                    default: ; // Non-shareable, no counting\n");
        fprintf(fo, "                endcase\n");
        fprintf(fo, "            end\n");
    }
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Domain activity outputs
    fprintf(fo, "    // Domain activity detection\n");
    fprintf(fo, "    wire [NUM_MASTER-1:0] master_aw_coherent;\n");
    fprintf(fo, "    wire [NUM_MASTER-1:0] master_ar_coherent;\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    assign master_aw_coherent[%d] = m%d_awvalid && (resolved_awdomain[%d] != DOMAIN_NON_SHAREABLE);\n", i, i, i);
        fprintf(fo, "    assign master_ar_coherent[%d] = m%d_arvalid && (resolved_ardomain[%d] != DOMAIN_NON_SHAREABLE);\n", i, i, i);
    }
    
    fprintf(fo, "    assign coherency_required = master_aw_coherent | master_ar_coherent;\n\n");
    
    // Generate domain activity per domain
    fprintf(fo, "    // Per-domain activity detection\n");
    for (i = 0; i < 4; i++) { // Fixed domains for now
        const char* domain_names[] = {"NON_SHAREABLE", "INNER_SHAREABLE", "OUTER_SHAREABLE", "SYSTEM"};
        fprintf(fo, "    wire domain_%d_aw_active = ", i);
        for (j = 0; j < numM; j++) {
            if (j > 0) fprintf(fo, " || ");
            fprintf(fo, "(master_aw_coherent[%d] && (resolved_awdomain[%d] == DOMAIN_%s))", j, j, domain_names[i]);
        }
        fprintf(fo, ";\n");
        
        fprintf(fo, "    wire domain_%d_ar_active = ", i);
        for (j = 0; j < numM; j++) {
            if (j > 0) fprintf(fo, " || ");
            fprintf(fo, "(master_ar_coherent[%d] && (resolved_ardomain[%d] == DOMAIN_%s))", j, j, domain_names[i]);
        }
        fprintf(fo, ";\n");
        
        fprintf(fo, "    assign domain_active[%d] = domain_%d_aw_active || domain_%d_ar_active;\n", i, i, i);
        fprintf(fo, "    assign domain_transaction_count[%d] = domain_aw_count[%d] + domain_ar_count[%d];\n\n", i, i, i);
    }
    
    // Domain hierarchy enforcement
    fprintf(fo, "    // Domain hierarchy enforcement\n");
    fprintf(fo, "    // Ensure proper domain nesting: System > Outer > Inner > Non-shareable\n");
    fprintf(fo, "    wire domain_hierarchy_violation = \n");
    fprintf(fo, "        // Inner shareable transactions should not bypass outer shareable domain\n");
    fprintf(fo, "        (domain_active[1] && domain_enable[2] && !domain_active[2]) ||\n");
    fprintf(fo, "        // Outer shareable transactions should not bypass system domain  \n");
    fprintf(fo, "        (domain_active[2] && domain_enable[3] && !domain_active[3]);\n\n");
    
    // Debug and monitoring outputs
    fprintf(fo, "    // Debug and monitoring\n");
    fprintf(fo, "    reg [15:0] total_coherent_transactions;\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            total_coherent_transactions <= 16'h0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            if (|coherency_required) begin\n");
    fprintf(fo, "                total_coherent_transactions <= total_coherent_transactions + 1;\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    fprintf(fo, "endmodule\n");
    
    return 0;
}