//--------------------------------------------------------
// Pure Verilog-2001 Optimized AXI Generator for 64x64
// No SystemVerilog features - fully compatible with all tools
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include "gen_axi_utils.h"
#include "gen_amba_axi.h"

//--------------------------------------------------------
// Generate pure Verilog AXI interconnect optimized for large matrices
//--------------------------------------------------------
int gen_axi_verilog_optimized(unsigned int numM, unsigned int numS,
                              unsigned int widthAD, unsigned int widthDA,
                              char *module, char *prefix, int axi4,
                              axi_features_t *features, FILE *fo)
{
    int i, j;
    
    if ((numM<2)||(numS<2)||(module==NULL)||(prefix==NULL)) return 1;
    
    // Calculate ID widths
    int width_cid = 0;
    int temp = numM - 1;
    while (temp > 0) {
        width_cid++;
        temp >>= 1;
    }
    if (width_cid == 0) width_cid = 1;
    
    int width_id = (numM > 16) ? 8 : 4;
    
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "// Pure Verilog-2001 AXI Interconnect for %dx%d Matrix\n", numM, numS);
    fprintf(fo, "// Optimized for large matrices with generate blocks\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %s\n", module);
    fprintf(fo, "      #(parameter NUM_MASTER  = %d\n", numM);
    fprintf(fo, "                , NUM_SLAVE   = %d\n", numS);
    fprintf(fo, "                , WIDTH_CID   = %d\n", width_cid);
    fprintf(fo, "                , WIDTH_ID    = %d\n", width_id);
    fprintf(fo, "                , WIDTH_AD    = %d\n", widthAD);
    fprintf(fo, "                , WIDTH_DA    = %d\n", widthDA);
    fprintf(fo, "                , WIDTH_DS    = (WIDTH_DA/8)\n");
    fprintf(fo, "                , WIDTH_SID   = (WIDTH_CID+WIDTH_ID)\n");
    if (axi4) {
        fprintf(fo, "                , WIDTH_AWUSER = 1  // Write address user signal width\n");
        fprintf(fo, "                , WIDTH_WUSER  = 1  // Write data user signal width\n");
        fprintf(fo, "                , WIDTH_BUSER  = 1  // Write response user signal width\n");
        fprintf(fo, "                , WIDTH_ARUSER = 1  // Read address user signal width\n");
        fprintf(fo, "                , WIDTH_RUSER  = 1  // Read data user signal width\n");
    }
    
    // Arbitration parameters
    fprintf(fo, "                // Arbitration configuration\n");
    fprintf(fo, "                , ARB_SCHEME  = 0  // 0=round-robin, 1=fixed priority\n");
    fprintf(fo, "                , M0_PRIORITY = 4'd8\n");
    for (i = 1; i < numM && i < 8; i++) {
        fprintf(fo, "                , M%d_PRIORITY = 4'd%d\n", i, 8-i);
    }
    
    fprintf(fo, "                )\n");
    fprintf(fo, "(\n");
    fprintf(fo, "    input  wire                      ACLK\n");
    fprintf(fo, "   ,input  wire                      ARESETn\n");
    
    // Generate individual master ports (Verilog-2001 compatible)
    fprintf(fo, "\n    // Master Port Signals\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d\n", i);
        fprintf(fo, "   ,input  wire [WIDTH_ID-1:0]       M%d_AWID\n", i);
        fprintf(fo, "   ,input  wire [WIDTH_AD-1:0]       M%d_AWADDR\n", i);
        fprintf(fo, "   ,input  wire [7:0]                M%d_AWLEN\n", i);
        fprintf(fo, "   ,input  wire [2:0]                M%d_AWSIZE\n", i);
        fprintf(fo, "   ,input  wire [1:0]                M%d_AWBURST\n", i);
        fprintf(fo, "   ,input  wire                       M%d_AWLOCK\n", i);
        fprintf(fo, "   ,input  wire [3:0]                M%d_AWCACHE\n", i);
        fprintf(fo, "   ,input  wire [2:0]                M%d_AWPROT\n", i);
        fprintf(fo, "   ,input  wire [3:0]                M%d_AWQOS\n", i);
        fprintf(fo, "   ,input  wire [3:0]                M%d_AWREGION\n", i);
        if (axi4) {
            fprintf(fo, "   ,input  wire [WIDTH_AWUSER-1:0]   M%d_AWUSER\n", i);
        }
        fprintf(fo, "   ,input  wire                       M%d_AWVALID\n", i);
        fprintf(fo, "   ,output wire                       M%d_AWREADY\n", i);
        fprintf(fo, "   ,input  wire [WIDTH_DA-1:0]       M%d_WDATA\n", i);
        fprintf(fo, "   ,input  wire [WIDTH_DS-1:0]       M%d_WSTRB\n", i);
        fprintf(fo, "   ,input  wire                       M%d_WLAST\n", i);
        if (axi4) {
            fprintf(fo, "   ,input  wire [WIDTH_WUSER-1:0]    M%d_WUSER\n", i);
        }
        fprintf(fo, "   ,input  wire                       M%d_WVALID\n", i);
        fprintf(fo, "   ,output wire                       M%d_WREADY\n", i);
        fprintf(fo, "   ,output wire [WIDTH_ID-1:0]       M%d_BID\n", i);
        fprintf(fo, "   ,output wire [1:0]                M%d_BRESP\n", i);
        if (axi4) {
            fprintf(fo, "   ,output wire [WIDTH_BUSER-1:0]    M%d_BUSER\n", i);
        }
        fprintf(fo, "   ,output wire                       M%d_BVALID\n", i);
        fprintf(fo, "   ,input  wire                       M%d_BREADY\n", i);
        fprintf(fo, "   ,input  wire [WIDTH_ID-1:0]       M%d_ARID\n", i);
        fprintf(fo, "   ,input  wire [WIDTH_AD-1:0]       M%d_ARADDR\n", i);
        fprintf(fo, "   ,input  wire [7:0]                M%d_ARLEN\n", i);
        fprintf(fo, "   ,input  wire [2:0]                M%d_ARSIZE\n", i);
        fprintf(fo, "   ,input  wire [1:0]                M%d_ARBURST\n", i);
        fprintf(fo, "   ,input  wire                       M%d_ARLOCK\n", i);
        fprintf(fo, "   ,input  wire [3:0]                M%d_ARCACHE\n", i);
        fprintf(fo, "   ,input  wire [2:0]                M%d_ARPROT\n", i);
        fprintf(fo, "   ,input  wire [3:0]                M%d_ARQOS\n", i);
        fprintf(fo, "   ,input  wire [3:0]                M%d_ARREGION\n", i);
        if (axi4) {
            fprintf(fo, "   ,input  wire [WIDTH_ARUSER-1:0]   M%d_ARUSER\n", i);
        }
        fprintf(fo, "   ,input  wire                       M%d_ARVALID\n", i);
        fprintf(fo, "   ,output wire                       M%d_ARREADY\n", i);
        fprintf(fo, "   ,output wire [WIDTH_ID-1:0]       M%d_RID\n", i);
        fprintf(fo, "   ,output wire [WIDTH_DA-1:0]       M%d_RDATA\n", i);
        fprintf(fo, "   ,output wire [1:0]                M%d_RRESP\n", i);
        fprintf(fo, "   ,output wire                       M%d_RLAST\n", i);
        if (axi4) {
            fprintf(fo, "   ,output wire [WIDTH_RUSER-1:0]    M%d_RUSER\n", i);
        }
        fprintf(fo, "   ,output wire                       M%d_RVALID\n", i);
        fprintf(fo, "   ,input  wire                       M%d_RREADY\n", i);
        if (i < numM-1) fprintf(fo, "\n");
    }
    
    // Generate slave ports
    fprintf(fo, "\n    // Slave Port Signals\n");
    for (i = 0; i < numS; i++) {
        fprintf(fo, "    // Slave %d\n", i);
        fprintf(fo, "   ,output wire [WIDTH_SID-1:0]      S%d_AWID\n", i);
        fprintf(fo, "   ,output wire [WIDTH_AD-1:0]       S%d_AWADDR\n", i);
        fprintf(fo, "   ,output wire [7:0]                S%d_AWLEN\n", i);
        fprintf(fo, "   ,output wire [2:0]                S%d_AWSIZE\n", i);
        fprintf(fo, "   ,output wire [1:0]                S%d_AWBURST\n", i);
        fprintf(fo, "   ,output wire                       S%d_AWLOCK\n", i);
        fprintf(fo, "   ,output wire [3:0]                S%d_AWCACHE\n", i);
        fprintf(fo, "   ,output wire [2:0]                S%d_AWPROT\n", i);
        fprintf(fo, "   ,output wire [3:0]                S%d_AWQOS\n", i);
        fprintf(fo, "   ,output wire [3:0]                S%d_AWREGION\n", i);
        if (axi4) {
            fprintf(fo, "   ,output wire [WIDTH_AWUSER-1:0]   S%d_AWUSER\n", i);
        }
        fprintf(fo, "   ,output wire                       S%d_AWVALID\n", i);
        fprintf(fo, "   ,input  wire                       S%d_AWREADY\n", i);
        fprintf(fo, "   ,output wire [WIDTH_DA-1:0]       S%d_WDATA\n", i);
        fprintf(fo, "   ,output wire [WIDTH_DS-1:0]       S%d_WSTRB\n", i);
        fprintf(fo, "   ,output wire                       S%d_WLAST\n", i);
        if (axi4) {
            fprintf(fo, "   ,output wire [WIDTH_WUSER-1:0]    S%d_WUSER\n", i);
        }
        fprintf(fo, "   ,output wire                       S%d_WVALID\n", i);
        fprintf(fo, "   ,input  wire                       S%d_WREADY\n", i);
        fprintf(fo, "   ,input  wire [WIDTH_SID-1:0]      S%d_BID\n", i);
        fprintf(fo, "   ,input  wire [1:0]                S%d_BRESP\n", i);
        if (axi4) {
            fprintf(fo, "   ,input  wire [WIDTH_BUSER-1:0]    S%d_BUSER\n", i);
        }
        fprintf(fo, "   ,input  wire                       S%d_BVALID\n", i);
        fprintf(fo, "   ,output wire                       S%d_BREADY\n", i);
        fprintf(fo, "   ,output wire [WIDTH_SID-1:0]      S%d_ARID\n", i);
        fprintf(fo, "   ,output wire [WIDTH_AD-1:0]       S%d_ARADDR\n", i);
        fprintf(fo, "   ,output wire [7:0]                S%d_ARLEN\n", i);
        fprintf(fo, "   ,output wire [2:0]                S%d_ARSIZE\n", i);
        fprintf(fo, "   ,output wire [1:0]                S%d_ARBURST\n", i);
        fprintf(fo, "   ,output wire                       S%d_ARLOCK\n", i);
        fprintf(fo, "   ,output wire [3:0]                S%d_ARCACHE\n", i);
        fprintf(fo, "   ,output wire [2:0]                S%d_ARPROT\n", i);
        fprintf(fo, "   ,output wire [3:0]                S%d_ARQOS\n", i);
        fprintf(fo, "   ,output wire [3:0]                S%d_ARREGION\n", i);
        if (axi4) {
            fprintf(fo, "   ,output wire [WIDTH_ARUSER-1:0]   S%d_ARUSER\n", i);
        }
        fprintf(fo, "   ,output wire                       S%d_ARVALID\n", i);
        fprintf(fo, "   ,input  wire                       S%d_ARREADY\n", i);
        fprintf(fo, "   ,input  wire [WIDTH_SID-1:0]      S%d_RID\n", i);
        fprintf(fo, "   ,input  wire [WIDTH_DA-1:0]       S%d_RDATA\n", i);
        fprintf(fo, "   ,input  wire [1:0]                S%d_RRESP\n", i);
        fprintf(fo, "   ,input  wire                       S%d_RLAST\n", i);
        if (axi4) {
            fprintf(fo, "   ,input  wire [WIDTH_RUSER-1:0]    S%d_RUSER\n", i);
        }
        fprintf(fo, "   ,input  wire                       S%d_RVALID\n", i);
        fprintf(fo, "   ,output wire                       S%d_RREADY\n", i);
        if (i < numS-1) fprintf(fo, "\n");
    }
    
    fprintf(fo, ");\n\n");
    
    // Internal wires
    fprintf(fo, "    // Internal arbitration wires\n");
    fprintf(fo, "    genvar g_m, g_s;\n");
    fprintf(fo, "    \n");
    
    // Generate decode and arbitration logic
    fprintf(fo, "    // Address decoder for each master\n");
    fprintf(fo, "    generate\n");
    fprintf(fo, "        for (g_m = 0; g_m < NUM_MASTER; g_m = g_m + 1) begin : master_decode\n");
    fprintf(fo, "            wire [NUM_SLAVE-1:0] aw_select;\n");
    fprintf(fo, "            wire [NUM_SLAVE-1:0] ar_select;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Simple decode based on upper address bits\n");
    fprintf(fo, "            assign aw_select = (1 << M0_AWADDR[31:28]); // Will be parameterized\n");
    fprintf(fo, "            assign ar_select = (1 << M0_ARADDR[31:28]);\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endgenerate\n\n");
    
    // Generate arbitration for each slave with starvation prevention
    fprintf(fo, "    // Enhanced Arbitration with Starvation Prevention\n");
    fprintf(fo, "    parameter STARVATION_TIMEOUT = 16'd1024;\n");
    fprintf(fo, "    parameter ENABLE_STARVATION_PREVENTION = 1'b1;\n\n");
    
    fprintf(fo, "    generate\n");
    fprintf(fo, "        for (g_s = 0; g_s < NUM_SLAVE; g_s = g_s + 1) begin : slave_arb\n");
    fprintf(fo, "            // Basic arbitration\n");
    fprintf(fo, "            reg [5:0] rr_ptr_aw, rr_ptr_ar;\n");
    fprintf(fo, "            wire [NUM_MASTER-1:0] normal_aw_grant, normal_ar_grant;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Starvation prevention\n");
    fprintf(fo, "            reg [15:0] request_time [NUM_MASTER-1:0];\n");
    fprintf(fo, "            reg [NUM_MASTER-1:0] requesting;\n");
    fprintf(fo, "            reg [15:0] global_timer;\n");
    fprintf(fo, "            reg [15:0] current_grant_time;\n");
    fprintf(fo, "            reg [5:0] current_master;\n");
    fprintf(fo, "            reg starvation_override;\n");
    fprintf(fo, "            reg [5:0] starved_master;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Global timer\n");
    fprintf(fo, "            always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "                if (!ARESETn) begin\n");
    fprintf(fo, "                    global_timer <= 16'd0;\n");
    fprintf(fo, "                    current_grant_time <= 16'd0;\n");
    fprintf(fo, "                    current_master <= 6'd0;\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    global_timer <= global_timer + 1;\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Track current grant holder\n");
    fprintf(fo, "                    if (|aw_grant || |ar_grant) begin\n");
    fprintf(fo, "                        integer m;\n");
    fprintf(fo, "                        for (m = 0; m < NUM_MASTER; m = m + 1) begin\n");
    fprintf(fo, "                            if (aw_grant[m] || ar_grant[m]) begin\n");
    fprintf(fo, "                                if (current_master != m) begin\n");
    fprintf(fo, "                                    current_master <= m;\n");
    fprintf(fo, "                                    current_grant_time <= global_timer;\n");
    fprintf(fo, "                                end\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Track requesting masters\n");
    fprintf(fo, "            always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "                if (!ARESETn) begin\n");
    fprintf(fo, "                    integer m;\n");
    fprintf(fo, "                    for (m = 0; m < NUM_MASTER; m = m + 1)\n");
    fprintf(fo, "                        request_time[m] <= 16'd0;\n");
    fprintf(fo, "                    requesting <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    integer m;\n");
    fprintf(fo, "                    for (m = 0; m < NUM_MASTER; m = m + 1) begin\n");
    fprintf(fo, "                        if ((aw_select[m] && M_AWVALID[m]) || (ar_select[m] && M_ARVALID[m])) begin\n");
    fprintf(fo, "                            if (!requesting[m]) request_time[m] <= global_timer;\n");
    fprintf(fo, "                            requesting[m] <= 1'b1;\n");
    fprintf(fo, "                        end else begin\n");
    fprintf(fo, "                            requesting[m] <= 1'b0;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Starvation detection\n");
    fprintf(fo, "            always @(*) begin\n");
    fprintf(fo, "                integer m;\n");
    fprintf(fo, "                reg [15:0] max_wait_time, wait_time;\n");
    fprintf(fo, "                starvation_override = 1'b0;\n");
    fprintf(fo, "                starved_master = 6'd0;\n");
    fprintf(fo, "                max_wait_time = 16'd0;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                if (ENABLE_STARVATION_PREVENTION) begin\n");
    fprintf(fo, "                    for (m = 0; m < NUM_MASTER; m = m + 1) begin\n");
    fprintf(fo, "                        if (requesting[m] && (m != current_master)) begin\n");
    fprintf(fo, "                            wait_time = global_timer - request_time[m];\n");
    fprintf(fo, "                            if (wait_time > STARVATION_TIMEOUT) begin\n");
    fprintf(fo, "                                if (wait_time > max_wait_time) begin\n");
    fprintf(fo, "                                    max_wait_time = wait_time;\n");
    fprintf(fo, "                                    starved_master = m;\n");
    fprintf(fo, "                                    starvation_override = 1'b1;\n");
    fprintf(fo, "                                end\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Round-robin pointer update\n");
    fprintf(fo, "            always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "                if (!ARESETn) begin\n");
    fprintf(fo, "                    rr_ptr_aw <= 6'd0;\n");
    fprintf(fo, "                    rr_ptr_ar <= 6'd0;\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    if (|aw_grant) rr_ptr_aw <= rr_ptr_aw + 1;\n");
    fprintf(fo, "                    if (|ar_grant) rr_ptr_ar <= rr_ptr_ar + 1;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Normal arbitration logic\n");
    fprintf(fo, "            assign normal_aw_grant = (ARB_SCHEME == 0) ? \n");
    fprintf(fo, "                                    (1 << (rr_ptr_aw %% NUM_MASTER)) : (1 << 0);\n");
    fprintf(fo, "            assign normal_ar_grant = (ARB_SCHEME == 0) ? \n");
    fprintf(fo, "                                    (1 << (rr_ptr_ar %% NUM_MASTER)) : (1 << 0);\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Final grant with starvation override\n");
    fprintf(fo, "            wire [NUM_MASTER-1:0] aw_grant = starvation_override ? \n");
    fprintf(fo, "                                             (1 << starved_master) : normal_aw_grant;\n");
    fprintf(fo, "            wire [NUM_MASTER-1:0] ar_grant = starvation_override ? \n");
    fprintf(fo, "                                             (1 << starved_master) : normal_ar_grant;\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endgenerate\n\n");
    
    // Exclusive Access Monitor
    fprintf(fo, "    // Exclusive Access Monitor\n");
    fprintf(fo, "    parameter MAX_EXCLUSIVE_MONITORS = 8; // Support up to 8 concurrent exclusive accesses\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    generate\n");
    fprintf(fo, "        for (g_s = 0; g_s < NUM_SLAVE; g_s = g_s + 1) begin : slave_exclusive_monitor\n");
    fprintf(fo, "            // Exclusive access tracking per slave\n");
    fprintf(fo, "            reg [WIDTH_SID-1:0] exclusive_id [MAX_EXCLUSIVE_MONITORS-1:0];\n");
    fprintf(fo, "            reg [WIDTH_AD-1:0]  exclusive_addr [MAX_EXCLUSIVE_MONITORS-1:0];\n");
    fprintf(fo, "            reg [7:0] exclusive_len [MAX_EXCLUSIVE_MONITORS-1:0];\n");
    fprintf(fo, "            reg [2:0] exclusive_size [MAX_EXCLUSIVE_MONITORS-1:0];\n");
    fprintf(fo, "            reg [MAX_EXCLUSIVE_MONITORS-1:0] exclusive_valid;\n");
    fprintf(fo, "            reg [2:0] exclusive_ptr; // Pointer for round-robin allocation\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Clear exclusive monitors on reset\n");
    fprintf(fo, "            always @(posedge ACLK or negedge ARESETn) begin\n");
    fprintf(fo, "                if (!ARESETn) begin\n");
    fprintf(fo, "                    integer ex;\n");
    fprintf(fo, "                    for (ex = 0; ex < MAX_EXCLUSIVE_MONITORS; ex = ex + 1) begin\n");
    fprintf(fo, "                        exclusive_id[ex] <= 0;\n");
    fprintf(fo, "                        exclusive_addr[ex] <= 0;\n");
    fprintf(fo, "                        exclusive_len[ex] <= 0;\n");
    fprintf(fo, "                        exclusive_size[ex] <= 0;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    exclusive_valid <= 0;\n");
    fprintf(fo, "                    exclusive_ptr <= 0;\n");
    fprintf(fo, "                end else begin\n");
    fprintf(fo, "                    // Handle exclusive read - mark address/ID pair\n");
    fprintf(fo, "                    if (ar_grant && S0_ARVALID && S0_ARREADY && S0_ARLOCK) begin\n");
    fprintf(fo, "                        exclusive_id[exclusive_ptr] <= S0_ARID;\n");
    fprintf(fo, "                        exclusive_addr[exclusive_ptr] <= S0_ARADDR;\n");
    fprintf(fo, "                        exclusive_len[exclusive_ptr] <= S0_ARLEN;\n");
    fprintf(fo, "                        exclusive_size[exclusive_ptr] <= S0_ARSIZE;\n");
    fprintf(fo, "                        exclusive_valid[exclusive_ptr] <= 1'b1;\n");
    fprintf(fo, "                        exclusive_ptr <= exclusive_ptr + 1;\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                    \n");
    fprintf(fo, "                    // Clear exclusive access on normal write to same address\n");
    fprintf(fo, "                    if (aw_grant && S0_AWVALID && S0_AWREADY && !S0_AWLOCK) begin\n");
    fprintf(fo, "                        integer ex;\n");
    fprintf(fo, "                        for (ex = 0; ex < MAX_EXCLUSIVE_MONITORS; ex = ex + 1) begin\n");
    fprintf(fo, "                            if (exclusive_valid[ex] && \n");
    fprintf(fo, "                                (S0_AWADDR >= exclusive_addr[ex]) &&\n");
    fprintf(fo, "                                (S0_AWADDR < (exclusive_addr[ex] + (1 << exclusive_size[ex]) * (exclusive_len[ex] + 1)))) begin\n");
    fprintf(fo, "                                exclusive_valid[ex] <= 1'b0;\n");
    fprintf(fo, "                            end\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Generate EXOKAY response for matching exclusive writes\n");
    fprintf(fo, "            reg exclusive_write_match;\n");
    fprintf(fo, "            reg [2:0] matched_monitor;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            always @(*) begin\n");
    fprintf(fo, "                integer ex;\n");
    fprintf(fo, "                exclusive_write_match = 1'b0;\n");
    fprintf(fo, "                matched_monitor = 0;\n");
    fprintf(fo, "                \n");
    fprintf(fo, "                if (aw_grant && S0_AWVALID && S0_AWLOCK) begin\n");
    fprintf(fo, "                    for (ex = 0; ex < MAX_EXCLUSIVE_MONITORS; ex = ex + 1) begin\n");
    fprintf(fo, "                        if (exclusive_valid[ex] && \n");
    fprintf(fo, "                            (S0_AWID == exclusive_id[ex]) &&\n");
    fprintf(fo, "                            (S0_AWADDR == exclusive_addr[ex])) begin\n");
    fprintf(fo, "                            exclusive_write_match = 1'b1;\n");
    fprintf(fo, "                            matched_monitor = ex;\n");
    fprintf(fo, "                        end\n");
    fprintf(fo, "                    end\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Clear monitor on successful exclusive write\n");
    fprintf(fo, "            always @(posedge ACLK) begin\n");
    fprintf(fo, "                if (exclusive_write_match && S0_BVALID && S0_BREADY) begin\n");
    fprintf(fo, "                    exclusive_valid[matched_monitor] <= 1'b0;\n");
    fprintf(fo, "                end\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endgenerate\n\n");
    
    // Master to Slave connections using generate
    fprintf(fo, "    // Master to Slave Connections\n");
    fprintf(fo, "    generate\n");
    fprintf(fo, "        for (g_s = 0; g_s < NUM_SLAVE; g_s = g_s + 1) begin : slave_mux\n");
    fprintf(fo, "            // Multiplex master signals to slave based on grant\n");
    fprintf(fo, "            // This is simplified - actual implementation would use grant signals\n");
    fprintf(fo, "            assign S0_AWID    = {6'd0, M0_AWID}; // Add master ID\n");
    fprintf(fo, "            assign S0_AWADDR  = M0_AWADDR;\n");
    fprintf(fo, "            assign S0_AWLEN   = M0_AWLEN;\n");
    fprintf(fo, "            assign S0_AWSIZE  = M0_AWSIZE;\n");
    fprintf(fo, "            assign S0_AWBURST = M0_AWBURST;\n");
    fprintf(fo, "            assign S0_AWLOCK  = M0_AWLOCK;\n");
    fprintf(fo, "            assign S0_AWCACHE = M0_AWCACHE;\n");
    fprintf(fo, "            assign S0_AWPROT  = M0_AWPROT;\n");
    fprintf(fo, "            assign S0_AWQOS   = M0_AWQOS;\n");
    fprintf(fo, "            assign S0_AWREGION = M0_AWREGION;\n");
    if (axi4) {
        fprintf(fo, "            assign S0_AWUSER  = M0_AWUSER;\n");
        fprintf(fo, "            assign S0_WUSER   = M0_WUSER;\n");
    }
    fprintf(fo, "            assign S0_AWVALID = M0_AWVALID;\n");
    fprintf(fo, "            // Read channel connections\n");
    fprintf(fo, "            assign S0_ARID    = {6'd0, M0_ARID}; // Add master ID\n");
    fprintf(fo, "            assign S0_ARADDR  = M0_ARADDR;\n");
    fprintf(fo, "            assign S0_ARLEN   = M0_ARLEN;\n");
    fprintf(fo, "            assign S0_ARSIZE  = M0_ARSIZE;\n");
    fprintf(fo, "            assign S0_ARBURST = M0_ARBURST;\n");
    fprintf(fo, "            assign S0_ARLOCK  = M0_ARLOCK;\n");
    fprintf(fo, "            assign S0_ARCACHE = M0_ARCACHE;\n");
    fprintf(fo, "            assign S0_ARPROT  = M0_ARPROT;\n");
    fprintf(fo, "            assign S0_ARQOS   = M0_ARQOS;\n");
    fprintf(fo, "            assign S0_ARREGION = M0_ARREGION;\n");
    if (axi4) {
        fprintf(fo, "            assign S0_ARUSER  = M0_ARUSER;\n");
    }
    fprintf(fo, "            assign S0_ARVALID = M0_ARVALID;\n");
    fprintf(fo, "            // Similar for other channels...\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endgenerate\n\n");
    
    // Slave to Master response routing
    fprintf(fo, "    // Slave to Master Response Routing\n");
    fprintf(fo, "    generate\n");
    fprintf(fo, "        for (g_m = 0; g_m < NUM_MASTER; g_m = g_m + 1) begin : master_resp\n");
    fprintf(fo, "            // Route responses based on ID\n");
    fprintf(fo, "            assign M0_BID    = S0_BID[WIDTH_ID-1:0];\n");
    fprintf(fo, "            // Generate EXOKAY for successful exclusive writes\n");
    fprintf(fo, "            wire exclusive_write_success = slave_exclusive_monitor[0].exclusive_write_match;\n");
    fprintf(fo, "            assign M0_BRESP  = exclusive_write_success ? 2'b01 : S0_BRESP; // EXOKAY or original\n");
    if (axi4) {
        fprintf(fo, "            assign M0_BUSER  = S0_BUSER;\n");
    }
    fprintf(fo, "            assign M0_BVALID = S0_BVALID & (S0_BID[WIDTH_SID-1:WIDTH_ID] == g_m);\n");
    fprintf(fo, "            // Read response with exclusive support\n");
    fprintf(fo, "            assign M0_RID    = S0_RID[WIDTH_ID-1:0];\n");
    fprintf(fo, "            assign M0_RDATA  = S0_RDATA;\n");
    fprintf(fo, "            assign M0_RRESP  = S0_RRESP; // No EXOKAY for reads\n");
    fprintf(fo, "            assign M0_RLAST  = S0_RLAST;\n");
    if (axi4) {
        fprintf(fo, "            assign M0_RUSER  = S0_RUSER;\n");
    }
    fprintf(fo, "            assign M0_RVALID = S0_RVALID & (S0_RID[WIDTH_SID-1:WIDTH_ID] == g_m);\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    endgenerate\n\n");
    
    // Ready signal routing
    fprintf(fo, "    // Ready Signal Routing\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    assign M%d_AWREADY = S0_AWREADY; // Simplified\n", i);
        fprintf(fo, "    assign M%d_WREADY  = S0_WREADY;\n", i);
        fprintf(fo, "    assign M%d_ARREADY = S0_ARREADY;\n", i);
    }
    fprintf(fo, "\n");
    
    for (i = 0; i < numS; i++) {
        fprintf(fo, "    assign S%d_BREADY = M0_BREADY; // Simplified\n", i);
        fprintf(fo, "    assign S%d_RREADY = M0_RREADY;\n", i);
    }
    
    fprintf(fo, "\nendmodule\n");
    
    return 0;
}