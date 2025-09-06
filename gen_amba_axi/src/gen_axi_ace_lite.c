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
    fprintf(fo, "// ACE-Lite Coherency Extension Module\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %saxi_ace_lite\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32\n");
    fprintf(fo, "              , WIDTH_SD_AWUSER = %d\n", features->width_sd_awuser);
    fprintf(fo, "              , WIDTH_SD_WUSER  = %d\n", features->width_sd_wuser);
    fprintf(fo, "              , WIDTH_SD_BUSER  = %d\n", features->width_sd_buser);
    fprintf(fo, "              , WIDTH_SD_ARUSER = %d\n", features->width_sd_aruser);
    fprintf(fo, "              , WIDTH_SD_RUSER  = %d)\n", features->width_sd_ruser);
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                    clk\n");
    fprintf(fo, "    , input  wire                    rst_n\n");
    
    // Add master interface connections
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d interface\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]    m%d_awid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]    m%d_awaddr\n", i);
        fprintf(fo, "    , input  wire [1:0]             m%d_awdomain\n", i);
        fprintf(fo, "    , input  wire [2:0]             m%d_awsnoop\n", i);
        fprintf(fo, "    , input  wire [1:0]             m%d_awbar\n", i);
        fprintf(fo, "    , input  wire [WIDTH_SD_AWUSER-1:0] m%d_sd_awuser\n", i);
        fprintf(fo, "    , input  wire                   m%d_awvalid\n", i);
        fprintf(fo, "    , input  wire                   m%d_awready\n", i);
        fprintf(fo, "    , input  wire [WIDTH_SD_WUSER-1:0]  m%d_sd_wuser\n", i);
        fprintf(fo, "    , input  wire [WIDTH_ID-1:0]    m%d_arid\n", i);
        fprintf(fo, "    , input  wire [WIDTH_AD-1:0]    m%d_araddr\n", i);
        fprintf(fo, "    , input  wire [1:0]             m%d_ardomain\n", i);
        fprintf(fo, "    , input  wire [3:0]             m%d_arsnoop\n", i);
        fprintf(fo, "    , input  wire [1:0]             m%d_arbar\n", i);
        fprintf(fo, "    , input  wire [WIDTH_SD_ARUSER-1:0] m%d_sd_aruser\n", i);
        fprintf(fo, "    , input  wire                   m%d_arvalid\n", i);
        fprintf(fo, "    , input  wire                   m%d_arready\n", i);
        fprintf(fo, "    , input  wire [WIDTH_SD_BUSER-1:0]  m%d_sd_buser\n", i);
        fprintf(fo, "    , input  wire                   m%d_bvalid\n", i);
        fprintf(fo, "    , input  wire                   m%d_bready\n", i);
        fprintf(fo, "    , input  wire [WIDTH_SD_RUSER-1:0]  m%d_sd_ruser\n", i);
        fprintf(fo, "    , input  wire                   m%d_rlast\n", i);
        fprintf(fo, "    , input  wire                   m%d_rvalid\n", i);
        fprintf(fo, "    , input  wire                   m%d_rready\n", i);
    }
    
    // Add coherency channels for ACE-Lite snoop protocol
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    // Master %d Coherency Channels\n", i);
        
        // Snoop Address Channel (Interconnect -> Master)
        fprintf(fo, "    , output wire [WIDTH_AD-1:0]    m%d_acaddr     // Snoop address\n", i);
        fprintf(fo, "    , output wire [2:0]             m%d_acsnoop    // Snoop transaction type\n", i);
        fprintf(fo, "    , output wire [2:0]             m%d_acprot     // Snoop protection type\n", i);
        fprintf(fo, "    , output wire                   m%d_acvalid    // Snoop address valid\n", i);
        fprintf(fo, "    , input  wire                   m%d_acready    // Snoop address ready\n", i);
        
        // Coherency Response Channel (Master -> Interconnect) 
        fprintf(fo, "    , input  wire [4:0]             m%d_crresp     // Snoop response\n", i);
        fprintf(fo, "    , input  wire                   m%d_crvalid    // Snoop response valid\n", i);
        fprintf(fo, "    , output wire                   m%d_crready    // Snoop response ready\n", i);
        
        // Coherency Data Channel (Master -> Interconnect)
        fprintf(fo, "    , input  wire [WIDTH_DA-1:0]    m%d_cddata     // Snoop data\n", i);
        fprintf(fo, "    , input  wire [WIDTH_DA/8-1:0]  m%d_cdstrb     // Snoop data strobe\n", i);
        fprintf(fo, "    , input  wire                   m%d_cdlast     // Snoop data last\n", i);
        fprintf(fo, "    , input  wire                   m%d_cdvalid    // Snoop data valid\n", i);
        fprintf(fo, "    , output wire                   m%d_cdready    // Snoop data ready\n", i);
        fprintf(fo, "\n");
    }
    
    // Add coherency monitoring outputs
    fprintf(fo, "    // Coherency monitoring outputs\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]  coherency_violation\n");
    fprintf(fo, "    , output reg                    snoop_required\n");
    fprintf(fo, "    , output reg                    barrier_active\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // ACE-Lite transaction validation error outputs\n");
    fprintf(fo, "    , output wire                   transaction_error      // Aggregate error flag\n");
    fprintf(fo, "    , output reg                    ace_lite_txn_error     // ACE-Lite specific errors\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0] invalid_write_txn      // Per-master write errors\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0] invalid_read_txn       // Per-master read errors\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0] unsupported_cache_maint // Unsupported cache maintenance\n");
    
    fprintf(fo, ");\n\n");
    
    // Generate parameter definitions inside module
    fprintf(fo, "    // ACE-Lite parameters\n");
    fprintf(fo, "    localparam WIDTH_DOMAIN = %d;  // Shareability domain\n", features->width_domain);
    fprintf(fo, "    localparam WIDTH_SNOOP_AW = %d; // Write snoop type\n", features->width_snoop_aw);
    fprintf(fo, "    localparam WIDTH_SNOOP_AR = %d; // Read snoop type\n", features->width_snoop_ar);
    fprintf(fo, "    localparam WIDTH_BAR = %d;     // Barrier type\n\n", features->width_bar);
    
    // Add SD_USER signal bit field definitions
    fprintf(fo, "    // SD_USER signal bit field definitions\n");
    fprintf(fo, "    // SD_AWUSER bit fields (coherency attributes for write address)\n");
    fprintf(fo, "    localparam SD_AWUSER_CACHE_ALLOC  = 0;  // Cache allocation hint\n");
    fprintf(fo, "    localparam SD_AWUSER_CACHE_POLICY = 1;  // Cache policy hint\n");
    fprintf(fo, "    localparam SD_AWUSER_QOS_START    = 2;  // QoS field start\n");
    fprintf(fo, "    localparam SD_AWUSER_QOS_WIDTH    = 4;  // QoS field width\n");
    fprintf(fo, "    localparam SD_AWUSER_SECURE       = 6;  // Security attribute\n");
    fprintf(fo, "    localparam SD_AWUSER_PRIV         = 7;  // Privilege level\n\n");
    
    fprintf(fo, "    // SD_ARUSER bit fields (coherency attributes for read address)\n");
    fprintf(fo, "    localparam SD_ARUSER_CACHE_ALLOC  = 0;  // Cache allocation hint\n");
    fprintf(fo, "    localparam SD_ARUSER_CACHE_POLICY = 1;  // Cache policy hint\n");
    fprintf(fo, "    localparam SD_ARUSER_QOS_START    = 2;  // QoS field start\n");
    fprintf(fo, "    localparam SD_ARUSER_QOS_WIDTH    = 4;  // QoS field width\n");
    fprintf(fo, "    localparam SD_ARUSER_SECURE       = 6;  // Security attribute\n");
    fprintf(fo, "    localparam SD_ARUSER_PRIV         = 7;  // Privilege level\n\n");
    
    fprintf(fo, "    // SD_WUSER bit fields (coherency attributes for write data)\n");
    fprintf(fo, "    localparam SD_WUSER_DIRTY_BIT     = 0;  // Cache line dirty indicator\n");
    fprintf(fo, "    localparam SD_WUSER_SHARED_BIT    = 1;  // Shared cache line indicator\n");
    fprintf(fo, "    localparam SD_WUSER_ERROR_BIT     = 2;  // Error injection for testing\n\n");
    
    fprintf(fo, "    // SD_BUSER/SD_RUSER bit fields (response coherency attributes)\n");
    fprintf(fo, "    localparam SD_RESP_CACHE_STATE    = 0;  // Cache state after operation\n");
    fprintf(fo, "    localparam SD_RESP_SHARED_DIRTY   = 2;  // Shared dirty indication\n");
    fprintf(fo, "    localparam SD_RESP_ERROR_INJECT   = 3;  // Error injection response\n\n");
    
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
    
    // Coherency Channel Protocol Definitions
    fprintf(fo, "    // Coherency snoop transaction encodings (ACSNOOP)\n");
    fprintf(fo, "    localparam [2:0] ACSNOOP_READ_ONCE        = 3'b000;\n");
    fprintf(fo, "    localparam [2:0] ACSNOOP_READ_SHARED      = 3'b001;\n");
    fprintf(fo, "    localparam [2:0] ACSNOOP_READ_CLEAN       = 3'b010;\n");
    fprintf(fo, "    localparam [2:0] ACSNOOP_READ_NOT_SHARED_DIRTY = 3'b011;\n");
    fprintf(fo, "    localparam [2:0] ACSNOOP_READ_UNIQUE      = 3'b111;\n");
    fprintf(fo, "    localparam [2:0] ACSNOOP_CLEAN_INVALID    = 3'b100;\n");
    fprintf(fo, "    localparam [2:0] ACSNOOP_MAKE_INVALID     = 3'b101;\n\n");
    
    fprintf(fo, "    // Coherency response encodings (CRRESP)\n");
    fprintf(fo, "    localparam [4:0] CRRESP_DATATRANSFER      = 5'b00000;\n");  
    fprintf(fo, "    localparam [4:0] CRRESP_ERROR             = 5'b00001;\n");
    fprintf(fo, "    localparam [4:0] CRRESP_OK_WAS_UNIQUE     = 5'b00010;\n");
    fprintf(fo, "    localparam [4:0] CRRESP_OK_SHARED_CLEAN   = 5'b00100;\n");
    fprintf(fo, "    localparam [4:0] CRRESP_OK_SHARED_DIRTY   = 5'b01000;\n");
    fprintf(fo, "    localparam [4:0] CRRESP_OK_PASS_DIRTY     = 5'b10000;\n\n");
    
    // Coherency channel state tracking
    fprintf(fo, "    // Coherency channel state registers\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] snoop_pending;        // Snoop requests pending per master\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] snoop_response_ready; // Response ready per master\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] snoop_data_pending;   // Data response pending per master\n");
    fprintf(fo, "    \n");
    
    // Generate coherency checking logic
    fprintf(fo, "    // Coherency checking logic\n");
    fprintf(fo, "    // This ensures coherent transactions are handled correctly\n");
    fprintf(fo, "    reg coherency_error;\n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        coherency_error = 1'b0;\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        // Check Master %d coherency\n", i);
        fprintf(fo, "        if (m%d_awvalid && m%d_awdomain != DOMAIN_NON_SHAREABLE) begin\n", i, i);
        fprintf(fo, "            // Coherent write transaction\n");
        fprintf(fo, "            if (m%d_awsnoop == AWSNOOP_WRITE_NO_SNOOP) begin\n", i);
        fprintf(fo, "                // Error: Shareable domain but no snoop\n");
        fprintf(fo, "                coherency_error = 1'b1;\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
    }
    
    fprintf(fo, "    end\n\n");
    
    // Coherency Channel Management Logic
    fprintf(fo, "    // Coherency Channel State Management\n");
    fprintf(fo, "    // Tracks snoop requests and responses for each master\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            snoop_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            snoop_response_ready <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            snoop_data_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "        end else begin\n");
    
    // Generate per-master snoop logic
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d snoop channel state tracking\n", i);
        fprintf(fo, "            if (m%d_acvalid && m%d_acready) begin\n", i, i);
        fprintf(fo, "                snoop_pending[%d] <= 1'b1;    // Snoop request started\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            if (m%d_crvalid && m%d_crready) begin\n", i, i);
        fprintf(fo, "                snoop_response_ready[%d] <= 1'b1; // Response received\n", i);
        fprintf(fo, "                if (m%d_crresp[0]) begin  // Check if data transfer required\n", i);
        fprintf(fo, "                    snoop_data_pending[%d] <= 1'b1;\n", i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            if (m%d_cdvalid && m%d_cdready && m%d_cdlast) begin\n", i, i, i);
        fprintf(fo, "                snoop_data_pending[%d] <= 1'b0;  // Data transfer complete\n", i);
        fprintf(fo, "                snoop_pending[%d] <= 1'b0;       // Complete snoop transaction\n", i);
        fprintf(fo, "                snoop_response_ready[%d] <= 1'b0;\n", i);
        fprintf(fo, "            end else if (m%d_crvalid && m%d_crready && !m%d_crresp[0]) begin\n", i, i, i);
        fprintf(fo, "                // No data required, complete immediately\n");
        fprintf(fo, "                snoop_pending[%d] <= 1'b0;\n", i);
        fprintf(fo, "                snoop_response_ready[%d] <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
    }
    
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Coherency handshake timeout detection
    fprintf(fo, "    // Coherency Channel Timeout Detection\n");
    fprintf(fo, "    reg [15:0] snoop_timeout_counter [NUM_MASTER-1:0];\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] snoop_timeout_error;\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            snoop_timeout_counter[%d] <= 16'h0000;\n", i);
    }
    fprintf(fo, "            snoop_timeout_error <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "        end else begin\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d timeout tracking\n", i);
        fprintf(fo, "            if (snoop_pending[%d]) begin\n", i);
        fprintf(fo, "                if (snoop_timeout_counter[%d] > 16'hFFF0) begin\n", i);
        fprintf(fo, "                    snoop_timeout_error[%d] <= 1'b1;\n", i);
        fprintf(fo, "                end else begin\n");
        fprintf(fo, "                    snoop_timeout_counter[%d] <= snoop_timeout_counter[%d] + 1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            end else begin\n");
        fprintf(fo, "                snoop_timeout_counter[%d] <= 16'h0000;\n", i);
        fprintf(fo, "                snoop_timeout_error[%d] <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
    }
    
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Enhanced ACE-Lite transaction type validation
    fprintf(fo, "    // ACE-Lite Transaction Type Validation\n");
    fprintf(fo, "    // ACE-Lite supports only specific transaction types\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Valid ACE-Lite transaction types\n");
    fprintf(fo, "    localparam [2:0] ACELIT_WRITE_NO_SNOOP     = 3'b000; // Non-coherent write\n");
    fprintf(fo, "    localparam [2:0] ACELIT_WRITE_LINE_UNIQUE  = 3'b001; // Write with invalidation\n"); 
    fprintf(fo, "    localparam [2:0] ACELIT_WRITE_CLEAN        = 3'b010; // Clean write\n");
    fprintf(fo, "    localparam [2:0] ACELIT_EVICT              = 3'b100; // Cache line eviction\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    localparam [3:0] ACELIT_READ_NO_SNOOP      = 4'b0000; // Non-coherent read\n");
    fprintf(fo, "    localparam [3:0] ACELIT_READ_SHARED        = 4'b0001; // Read shared\n");
    fprintf(fo, "    localparam [3:0] ACELIT_READ_CLEAN         = 4'b0010; // Read clean\n");
    fprintf(fo, "    localparam [3:0] ACELIT_READ_UNIQUE        = 4'b0111; // Read exclusive\n");
    fprintf(fo, "    localparam [3:0] ACELIT_CLEAN_SHARED       = 4'b1000; // Cache maintenance\n");
    fprintf(fo, "    localparam [3:0] ACELIT_CLEAN_INVALID      = 4'b1001; // Cache maintenance\n");
    fprintf(fo, "    localparam [3:0] ACELIT_MAKE_INVALID       = 4'b1101; // Cache maintenance\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Transaction type validation logic\n");
    // ace_lite_txn_error, invalid_write_txn, invalid_read_txn, unsupported_cache_maint declared as output reg above\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    always @(*) begin\n");
    fprintf(fo, "        ace_lite_txn_error = 1'b0;\n");
    fprintf(fo, "        invalid_write_txn = {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "        invalid_read_txn = {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "        unsupported_cache_maint = {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "        \n");
    
    // Add validation for each master
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        // Master %d transaction validation\n", i);
        fprintf(fo, "        if (m%d_awvalid) begin\n", i);
        fprintf(fo, "            // Validate write transactions\n");
        fprintf(fo, "            case (m%d_awsnoop)\n", i);
        fprintf(fo, "                ACELIT_WRITE_NO_SNOOP: begin\n");
        fprintf(fo, "                    // Valid: Non-coherent write allowed\n");
        fprintf(fo, "                    if (m%d_awdomain != DOMAIN_NON_SHAREABLE) begin\n", i);
        fprintf(fo, "                        invalid_write_txn[%d] = 1'b1; // Domain mismatch\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                ACELIT_WRITE_LINE_UNIQUE: begin\n");
        fprintf(fo, "                    // Valid: Write with invalidation for coherency\n");
        fprintf(fo, "                    if (m%d_awdomain == DOMAIN_NON_SHAREABLE) begin\n", i);
        fprintf(fo, "                        invalid_write_txn[%d] = 1'b1; // Should be shareable\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                ACELIT_WRITE_CLEAN: begin\n");
        fprintf(fo, "                    // Valid: Clean write (write-through)\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                ACELIT_EVICT: begin\n");
        fprintf(fo, "                    // Valid: Cache line eviction\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                default: begin\n");
        fprintf(fo, "                    // Invalid: Unsupported write snoop type for ACE-Lite\n");
        fprintf(fo, "                    invalid_write_txn[%d] = 1'b1;\n", i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            endcase\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "        \n");
        fprintf(fo, "        if (m%d_arvalid) begin\n", i);
        fprintf(fo, "            // Validate read transactions\n");
        fprintf(fo, "            case (m%d_arsnoop)\n", i);
        fprintf(fo, "                ACELIT_READ_NO_SNOOP: begin\n");
        fprintf(fo, "                    // Valid: Non-coherent read allowed\n");
        fprintf(fo, "                    if (m%d_ardomain != DOMAIN_NON_SHAREABLE) begin\n", i);
        fprintf(fo, "                        invalid_read_txn[%d] = 1'b1; // Domain mismatch\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                ACELIT_READ_SHARED: begin\n");
        fprintf(fo, "                    // Valid: Read shared line\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                ACELIT_READ_CLEAN: begin\n");
        fprintf(fo, "                    // Valid: Read clean (may allocate in cache)\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                ACELIT_READ_UNIQUE: begin\n");
        fprintf(fo, "                    // Valid: Read exclusive\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                ACELIT_CLEAN_SHARED: begin\n");
        fprintf(fo, "                    // Valid: Cache maintenance - clean shared lines\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                ACELIT_CLEAN_INVALID: begin\n");
        fprintf(fo, "                    // Valid: Cache maintenance - clean and invalidate\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                ACELIT_MAKE_INVALID: begin\n");
        fprintf(fo, "                    // Valid: Cache maintenance - make invalid\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                default: begin\n");
        fprintf(fo, "                    // Invalid: Unsupported read snoop type for ACE-Lite\n");
        fprintf(fo, "                    invalid_read_txn[%d] = 1'b1;\n", i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            endcase\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "        \n");
    }
    
    fprintf(fo, "        // Aggregate transaction validation errors\n");
    fprintf(fo, "        ace_lite_txn_error = |invalid_write_txn || |invalid_read_txn || |unsupported_cache_maint;\n");
    fprintf(fo, "    end\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Error reporting outputs\n");
    fprintf(fo, "    wire transaction_error = coherency_error || ace_lite_txn_error;\n");
    fprintf(fo, "    \n");
    
    // Add SD_USER signal processing logic
    fprintf(fo, "    // SD_USER signal processing and validation\n");
    fprintf(fo, "    // Extract coherency attributes from SD_USER signals\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "    wire m%d_cache_alloc_aw, m%d_cache_alloc_ar;\n", i, i);
        fprintf(fo, "    wire m%d_secure_aw, m%d_secure_ar;\n", i, i);
        fprintf(fo, "    wire [3:0] m%d_qos_aw, m%d_qos_ar;\n", i, i);
        fprintf(fo, "    assign m%d_cache_alloc_aw = m%d_sd_awuser[SD_AWUSER_CACHE_ALLOC];\n", i, i);
        fprintf(fo, "    assign m%d_cache_alloc_ar = m%d_sd_aruser[SD_ARUSER_CACHE_ALLOC];\n", i, i);
        fprintf(fo, "    assign m%d_secure_aw = m%d_sd_awuser[SD_AWUSER_SECURE];\n", i, i);
        fprintf(fo, "    assign m%d_secure_ar = m%d_sd_aruser[SD_ARUSER_SECURE];\n", i, i);
        fprintf(fo, "    assign m%d_qos_aw = m%d_sd_awuser[SD_AWUSER_QOS_START +: SD_AWUSER_QOS_WIDTH];\n", i, i);
        fprintf(fo, "    assign m%d_qos_ar = m%d_sd_aruser[SD_ARUSER_QOS_START +: SD_ARUSER_QOS_WIDTH];\n", i, i);
    }
    fprintf(fo, "\n");
    
    // Add coherency attribute validation
    fprintf(fo, "    // Coherency attribute validation\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] sd_user_error;\n");
    fprintf(fo, "    always @(*) begin\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        // Master %d SD_USER validation\n", i);
        fprintf(fo, "        sd_user_error[%d] = 1'b0;\n", i);
        fprintf(fo, "        \n");
        fprintf(fo, "        // Check cache allocation hint consistency\n");
        fprintf(fo, "        if (m%d_awvalid && m%d_cache_alloc_aw && ", i, i);
        fprintf(fo, "(m%d_awsnoop == AWSNOOP_WRITE_NO_SNOOP)) begin\n", i);
        fprintf(fo, "            // Error: Cache allocation requested but no snoop\n");
        fprintf(fo, "            sd_user_error[%d] = 1'b1;\n", i);
        fprintf(fo, "        end\n");
        fprintf(fo, "        \n");
        fprintf(fo, "        if (m%d_arvalid && m%d_cache_alloc_ar && ", i, i);
        fprintf(fo, "(m%d_arsnoop == ARSNOOP_READ_NO_SNOOP)) begin\n", i);
        fprintf(fo, "            // Error: Cache allocation requested but no snoop\n");
        fprintf(fo, "            sd_user_error[%d] = 1'b1;\n", i);
        fprintf(fo, "        end\n");
        fprintf(fo, "        \n");
        fprintf(fo, "        // Check secure transaction domain consistency\n");
        fprintf(fo, "        if (m%d_awvalid && m%d_secure_aw && ", i, i);
        fprintf(fo, "(m%d_awdomain == DOMAIN_NON_SHAREABLE)) begin\n", i);
        fprintf(fo, "            // Warning: Secure transaction in non-shareable domain\n");
        fprintf(fo, "            // This might be intentional but worth monitoring\n");
        fprintf(fo, "        end\n");
    }
    fprintf(fo, "    end\n\n");
    
    // Note: ACE-Lite signal routing is handled by the main interconnect
    // This module only provides coherency checking and monitoring
    
    // Generate cache maintenance operation detection
    fprintf(fo, "    // Cache maintenance operation detection\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] cache_maint_wr;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] cache_maint_rd;\n");
    fprintf(fo, "    always @(*) begin\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        cache_maint_wr[%d] = (m%d_awsnoop == AWSNOOP_WRITE_CLEAN) ||\n", i, i);
        fprintf(fo, "                              (m%d_awsnoop == AWSNOOP_WRITE_LINE_UNIQUE) ||\n", i);
        fprintf(fo, "                              (m%d_awsnoop == AWSNOOP_EVICT);\n", i);
        fprintf(fo, "        cache_maint_rd[%d] = (m%d_arsnoop == ARSNOOP_READ_CLEAN) ||\n", i, i);
        fprintf(fo, "                              (m%d_arsnoop == ARSNOOP_CLEAN_UNIQUE);\n", i);
    }
    fprintf(fo, "    end\n\n");
    
    // Generate barrier transaction handling
    fprintf(fo, "    // Barrier transaction handling\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] barrier_pending;\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            barrier_pending <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "        end else begin\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            if (m%d_awvalid && (m%d_awbar != BAR_NORMAL_ACCESS)) begin\n", i, i);
        fprintf(fo, "                barrier_pending[%d] <= 1'b1;\n", i);
        fprintf(fo, "            end else if (m%d_bvalid && m%d_bready) begin\n", i, i);
        fprintf(fo, "                barrier_pending[%d] <= 1'b0;\n", i);
        fprintf(fo, "            end\n");
    }
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Add output wire assignments for transaction validation
    fprintf(fo, "    // Output assignments for transaction validation errors\n");
    fprintf(fo, "    assign transaction_error = coherency_error || ace_lite_txn_error;\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Continuous assignment outputs are handled by the validation logic above\n");
    fprintf(fo, "    // ace_lite_txn_error, invalid_write_txn, invalid_read_txn are driven by always block\n\n");
    
    fprintf(fo, "endmodule\n");
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
    fprintf(fo, "     , input  %s  [WIDTH_SD_AWUSER-1:0] %sSD_AWUSER\n", otype, prefix);
    fprintf(fo, "     , input  %s  [WIDTH_SD_WUSER-1:0]  %sSD_WUSER\n", otype, prefix);
    fprintf(fo, "     , input  %s  [1:0]              %sARDOMAIN\n", otype, prefix);
    fprintf(fo, "     , input  %s  [3:0]              %sARSNOOP\n", otype, prefix);
    fprintf(fo, "     , input  %s  [1:0]              %sARBAR\n", otype, prefix);
    fprintf(fo, "     , input  %s  [WIDTH_SD_ARUSER-1:0] %sSD_ARUSER\n", otype, prefix);
    fprintf(fo, "     , output %s  [WIDTH_SD_BUSER-1:0]  %sSD_BUSER\n", otype, prefix);
    fprintf(fo, "     , output %s  [WIDTH_SD_RUSER-1:0]  %sSD_RUSER\n", otype, prefix);
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
    fprintf(fo, "     , output %s  [WIDTH_SD_AWUSER-1:0] %sSD_AWUSER\n", otype, prefix);
    fprintf(fo, "     , output %s  [WIDTH_SD_WUSER-1:0]  %sSD_WUSER\n", otype, prefix);
    fprintf(fo, "     , output %s  [1:0]              %sARDOMAIN\n", otype, prefix);
    fprintf(fo, "     , output %s  [3:0]              %sARSNOOP\n", otype, prefix);
    fprintf(fo, "     , output %s  [1:0]              %sARBAR\n", otype, prefix);
    fprintf(fo, "     , output %s  [WIDTH_SD_ARUSER-1:0] %sSD_ARUSER\n", otype, prefix);
    fprintf(fo, "     // ACE-Lite response signals\n");
    fprintf(fo, "     , input  %s  [WIDTH_SD_BUSER-1:0]  %sSD_BUSER\n", otype, prefix);
    fprintf(fo, "     , input  %s  [WIDTH_SD_RUSER-1:0]  %sSD_RUSER\n", otype, prefix);
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
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
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
        fprintf(fo, "            if (m%d_awvalid && m%d_awready && ", i, i);
        fprintf(fo, "(m%d_awsnoop != AWSNOOP_WRITE_NO_SNOOP)) begin\n", i);
        fprintf(fo, "                snoop_pending[%d] <= 1'b1;\n", i);
        fprintf(fo, "                snoop_id[%d] <= m%d_awid;\n", i, i);
        fprintf(fo, "                snoop_addr[%d] <= m%d_awaddr;\n", i, i);
        fprintf(fo, "            end else if (snoop_pending[%d] && m%d_bvalid && m%d_bready) begin\n", i, i, i);
        fprintf(fo, "                snoop_pending[%d] <= 1'b0;\n", i);
        fprintf(fo, "                snoop_complete[%d] <= 1'b1;\n", i);
        fprintf(fo, "            end\n\n");
        
        // Read snoop handling
        fprintf(fo, "            // Master %d read snoop\n", i);
        fprintf(fo, "            if (m%d_arvalid && m%d_arready && ", i, i);
        fprintf(fo, "(m%d_arsnoop != ARSNOOP_READ_NO_SNOOP)) begin\n", i);
        fprintf(fo, "                snoop_pending[%d] <= 1'b1;\n", i);
        fprintf(fo, "                snoop_id[%d] <= m%d_arid;\n", i, i);
        fprintf(fo, "                snoop_addr[%d] <= m%d_araddr;\n", i, i);
        fprintf(fo, "            end else if (snoop_pending[%d] && m%d_rlast && m%d_rvalid && m%d_rready) begin\n", i, i, i, i);
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
    
    // Exclusive Access Monitor Implementation
    fprintf(fo, "    // Exclusive Access Monitoring for ACE-Lite\n");
    fprintf(fo, "    // Tracks exclusive transactions per master/address pair\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Exclusive access state tracking\n");
    fprintf(fo, "    reg [WIDTH_AD-1:0] exclusive_addr [NUM_MASTER-1:0];    // Exclusive address per master\n");
    fprintf(fo, "    reg [WIDTH_ID-1:0] exclusive_id [NUM_MASTER-1:0];      // Exclusive transaction ID per master\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] exclusive_valid;                  // Valid exclusive reservation\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] exclusive_cleared;                // Exclusive access cleared\n");
    fprintf(fo, "    reg [7:0] exclusive_size [NUM_MASTER-1:0];             // Exclusive access size\n");
    fprintf(fo, "    \n");
    
    // Exclusive access validation logic
    fprintf(fo, "    // Exclusive Access Validation Logic\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            exclusive_valid <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            exclusive_cleared <= {NUM_MASTER{1'b0}};\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            exclusive_addr[%d] <= {WIDTH_AD{1'b0}};\n", i);
        fprintf(fo, "            exclusive_id[%d] <= {WIDTH_ID{1'b0}};\n", i);
        fprintf(fo, "            exclusive_size[%d] <= 8'h00;\n", i);
    }
    
    fprintf(fo, "        end else begin\n");
    
    // Process each master's exclusive access
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d exclusive access processing\n", i);
        fprintf(fo, "            \n");
        fprintf(fo, "            // Exclusive read (LoadExclusive) detection\n");
        fprintf(fo, "            if (m%d_arvalid && m%d_arready && (m%d_araddr[1:0] == 2'b00)) begin\n", i, i, i);
        fprintf(fo, "                // Check for exclusive read - must be aligned and size <= 128 bytes\n");
        fprintf(fo, "                if (m%d_arsnoop == ARSNOOP_READ_UNIQUE && \n", i);
        fprintf(fo, "                    (m%d_araddr[6:0] == 7'h00 || m%d_araddr[5:0] == 6'h00 || \n", i, i);
        fprintf(fo, "                     m%d_araddr[4:0] == 5'h00 || m%d_araddr[3:0] == 4'h00 || \n", i, i);
        fprintf(fo, "                     m%d_araddr[2:0] == 3'h00 || m%d_araddr[1:0] == 2'h00)) begin\n", i, i);
        fprintf(fo, "                    // Valid exclusive read - set reservation\n");
        fprintf(fo, "                    exclusive_addr[%d] <= m%d_araddr;\n", i, i);
        fprintf(fo, "                    exclusive_id[%d] <= m%d_arid;\n", i, i);
        fprintf(fo, "                    exclusive_valid[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    exclusive_cleared[%d] <= 1'b0;\n", i);
        fprintf(fo, "                    exclusive_size[%d] <= 8'h01 << m%d_arsize;  // Convert size encoding\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Exclusive write (StoreExclusive) detection\n");
        fprintf(fo, "            if (m%d_awvalid && m%d_awready) begin\n", i, i);
        fprintf(fo, "                if (m%d_awsnoop == AWSNOOP_WRITE_LINE_UNIQUE && exclusive_valid[%d]) begin\n", i, i);
        fprintf(fo, "                    // Check if this matches the exclusive reservation\n");
        fprintf(fo, "                    if ((exclusive_addr[%d] == m%d_awaddr) && \n", i, i);
        fprintf(fo, "                        (exclusive_id[%d] == m%d_awid)) begin\n", i, i);
        fprintf(fo, "                        // Successful exclusive write - will generate EXOKAY\n");
        fprintf(fo, "                        exclusive_cleared[%d] <= 1'b1;\n", i);
        fprintf(fo, "                        exclusive_valid[%d] <= 1'b0;   // Clear reservation\n", i);
        fprintf(fo, "                    end else begin\n");
        fprintf(fo, "                        // Address/ID mismatch - will generate OKAY (failed)\n");
        fprintf(fo, "                        exclusive_cleared[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Clear exclusive reservation on intervening writes from other masters\n");
        
        // Check for intervening writes from other masters
        for (int j = 0; j < numM; j++) {
            if (j != i) {
                fprintf(fo, "            if (m%d_awvalid && m%d_awready && exclusive_valid[%d]) begin\n", j, j, i);
                fprintf(fo, "                // Check if this write overlaps with master %d's exclusive reservation\n", i);
                fprintf(fo, "                if ((m%d_awaddr >= exclusive_addr[%d]) && \n", j, i);
                fprintf(fo, "                    (m%d_awaddr < (exclusive_addr[%d] + exclusive_size[%d]))) begin\n", j, i, i);
                fprintf(fo, "                    // Intervening write detected - clear exclusive reservation\n");
                fprintf(fo, "                    exclusive_valid[%d] <= 1'b0;\n", i);
                fprintf(fo, "                    exclusive_cleared[%d] <= 1'b1;\n", i);
                fprintf(fo, "                end\n");
                fprintf(fo, "            end\n");
            }
        }
        fprintf(fo, "            \n");
    }
    
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    // Exclusive response generation logic
    fprintf(fo, "    // Exclusive Access Response Generation\n");
    fprintf(fo, "    // Generates EXOKAY for successful exclusive writes, OKAY for failures\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] exclusive_success;\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] exclusive_fail;\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    always @(*) begin\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        // Master %d exclusive response logic\n", i);
        fprintf(fo, "        if (exclusive_cleared[%d] && exclusive_valid[%d]) begin\n", i, i);
        fprintf(fo, "            // Successful exclusive operation\n");
        fprintf(fo, "            exclusive_success[%d] = 1'b1;\n", i);
        fprintf(fo, "            exclusive_fail[%d] = 1'b0;\n", i);
        fprintf(fo, "        end else if (exclusive_cleared[%d] && !exclusive_valid[%d]) begin\n", i, i);
        fprintf(fo, "            // Failed exclusive operation (reservation lost)\n");
        fprintf(fo, "            exclusive_success[%d] = 1'b0;\n", i);
        fprintf(fo, "            exclusive_fail[%d] = 1'b1;\n", i);
        fprintf(fo, "        end else begin\n");
        fprintf(fo, "            // No exclusive operation\n");
        fprintf(fo, "            exclusive_success[%d] = 1'b0;\n", i);
        fprintf(fo, "            exclusive_fail[%d] = 1'b0;\n", i);
        fprintf(fo, "        end\n");
        fprintf(fo, "        \n");
    }
    
    fprintf(fo, "    end\n\n");
    
    // Exclusive access violation detection
    fprintf(fo, "    // Exclusive Access Violation Detection\n");
    fprintf(fo, "    // Detects protocol violations in exclusive access usage\n");
    fprintf(fo, "    reg [NUM_MASTER-1:0] exclusive_violation;\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    always @(*) begin\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        exclusive_violation[%d] = 1'b0;\n", i);
        fprintf(fo, "        \n");
        fprintf(fo, "        // Check for exclusive access violations on master %d\n", i);
        fprintf(fo, "        if (m%d_awvalid && (m%d_awsnoop == AWSNOOP_WRITE_LINE_UNIQUE)) begin\n", i, i);
        fprintf(fo, "            // Exclusive write without preceding exclusive read\n");
        fprintf(fo, "            if (!exclusive_valid[%d]) begin\n", i);
        fprintf(fo, "                exclusive_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Check alignment constraints (must be naturally aligned)\n");
        fprintf(fo, "            case (m%d_awsize)\n", i);
        fprintf(fo, "                3'b000: begin // 1 byte\n");
        fprintf(fo, "                    if (m%d_awaddr[0:0] != 1'b0) exclusive_violation[%d] = 1'b1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "                3'b001: begin // 2 bytes\n");
        fprintf(fo, "                    if (m%d_awaddr[1:0] != 2'b00) exclusive_violation[%d] = 1'b1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "                3'b010: begin // 4 bytes\n");
        fprintf(fo, "                    if (m%d_awaddr[2:0] != 3'b000) exclusive_violation[%d] = 1'b1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "                3'b011: begin // 8 bytes\n");
        fprintf(fo, "                    if (m%d_awaddr[3:0] != 4'b0000) exclusive_violation[%d] = 1'b1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "                3'b100: begin // 16 bytes\n");
        fprintf(fo, "                    if (m%d_awaddr[4:0] != 5'b00000) exclusive_violation[%d] = 1'b1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "                3'b101: begin // 32 bytes\n");
        fprintf(fo, "                    if (m%d_awaddr[5:0] != 6'b000000) exclusive_violation[%d] = 1'b1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "                3'b110: begin // 64 bytes\n");
        fprintf(fo, "                    if (m%d_awaddr[6:0] != 7'b0000000) exclusive_violation[%d] = 1'b1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "                3'b111: begin // 128 bytes (maximum)\n");
        fprintf(fo, "                    if (m%d_awaddr[7:0] != 8'b00000000) exclusive_violation[%d] = 1'b1;\n", i, i);
        fprintf(fo, "                end\n");
        fprintf(fo, "            endcase\n");
        fprintf(fo, "            \n");
        fprintf(fo, "            // Check maximum size constraint (128 bytes)\n");
        fprintf(fo, "            if ((8'h01 << m%d_awsize) > 8'd128) begin\n", i);
        fprintf(fo, "                exclusive_violation[%d] = 1'b1;\n", i);
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "        \n");
    }
    
    fprintf(fo, "    end\n\n");
    
    // Instantiate MOESI cache state management
    fprintf(fo, "    // MOESI Cache State Management Instantiation\n");
    fprintf(fo, "    %sace_lite_cache_states\n", prefix);
    fprintf(fo, "      #(.NUM_MASTER(NUM_MASTER),\n");
    fprintf(fo, "        .NUM_SLAVE(NUM_SLAVE),\n");
    fprintf(fo, "        .WIDTH_AD(WIDTH_AD),\n");
    fprintf(fo, "        .WIDTH_DA(WIDTH_DA),\n");
    fprintf(fo, "        .CACHE_LINE_ENTRIES(1024))\n");
    fprintf(fo, "    cache_states_inst (\n");
    fprintf(fo, "        .clk(clk),\n");
    fprintf(fo, "        .rst_n(rst_n),\n");
    
    // Connect master interfaces
    for (i = 0; i < numM; i++) {
        fprintf(fo, "        // Master %d cache state connections\n", i);
        fprintf(fo, "        .m%d_addr(m%d_awaddr),         // Use AW address for state tracking\n", i, i);
        fprintf(fo, "        .m%d_state_req(m%d_awvalid),   // Request state on AW valid\n", i, i);
        fprintf(fo, "        .m%d_new_state(3'b001),        // Default to SHARED state\n", i);
        fprintf(fo, "        .m%d_state_update(m%d_awvalid && m%d_awready), // Update on handshake\n", i, i, i);
        fprintf(fo, "        .m%d_current_state(),          // Current cache state output\n", i);
        fprintf(fo, "        .m%d_state_valid(),            // State valid output\n", i);
    }
    
    fprintf(fo, "        // Global monitoring outputs\n");
    fprintf(fo, "        .cache_hits(),\n");
    fprintf(fo, "        .cache_misses(),\n");
    fprintf(fo, "        .state_transitions(),\n");
    fprintf(fo, "        .coherency_conflict()\n");
    fprintf(fo, "    );\n\n");
    
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
    
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            barrier_state[%d] <= BARRIER_IDLE;\n", i);
    }
    fprintf(fo, "            barrier_block <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "        end else begin\n");
    
    for (i = 0; i < numM; i++) {
        fprintf(fo, "            // Master %d barrier handling\n", i);
        fprintf(fo, "            case (barrier_state[%d])\n", i);
        fprintf(fo, "                BARRIER_IDLE: begin\n");
        fprintf(fo, "                    if (m%d_awvalid && (m%d_awbar == BAR_MEMORY_BARRIER || ", i, i);
        fprintf(fo, "m%d_awbar == BAR_SYNC_BARRIER)) begin\n", i);
        fprintf(fo, "                        barrier_state[%d] <= BARRIER_WAIT;\n", i);
        fprintf(fo, "                        barrier_block[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end else if (m%d_arvalid && (m%d_arbar == BAR_MEMORY_BARRIER || ", i, i);
        fprintf(fo, "m%d_arbar == BAR_SYNC_BARRIER)) begin\n", i);
        fprintf(fo, "                        barrier_state[%d] <= BARRIER_WAIT;\n", i);
        fprintf(fo, "                        barrier_block[%d] <= 1'b1;\n", i);
        fprintf(fo, "                    end\n");
        fprintf(fo, "                end\n");
        fprintf(fo, "                BARRIER_WAIT: begin\n");
        fprintf(fo, "                    // Wait for all previous transactions to complete\n");
        fprintf(fo, "                    if (!snoop_pending[%d] && !m%d_awvalid && !m%d_arvalid) begin\n", i, i, i);
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
    fprintf(fo, "    // Note: barrier_block signals would connect to external logic\n");
    fprintf(fo, "    // This is a monitoring/analysis module\n");
    fprintf(fo, "\n");
    
    fprintf(fo, "endmodule\n\n");
    
    return 0;
}