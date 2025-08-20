//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// AXI4 REGION Implementation
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "gen_amba_axi.h"
#include "gen_axi_utils.h"

//--------------------------------------------------------
// Generate REGION support for address decoding
//--------------------------------------------------------
int gen_axi_region(unsigned int numM, unsigned int numS, 
                   char *prefix, axi_features_t *features, FILE *fo)
{
    int i, j;
    
    if (!features || !features->enable_region) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// AXI4 REGION Implementation\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "// REGION allows a single physical slave to have multiple logical interfaces\n");
    fprintf(fo, "// Each region can have different attributes (protection, cache, etc.)\n\n");
    
    // Generate REGION parameter definitions
    fprintf(fo, "    // REGION parameters\n");
    fprintf(fo, "    localparam WIDTH_REGION = %d; // REGION signal width (4 bits per AXI4)\n", features->width_region);
    fprintf(fo, "    localparam NUM_REGIONS = 2**WIDTH_REGION; // Number of regions per slave\n\n");
    
    // Generate REGION decoder for each slave
    fprintf(fo, "    // REGION-based address decoding\n");
    fprintf(fo, "    // Each slave can support up to %d regions\n", (1 << features->width_region));
    fprintf(fo, "    // The REGION value must remain constant for all beats in a burst\n\n");
    
    for (i = 0; i < numS; i++) {
        fprintf(fo, "    // Slave %d REGION decoder\n", i);
        fprintf(fo, "    reg s%d_region_hit;\n", i);
        fprintf(fo, "    reg [WIDTH_REGION-1:0] s%d_active_awregion;\n", i);
        fprintf(fo, "    reg [WIDTH_REGION-1:0] s%d_active_arregion;\n", i);
        fprintf(fo, "    reg s%d_aw_region_valid;\n", i);
        fprintf(fo, "    reg s%d_ar_region_valid;\n", i);
        fprintf(fo, "\n");
    }
    
    // Generate REGION configuration registers
    fprintf(fo, "    // REGION configuration (programmable via APB or static)\n");
    fprintf(fo, "    // Each region can have different access permissions\n");
    for (i = 0; i < numS; i++) {
        fprintf(fo, "    // Slave %d region configuration\n", i);
        fprintf(fo, "    reg [WIDTH_AD-1:0] s%d_region_base  [0:NUM_REGIONS-1];\n", i);
        fprintf(fo, "    reg [WIDTH_AD-1:0] s%d_region_size  [0:NUM_REGIONS-1];\n", i);
        fprintf(fo, "    reg                s%d_region_enable[0:NUM_REGIONS-1];\n", i);
        fprintf(fo, "    reg [2:0]          s%d_region_prot  [0:NUM_REGIONS-1]; // Protection per region\n", i);
        fprintf(fo, "    reg [3:0]          s%d_region_cache [0:NUM_REGIONS-1]; // Cache attr per region\n", i);
        fprintf(fo, "\n");
    }
    
    // Initialize region configurations
    fprintf(fo, "    // Initialize region configurations\n");
    fprintf(fo, "    initial begin\n");
    for (i = 0; i < numS; i++) {
        fprintf(fo, "        // Slave %d default regions\n", i);
        fprintf(fo, "        for (integer r = 0; r < NUM_REGIONS; r = r + 1) begin\n");
        fprintf(fo, "            s%d_region_base[r]   = ADDR_BASE%d + (r * 'h1000); // 4KB per region\n", i, i);
        fprintf(fo, "            s%d_region_size[r]   = 'h1000; // 4KB size\n", i);
        fprintf(fo, "            s%d_region_enable[r] = (r < 4) ? 1'b1 : 1'b0; // Enable first 4 regions\n", i);
        fprintf(fo, "            s%d_region_prot[r]   = 3'b010; // Non-secure, normal\n", i);
        fprintf(fo, "            s%d_region_cache[r]  = 4'b0011; // Write-back, allocate\n", i);
        fprintf(fo, "        end\n");
    }
    fprintf(fo, "    end\n\n");
    
    // Generate REGION validation logic
    fprintf(fo, "    // REGION validation - ensure REGION remains constant during burst\n");
    for (i = 0; i < numS; i++) {
        fprintf(fo, "    // Slave %d REGION validation\n", i);
        
        // Write channel REGION validation
        fprintf(fo, "    always @(posedge ACLK or negedge ARESETn) begin\n");
        fprintf(fo, "        if (!ARESETn) begin\n");
        fprintf(fo, "            s%d_active_awregion <= 0;\n", i);
        fprintf(fo, "            s%d_aw_region_valid <= 1'b1;\n", i);
        fprintf(fo, "        end else begin\n");
        fprintf(fo, "            if (S%d_AWVALID && S%d_AWREADY) begin\n", i, i);
        fprintf(fo, "                s%d_active_awregion <= S%d_AWREGION;\n", i, i);
        fprintf(fo, "                // Check if region is enabled\n");
        fprintf(fo, "                s%d_aw_region_valid <= s%d_region_enable[S%d_AWREGION];\n", i, i, i);
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "    end\n\n");
        
        // Read channel REGION validation
        fprintf(fo, "    always @(posedge ACLK or negedge ARESETn) begin\n");
        fprintf(fo, "        if (!ARESETn) begin\n");
        fprintf(fo, "            s%d_active_arregion <= 0;\n", i);
        fprintf(fo, "            s%d_ar_region_valid <= 1'b1;\n", i);
        fprintf(fo, "        end else begin\n");
        fprintf(fo, "            if (S%d_ARVALID && S%d_ARREADY) begin\n", i, i);
        fprintf(fo, "                s%d_active_arregion <= S%d_ARREGION;\n", i, i);
        fprintf(fo, "                // Check if region is enabled\n");
        fprintf(fo, "                s%d_ar_region_valid <= s%d_region_enable[S%d_ARREGION];\n", i, i, i);
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "    end\n\n");
    }
    
    // Generate REGION-based address checking
    fprintf(fo, "    // REGION-based address boundary checking\n");
    for (i = 0; i < numS; i++) {
        fprintf(fo, "    // Slave %d address checking per region\n", i);
        fprintf(fo, "    wire s%d_aw_in_region = (S%d_AWADDR >= s%d_region_base[S%d_AWREGION]) &&\n", i, i, i, i);
        fprintf(fo, "                             (S%d_AWADDR < (s%d_region_base[S%d_AWREGION] + s%d_region_size[S%d_AWREGION]));\n", 
                i, i, i, i, i);
        fprintf(fo, "    wire s%d_ar_in_region = (S%d_ARADDR >= s%d_region_base[S%d_ARREGION]) &&\n", i, i, i, i);
        fprintf(fo, "                             (S%d_ARADDR < (s%d_region_base[S%d_ARREGION] + s%d_region_size[S%d_ARREGION]));\n\n", 
                i, i, i, i, i);
    }
    
    // Generate REGION error response logic
    fprintf(fo, "    // Generate SLVERR for invalid REGION access\n");
    for (i = 0; i < numS; i++) {
        fprintf(fo, "    // Slave %d REGION error generation\n", i);
        fprintf(fo, "    assign s%d_region_aw_error = S%d_AWVALID && (!s%d_aw_region_valid || !s%d_aw_in_region);\n", 
                i, i, i, i);
        fprintf(fo, "    assign s%d_region_ar_error = S%d_ARVALID && (!s%d_ar_region_valid || !s%d_ar_in_region);\n\n", 
                i, i, i, i);
    }
    
    // Generate REGION-aware protection checking
    fprintf(fo, "    // REGION-aware protection and cache attribute override\n");
    for (i = 0; i < numS; i++) {
        fprintf(fo, "    // Slave %d protection override based on region\n", i);
        fprintf(fo, "    wire [2:0] s%d_effective_awprot = s%d_region_prot[s%d_active_awregion] | S%d_AWPROT;\n", 
                i, i, i, i);
        fprintf(fo, "    wire [2:0] s%d_effective_arprot = s%d_region_prot[s%d_active_arregion] | S%d_ARPROT;\n", 
                i, i, i, i);
        fprintf(fo, "    wire [3:0] s%d_effective_awcache = s%d_region_cache[s%d_active_awregion] & S%d_AWCACHE;\n", 
                i, i, i, i);
        fprintf(fo, "    wire [3:0] s%d_effective_arcache = s%d_region_cache[s%d_active_arregion] & S%d_ARCACHE;\n\n", 
                i, i, i, i);
    }
    
    // Generate debug outputs
    fprintf(fo, "    // REGION debug monitoring\n");
    fprintf(fo, "    `ifdef REGION_DEBUG\n");
    fprintf(fo, "    always @(posedge ACLK) begin\n");
    for (i = 0; i < numS; i++) {
        fprintf(fo, "        if (S%d_AWVALID && S%d_AWREADY) begin\n", i, i);
        fprintf(fo, "            $display(\"[REGION] Slave %d: Write to region %%d, addr 0x%%h\",\n", i);
        fprintf(fo, "                     S%d_AWREGION, S%d_AWADDR);\n", i, i);
        fprintf(fo, "            if (s%d_region_aw_error) begin\n", i);
        fprintf(fo, "                $display(\"[REGION] ERROR: Invalid region or address!\");\n");
        fprintf(fo, "            end\n");
        fprintf(fo, "        end\n");
    }
    fprintf(fo, "    end\n");
    fprintf(fo, "    `endif\n\n");
    
    return 0;
}

//--------------------------------------------------------
// Add REGION ports to master interface
//--------------------------------------------------------
int gen_axi_region_mport(char *prefix, char *otype, axi_features_t *features, FILE *fo)
{
    if (!features || !features->enable_region) return 0;
    
    fprintf(fo, "     `ifdef AMBA_AXI4_REGION\n");
    fprintf(fo, "     // AXI4 REGION signals (separate from QoS)\n");
    fprintf(fo, "     , input  %s  [%d:0]           %sAWREGION\n", otype, features->width_region-1, prefix);
    fprintf(fo, "     , input  %s  [%d:0]           %sARREGION\n", otype, features->width_region-1, prefix);
    fprintf(fo, "     `endif\n");
    
    return 0;
}

//--------------------------------------------------------
// Add REGION ports to slave interface
//--------------------------------------------------------
int gen_axi_region_sport(char *prefix, char *otype, axi_features_t *features, FILE *fo)
{
    if (!features || !features->enable_region) return 0;
    
    fprintf(fo, "     `ifdef AMBA_AXI4_REGION\n");
    fprintf(fo, "     // AXI4 REGION signals (separate from QoS)\n");
    fprintf(fo, "     , output %s  [%d:0]           %sAWREGION\n", otype, features->width_region-1, prefix);
    fprintf(fo, "     , output %s  [%d:0]           %sARREGION\n", otype, features->width_region-1, prefix);
    fprintf(fo, "     `endif\n");
    
    return 0;
}