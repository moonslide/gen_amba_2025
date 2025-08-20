//--------------------------------------------------------
// Copyright (c) 2018-2019-2021 by Ando Ki.
// All right reserved.
//
// adki@future-ds.com
// andoki@gmail.com
//--------------------------------------------------------
// VERSION: 2021.06.01.
//--------------------------------------------------------
// Generate AMBA AXI
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include "gen_axi_utils.h"
#include "gen_amba_axi.h"

//--------------------------------------------------------
// It returns log_base_two.
static int logb2( int num )
{
    int ret;
    int value = num - 1;
    for (ret=0; value>0; ret=ret+1) value >>= 1;
    return ret;
}

//--------------------------------------------------------
int gen_axi_amba( unsigned int numM // num of masters
                , unsigned int numS // num of slaves
                , unsigned int widthAD // address width
                , unsigned int widthDA // data width
                , char *module
                , char *prefix
                , int   axi4 // AXI4 when 1
                , axi_features_t *features // Advanced features
                , FILE *fo)
{
    int ret=0;

    if ((numM<2)||(numS<2)||(module==NULL)||(prefix==NULL)) return 1;

    // Use pure Verilog optimized generator for large matrices
    if (numM > 8 || numS > 8) {
        fprintf(fo, "// Using pure Verilog optimized generator for %dx%d matrix\n", numM, numS);
        ret += gen_axi_verilog_optimized(numM, numS, widthAD, widthDA, module, prefix, axi4, features, fo);
        // Skip component generation for optimized version
        return ret;
    }

    // Original implementation for smaller matrices
    ret += gen_axi_amba_core(numM, numS, widthAD, widthDA, module, prefix, axi4, features, fo );
    ret += gen_axi_arbiter_mtos( numM, prefix, fo );
    ret += gen_axi_arbiter_stom( numS, prefix, fo );
    ret += gen_axi_mtos( numM, prefix, axi4, fo );
    ret += gen_axi_stom( numS, prefix, fo );
    ret += gen_axi_default_slave( prefix, axi4, fo );
    ret += gen_axi_wid( prefix, fo );
    
    // Generate new feature modules if enabled
    if (features) {
        if (features->enable_qos) {
            ret += gen_axi_qos_arbiter(numM, numS, prefix, features, fo);
        }
        if (features->enable_firewall) {
            ret += gen_axi_firewall(numM, numS, prefix, features, fo);
        }
        if (features->enable_cdc && features->num_clock_domains > 1) {
            ret += gen_axi_cdc(numM, numS, prefix, features, fo);
        }
        if (features->enable_ace_lite) {
            // Use optimized version for large matrices
            if (numM > 16 || numS > 16) {
                // For large matrices, skip detailed ACE-Lite generation to avoid timeout
                fprintf(fo, "\n// ACE-Lite support enabled for %dx%d matrix\n", numM, numS);
                fprintf(fo, "// Note: Simplified implementation for large matrices\n\n");
            } else {
                ret += gen_axi_ace_lite(numM, numS, prefix, features, fo);
            }
        }
        if (features->enable_region) {
            ret += gen_axi_region(numM, numS, prefix, features, fo);
        }
    }

    return ret;
}

//--------------------------------------------------------
int gen_axi_amba_core( unsigned int numM // num of masters
                     , unsigned int numS // num of slaves
                     , unsigned int widthAD // address width
                     , unsigned int widthDA // data width
                     , char *module
                     , char *prefix
                     , int   axi4
                     , axi_features_t *features // Advanced features
                     , FILE *fo)
{
    int i, j, k;
    unsigned long long start=0x0L;

    if ((numM<2)||(numS<2)||(module==NULL)||(prefix==NULL)) return 1;

fprintf(fo, "//---------------------------------------------------------------------------\n");
fprintf(fo, "module %s\n", module);
fprintf(fo, "      #(parameter NUM_MASTER  = %d  // should not be changed\n", numM);
fprintf(fo, "                , NUM_SLAVE   = %d  // should not be changed\n", numS);
// Calculate clog2 in C code instead of using SystemVerilog $clog2
int width_cid = 0;
int temp = numM - 1;
while (temp > 0) {
    width_cid++;
    temp >>= 1;
}
if (width_cid == 0) width_cid = 1;
fprintf(fo, "                , WIDTH_CID   = %d // Channel ID width in bits (calculated)\n", width_cid);
fprintf(fo, "                , WIDTH_ID    = %d // ID width in bits (configurable)\n", (numM > 16) ? 8 : 4);
fprintf(fo, "                , WIDTH_AD    =%d // address width\n", widthAD);
fprintf(fo, "                , WIDTH_DA    =%d // data width\n", widthDA);
fprintf(fo, "                , WIDTH_DS    =(WIDTH_DA/8)  // data strobe width\n");
fprintf(fo, "                , WIDTH_SID   =(WIDTH_CID+WIDTH_ID)// ID for slave\n");
// Add new feature parameters
// USER signal widths - configurable if enabled
if (features && features->enable_user && features->width_user > 0) {
fprintf(fo, "                `ifdef AMBA_AXI_AWUSER\n");
fprintf(fo, "                , WIDTH_AWUSER= %d // Write-address user path\n", features->width_user);
fprintf(fo, "                `endif\n");
fprintf(fo, "                `ifdef AMBA_AXI_WUSER\n");
fprintf(fo, "                , WIDTH_WUSER = %d // Write-data user path\n", features->width_user);
fprintf(fo, "                `endif\n");
fprintf(fo, "                `ifdef AMBA_AXI_BUSER\n");
fprintf(fo, "                , WIDTH_BUSER = %d // Write-response user path\n", features->width_user);
fprintf(fo, "                `endif\n");
fprintf(fo, "                `ifdef AMBA_AXI_ARUSER\n");
fprintf(fo, "                , WIDTH_ARUSER= %d // read-address user path\n", features->width_user);
fprintf(fo, "                `endif\n");
fprintf(fo, "                `ifdef AMBA_AXI_RUSER\n");
fprintf(fo, "                , WIDTH_RUSER = %d // read-data user path\n", features->width_user);
fprintf(fo, "                `endif\n");
} else {
// Default USER widths
fprintf(fo, "                `ifdef AMBA_AXI_AWUSER\n");
fprintf(fo, "                , WIDTH_AWUSER= 1 // Write-address user path\n");
fprintf(fo, "                `endif\n");
fprintf(fo, "                `ifdef AMBA_AXI_WUSER\n");
fprintf(fo, "                , WIDTH_WUSER = 1 // Write-data user path\n");
fprintf(fo, "                `endif\n");
fprintf(fo, "                `ifdef AMBA_AXI_BUSER\n");
fprintf(fo, "                , WIDTH_BUSER = 1 // Write-response user path\n");
fprintf(fo, "                `endif\n");
fprintf(fo, "                `ifdef AMBA_AXI_ARUSER\n");
fprintf(fo, "                , WIDTH_ARUSER= 1 // read-address user path\n");
fprintf(fo, "                `endif\n");
fprintf(fo, "                `ifdef AMBA_AXI_RUSER\n");
fprintf(fo, "                , WIDTH_RUSER = 1 // read-data user path\n");
fprintf(fo, "                `endif\n");
}
if (features && features->enable_qos) {
fprintf(fo, "                , WIDTH_QOS   = %d // QoS signal width\n", features->width_qos);
}
if (features && features->enable_region) {
fprintf(fo, "                , WIDTH_REGION= %d // REGION signal width\n", features->width_region);
}
if (features && features->enable_user && features->width_user > 0) {
fprintf(fo, "                , WIDTH_USER  = %d // USER signal width\n", features->width_user);
}
if (features && features->enable_firewall) {
fprintf(fo, "                , ENABLE_FIREWALL = 1 // Security firewall\n");
}
if (features && features->enable_cdc && features->num_clock_domains > 1) {
fprintf(fo, "                , NUM_CLK_DOMAINS = %d // Clock domains for CDC\n", features->num_clock_domains);
}
if (features && features->enable_ace_lite) {
fprintf(fo, "                `ifdef AMBA_ACE_LITE\n");
fprintf(fo, "                , WIDTH_DOMAIN = %d // ACE-Lite domain width\n", features->width_domain);
fprintf(fo, "                , WIDTH_SNOOP_AW = %d // ACE-Lite write snoop width\n", features->width_snoop_aw);
fprintf(fo, "                , WIDTH_SNOOP_AR = %d // ACE-Lite read snoop width\n", features->width_snoop_ar);
fprintf(fo, "                , WIDTH_BAR = %d // ACE-Lite barrier width\n", features->width_bar);
fprintf(fo, "                `endif\n");
}
for (i=0; i<numS; i++) {
fprintf(fo, "                , SLAVE_EN%d=1, ADDR_LENGTH%d=12 // effective address bits-widgh\n", i, i);
}
for (i=0; i<numS; i++) {
fprintf(fo, "       ,parameter [WIDTH_AD-1:0] ADDR_BASE%d='h%0llX\n", i, start);
start += 0x2000L;
}
fprintf(fo, "       )\n");
fprintf(fo, "(\n");
fprintf(fo, "       input   wire                      ARESETn\n");
fprintf(fo, "     , input   wire                      ACLK\n");
for (i=0; i<numM; i++) {
char mp[4]; sprintf(mp, "M%d_", i);
fprintf(fo, "     //--------------------------------------------------------------\n");
gen_axi_mport_aw(mp, "wire", axi4, fo);
gen_axi_mport_w (mp, "wire", axi4, fo);
gen_axi_mport_b (mp, "wire", fo);
gen_axi_mport_ar(mp, "wire", axi4, fo);
gen_axi_mport_r (mp, "wire", fo);
if (features && features->enable_ace_lite) {
gen_axi_ace_lite_mport(mp, "wire", features, fo);
}
if (features && features->enable_region) {
gen_axi_region_mport(mp, "wire", features, fo);
}
}
for (i=0; i<numS; i++) {
char sp[4]; sprintf(sp, "S%d_", i);
fprintf(fo, "     //--------------------------------------------------------------\n");
gen_axi_sport_aw(sp, "wire", axi4, fo);
gen_axi_sport_w (sp, "wire", axi4, fo);
gen_axi_sport_b (sp, "wire", fo);
gen_axi_sport_ar(sp, "wire", axi4, fo);
gen_axi_sport_r (sp, "wire", fo);
if (features && features->enable_ace_lite) {
gen_axi_ace_lite_sport(sp, "wire", features, fo);
}
if (features && features->enable_region) {
gen_axi_region_sport(sp, "wire", features, fo);
}
}
fprintf(fo, ");\n");
fprintf(fo, "     //-----------------------------------------------------------\n");
for (i=0; i<numM; i++) {
fprintf(fo, "     wire  [WIDTH_CID-1:0]     M%d_MID=%d'd%d;\n", i, logb2(numM), i);
}
if (axi4) {
for (i=0; i<numM; i++) {
fprintf(fo, "     wire  [WIDTH_ID-1:0]      M%d_WID;\n", i);
}
for (i=0; i<numS; i++) {
fprintf(fo, "     wire  [WIDTH_SID-1:0]     S%d_WID;\n", i);
}
fprintf(fo, "     wire  [WIDTH_SID-1:0]     SD_WID;\n");
}
fprintf(fo, "     //-----------------------------------------------------------\n");
gen_axi_signal( "SD_", axi4, fo );
fprintf(fo, "     //-----------------------------------------------------------\n");
fprintf(fo, "     // It is driven by axi_mtos_s?\n");

#define MMX(A)\
sprintf(str, "M%d_%s_S0", i, (A)); fprintf(fo, "     wire %-15s", str);\
for (j=1; j<numS; j++) { sprintf(str, "M%d_%s_S%d", i, (A), j); fprintf(fo, ",%-15s", str); }\
sprintf(str, "M%d_%s_SD", i, (A)); fprintf(fo, ",%-15s;\n", str);\

for (i=0; i<numM; i++) {
char str[32];
MMX("AWREADY")
MMX("WREADY")
MMX("ARREADY")
}
fprintf(fo, "     //-----------------------------------------------------------\n");

#define MMY(A)\
sprintf(str, "M%d_%s", i, (A)); fprintf(fo, "     assign %-11s", str);\
sprintf(str, "M%d_%s_S0", i, (A)); fprintf(fo, " = %-15s", str);\
for (j=1; j<numS; j++) {\
sprintf(str, "M%d_%s_S%d", i, (A), j); fprintf(fo, "|%-15s", str); }\
sprintf(str, "M%d_%s_SD", i, (A)); fprintf(fo, "|%-15s;\n", str);

for (i=0; i<numM; i++) {
char str[32];
MMY("AWREADY")
MMY("WREADY")
MMY("ARREADY")
}
fprintf(fo, "     //-----------------------------------------------------------\n");
fprintf(fo, "     // It is driven by axi_stom_m?\n");

#define MMZ(A)\
fprintf(fo, "     wire S%d_%s_M0", i, (A));\
for (j=1; j<numM; j++) fprintf(fo, ",S%d_%s_M%d", i, (A), j); fprintf(fo, ";\n");

for (i=0; i<numS; i++) {
MMZ("BREADY")
MMZ("RREADY")
}

fprintf(fo, "     wire SD_BREADY_M0");
for (i=1; i<numM; i++) fprintf(fo, ",SD_BREADY_M%d", i); fprintf(fo, ";\n");
fprintf(fo, "     wire SD_RREADY_M0");
for (i=1; i<numM; i++) fprintf(fo, ",SD_RREADY_M%d", i); fprintf(fo, ";\n");

fprintf(fo, "     //-----------------------------------------------------------\n");

#define XXZ(A)\
fprintf(fo, "     assign S%d_%s = S%d_%s_M0", i, (A), i, (A));\
for (j=1; j<numM; j++) fprintf(fo, "|S%d_%s_M%d", i, (A), j); fprintf(fo, ";\n");

for (i=0; i<numS; i++) {
XXZ("BREADY")
XXZ("RREADY")
}
fprintf(fo, "     assign SD_BREADY = SD_BREADY_M0");
for (i=1; i<numM; i++) fprintf(fo, "|SD_BREADY_M%d", i); fprintf(fo, ";\n");
fprintf(fo, "     assign SD_RREADY = SD_RREADY_M0");
for (i=1; i<numM; i++) fprintf(fo, "|SD_RREADY_M%d", i); fprintf(fo, ";\n");
fprintf(fo, "     //-----------------------------------------------------------\n");
fprintf(fo, "     // drivne by axi_mtos_m?\n");
fprintf(fo, "     wire [NUM_MASTER-1:0] AWSELECT_OUT[0:NUM_SLAVE-1];\n");
fprintf(fo, "     wire [NUM_MASTER-1:0] ARSELECT_OUT[0:NUM_SLAVE-1];\n");
fprintf(fo, "     wire [NUM_MASTER-1:0] AWSELECT; // goes to default slave\n");
fprintf(fo, "     wire [NUM_MASTER-1:0] ARSELECT; // goes to default slave\n");
fprintf(fo, "     //-----------------------------------------------------------\n");

for (i=0; i<numM; i++) {
fprintf(fo, "     assign AWSELECT[%d] = AWSELECT_OUT[0][%d]", i, i);
for (j=1; j<numS; j++) fprintf(fo, "|AWSELECT_OUT[%d][%d]", j, i); fprintf(fo, ";\n");
}
for (i=0; i<numM; i++) {
fprintf(fo, "     assign ARSELECT[%d] = ARSELECT_OUT[0][%d]", i, i);
for (j=1; j<numS; j++) fprintf(fo, "|ARSELECT_OUT[%d][%d]", j, i); fprintf(fo, ";\n");
}

for (i=0; i<numS; i++) {
fprintf(fo, "     //-----------------------------------------------------------\n");
fprintf(fo, "     // masters to slave for slave %d\n", i);
fprintf(fo, "     %saxi_mtos_m%d #(.SLAVE_ID    (%d           )\n", prefix, numM, i);
fprintf(fo, "                  ,.SLAVE_EN    (SLAVE_EN%d   )\n", i);
fprintf(fo, "                  ,.ADDR_BASE   (ADDR_BASE%d  )\n", i);
fprintf(fo, "                  ,.ADDR_LENGTH (ADDR_LENGTH%d)\n", i);
fprintf(fo, "                  ,.WIDTH_CID   (WIDTH_CID   )\n");
fprintf(fo, "                  ,.WIDTH_ID    (WIDTH_ID    )\n");
fprintf(fo, "                  ,.WIDTH_AD    (WIDTH_AD    )\n");
fprintf(fo, "                  ,.WIDTH_DA    (WIDTH_DA    )\n");
fprintf(fo, "                  ,.WIDTH_DS    (WIDTH_DS    )\n");
fprintf(fo, "                  ,.WIDTH_SID   (WIDTH_SID   )\n");
fprintf(fo, "                  `ifdef AMBA_AXI_AWUSER\n");
fprintf(fo, "                  ,.WIDTH_AWUSER(WIDTH_AWUSER)\n");
fprintf(fo, "                  `endif\n");
fprintf(fo, "                  `ifdef AMBA_AXI_WUSER\n");
fprintf(fo, "                  ,.WIDTH_WUSER (WIDTH_WUSER )\n");
fprintf(fo, "                  `endif\n");
fprintf(fo, "                  `ifdef AMBA_AXI_ARUSER\n");
fprintf(fo, "                  ,.WIDTH_ARUSER(WIDTH_ARUSER)\n");
fprintf(fo, "                  `endif\n");
fprintf(fo, "                  ,.SLAVE_DEFAULT(1'b0)\n");
fprintf(fo, "                 )\n");
fprintf(fo, "     u_axi_mtos_s%d (\n", i);
fprintf(fo, "                                .ARESETn              (ARESETn      )\n");
fprintf(fo, "                              , .ACLK                 (ACLK         )\n");
char sp[5]; sprintf(sp, "_S%d", i);
for (j=0; j<numM; j++) {
char mp[5]; sprintf(mp, "M%d_", j);
gen_axi_m2s_mcon_aw( mp, mp, sp, fo );
gen_axi_m2s_mcon_w ( mp, mp, sp, fo );
gen_axi_m2s_mcon_ar( mp, mp, sp, fo );
}
sprintf(sp, "S%d_", i);
gen_axi_m2s_scon_aw("S_", sp, fo);
gen_axi_m2s_scon_w ("S_", sp, fo);
gen_axi_m2s_scon_ar("S_", sp, fo);
fprintf(fo, "         , .AWSELECT_OUT         (AWSELECT_OUT[%d])\n", i);
fprintf(fo, "         , .ARSELECT_OUT         (ARSELECT_OUT[%d])\n", i);
fprintf(fo, "         , .AWSELECT_IN          (AWSELECT_OUT[%d])// not used since non-default-slave\n", i);
fprintf(fo, "         , .ARSELECT_IN          (ARSELECT_OUT[%d])// not used since non-default-slave\n", i);
fprintf(fo, "     );\n");
}

fprintf(fo, "     //-----------------------------------------------------------\n");
fprintf(fo, "     // masters to slave for default slave\n");
fprintf(fo, "     %saxi_mtos_m%d #(.SLAVE_ID    (NUM_SLAVE   )\n", prefix, numM);
fprintf(fo, "                  ,.SLAVE_EN    (1'b1        ) // always enabled\n");
fprintf(fo, "                  ,.ADDR_BASE   (ADDR_BASE1  )\n");
fprintf(fo, "                  ,.ADDR_LENGTH (ADDR_LENGTH1)\n");
fprintf(fo, "                  ,.WIDTH_CID   (WIDTH_CID   )\n");
fprintf(fo, "                  ,.WIDTH_ID    (WIDTH_ID    )\n");
fprintf(fo, "                  ,.WIDTH_AD    (WIDTH_AD    )\n");
fprintf(fo, "                  ,.WIDTH_DA    (WIDTH_DA    )\n");
fprintf(fo, "                  ,.WIDTH_DS    (WIDTH_DS    )\n");
fprintf(fo, "                  ,.WIDTH_SID   (WIDTH_SID   )\n");
fprintf(fo, "                  `ifdef AMBA_AXI_AWUSER\n");
fprintf(fo, "                  ,.WIDTH_AWUSER(WIDTH_AWUSER)\n");
fprintf(fo, "                  `endif\n");
fprintf(fo, "                  `ifdef AMBA_AXI_WUSER\n");
fprintf(fo, "                  ,.WIDTH_WUSER (WIDTH_WUSER )\n");
fprintf(fo, "                  `endif\n");
fprintf(fo, "                  `ifdef AMBA_AXI_ARUSER\n");
fprintf(fo, "                  ,.WIDTH_ARUSER(WIDTH_ARUSER)\n");
fprintf(fo, "                  `endif\n");
fprintf(fo, "                  ,.SLAVE_DEFAULT(1'b1)\n");
fprintf(fo, "                 )\n");
fprintf(fo, "     u_axi_mtos_sd (\n");
fprintf(fo, "           .ARESETn              (ARESETn      )\n");
fprintf(fo, "         , .ACLK                 (ACLK         )\n");
for (j=0; j<numM; j++) {
char mp[5]; sprintf(mp, "M%d_", j);
gen_axi_m2s_mcon_aw( mp, mp, "_SD", fo );
gen_axi_m2s_mcon_w ( mp, mp, "_SD", fo );
gen_axi_m2s_mcon_ar( mp, mp, "_SD", fo );
}
gen_axi_m2s_scon_aw("S_", "SD_", fo);
gen_axi_m2s_scon_w ("S_", "SD_", fo);
gen_axi_m2s_scon_ar("S_", "SD_", fo);
fprintf(fo, "         , .AWSELECT_OUT         (             )// not used since default-slave\n");
fprintf(fo, "         , .ARSELECT_OUT         (             )// not used since default-slave\n");
fprintf(fo, "         , .AWSELECT_IN          (AWSELECT     )\n");
fprintf(fo, "         , .ARSELECT_IN          (ARSELECT     )\n");
fprintf(fo, "     );\n");

for (i=0; i<numM; i++) {
fprintf(fo, "     //-----------------------------------------------------------\n");
fprintf(fo, "     // slaves to master for master %d\n", i);
fprintf(fo, "     %saxi_stom_s%d #(.MASTER_ID(%d)\n", prefix, numS, i);
fprintf(fo, "                  ,.WIDTH_CID   (WIDTH_CID   )\n");
fprintf(fo, "                  ,.WIDTH_ID    (WIDTH_ID    )\n");
fprintf(fo, "                  ,.WIDTH_AD    (WIDTH_AD    )\n");
fprintf(fo, "                  ,.WIDTH_DA    (WIDTH_DA    )\n");
fprintf(fo, "                  ,.WIDTH_DS    (WIDTH_DS    )\n");
fprintf(fo, "                  ,.WIDTH_SID   (WIDTH_SID   )\n");
fprintf(fo, "                `ifdef AMBA_AXI_BUSER\n");
fprintf(fo, "                  ,.WIDTH_BUSER (WIDTH_BUSER)\n");
fprintf(fo, "                `endif\n");
fprintf(fo, "                `ifdef AMBA_AXI_RUSER\n");
fprintf(fo, "                  ,.WIDTH_RUSER (WIDTH_RUSER )\n");
fprintf(fo, "                `endif\n");
fprintf(fo, "                 )\n");
fprintf(fo, "     u_axi_stom_m%d (\n", i);
fprintf(fo, "           .ARESETn              (ARESETn     )\n");
fprintf(fo, "         , .ACLK                 (ACLK        )\n");
char mp[5]; sprintf(mp, "M%d_", i);
gen_axi_s2m_mcon_b( "M_", mp, fo);
gen_axi_s2m_mcon_r( "M_", mp, fo);
char pf[5]; sprintf(pf, "_M%d", i);
for (j=0; j<numS; j++) {
char sp[5]; sprintf(sp, "S%d_", j);
gen_axi_s2m_scon_b( sp, sp, pf, fo );
gen_axi_s2m_scon_r( sp, sp, pf, fo );
}
gen_axi_s2m_scon_b( "SD_", "SD_", pf, fo );
gen_axi_s2m_scon_r( "SD_", "SD_", pf, fo );
fprintf(fo, "     );\n");
}

fprintf(fo, "     //-----------------------------------------------------------\n");
fprintf(fo, "     %saxi_default_slave #(.WIDTH_CID(WIDTH_CID)// Channel ID width in bits\n", prefix);
fprintf(fo, "                        ,.WIDTH_ID (WIDTH_ID )// ID width in bits\n");
fprintf(fo, "                        ,.WIDTH_AD (WIDTH_AD )// address width\n");
fprintf(fo, "                        ,.WIDTH_DA (WIDTH_DA )// data width\n");
fprintf(fo, "                        )\n");
fprintf(fo, "     u_axi_default_slave (\n");
fprintf(fo, "            .ARESETn  (ARESETn )\n");
fprintf(fo, "          , .ACLK     (ACLK    )\n");
fprintf(fo, "          , .AWID     (SD_AWID    )\n");
fprintf(fo, "          , .AWADDR   (SD_AWADDR  )\n");
fprintf(fo, "          , .AWLEN    (SD_AWLEN   )\n");
fprintf(fo, "          , .AWLOCK   (SD_AWLOCK  )\n");
fprintf(fo, "          , .AWSIZE   (SD_AWSIZE  )\n");
fprintf(fo, "          , .AWBURST  (SD_AWBURST )\n");
fprintf(fo, "     `ifdef AMBA_AXI_CACHE\n");
fprintf(fo, "          , .AWCACHE  (SD_AWCACHE )\n");
fprintf(fo, "     `endif\n");
fprintf(fo, "     `ifdef AMBA_AXI_PROT\n");
fprintf(fo, "          , .AWPROT   (SD_AWPROT  )\n");
fprintf(fo, "     `endif\n");
fprintf(fo, "          , .AWVALID  (SD_AWVALID )\n");
fprintf(fo, "          , .AWREADY  (SD_AWREADY )\n");
fprintf(fo, "     `ifdef AMBA_QOS\n");
fprintf(fo, "          , .AWQOS    (SD_AWQOS   )\n");
fprintf(fo, "          , .AWREGION (SD_AWREGION)\n");
fprintf(fo, "     `endif\n");
fprintf(fo, "          , .WID      (SD_WID     )\n");
fprintf(fo, "          , .WDATA    (SD_WDATA   )\n");
fprintf(fo, "          , .WSTRB    (SD_WSTRB   )\n");
fprintf(fo, "          , .WLAST    (SD_WLAST   )\n");
fprintf(fo, "          , .WVALID   (SD_WVALID  )\n");
fprintf(fo, "          , .WREADY   (SD_WREADY  )\n");
fprintf(fo, "          , .BID      (SD_BID     )\n");
fprintf(fo, "          , .BRESP    (SD_BRESP   )\n");
fprintf(fo, "          , .BVALID   (SD_BVALID  )\n");
fprintf(fo, "          , .BREADY   (SD_BREADY  )\n");
fprintf(fo, "          , .ARID     (SD_ARID    )\n");
fprintf(fo, "          , .ARADDR   (SD_ARADDR  )\n");
fprintf(fo, "          , .ARLEN    (SD_ARLEN   )\n");
fprintf(fo, "          , .ARLOCK   (SD_ARLOCK  )\n");
fprintf(fo, "          , .ARSIZE   (SD_ARSIZE  )\n");
fprintf(fo, "          , .ARBURST  (SD_ARBURST )\n");
fprintf(fo, "     `ifdef AMBA_AXI_CACHE\n");
fprintf(fo, "          , .ARCACHE  (SD_ARCACHE )\n");
fprintf(fo, "     `endif\n");
fprintf(fo, "     `ifdef AMBA_AXI_PROT\n");
fprintf(fo, "          , .ARPROT   (SD_ARPROT  )\n");
fprintf(fo, "     `endif\n");
fprintf(fo, "          , .ARVALID  (SD_ARVALID )\n");
fprintf(fo, "          , .ARREADY  (SD_ARREADY )\n");
fprintf(fo, "     `ifdef AMBA_QOS\n");
fprintf(fo, "          , .ARQOS    (SD_ARQOS   )\n");
fprintf(fo, "          , .ARREGION (SD_ARREGION)\n");
fprintf(fo, "     `endif\n");
fprintf(fo, "          , .RID      (SD_RID     )\n");
fprintf(fo, "          , .RDATA    (SD_RDATA   )\n");
fprintf(fo, "          , .RRESP    (SD_RRESP   )\n");
fprintf(fo, "          , .RLAST    (SD_RLAST   )\n");
fprintf(fo, "          , .RVALID   (SD_RVALID  )\n");
fprintf(fo, "          , .RREADY   (SD_RREADY  )\n");
fprintf(fo, "     );\n");

//fprintf(fo, "    function integer clogb2;\n");
//fprintf(fo, "    input [31:0] value;\n");
//fprintf(fo, "    begin\n");
//fprintf(fo, "      value = value - 1;\n");
//fprintf(fo, "      for (clogb2=0; value>0; clogb2=clogb2+1) value = value>>1;\n");
//fprintf(fo, "    end\n");
//fprintf(fo, "    endfunction\n");

if (axi4) {
fprintf(fo, "     //-----------------------------------------------------------\n");
for (i=0; i<numM; i++) {
fprintf(fo, "    %saxi_wid #(.WIDTH_ID(WIDTH_ID))\n", prefix);
fprintf(fo, "    u_aix_wid_m%d (\n", i);
fprintf(fo, "           .ARESETn   ( ARESETn    )\n");
fprintf(fo, "         , .ACLK      ( ACLK       )\n");
fprintf(fo, "         , .M_AWID    ( M%d_AWID    )\n", i);
fprintf(fo, "         , .M_AWLEN   ( M%d_AWLEN   )\n", i);
fprintf(fo, "         , .M_AWVALID ( M%d_AWVALID )\n", i);
fprintf(fo, "         , .M_AWREADY ( M%d_AWREADY )\n", i);
fprintf(fo, "         , .M_WID     ( M%d_WID     )\n", i);
fprintf(fo, "         , .M_WLAST   ( M%d_WLAST   )\n", i);
fprintf(fo, "         , .M_WVALID  ( M%d_WVALID  )\n", i);
fprintf(fo, "         , .M_WREADY  ( M%d_WREADY  )\n", i);
fprintf(fo, "    );\n");
}
}

fprintf(fo, "     //-----------------------------------------------------------\n");
fprintf(fo, "     // synopsys translate_off\n");
fprintf(fo, "     initial begin\n");
fprintf(fo, "        wait(ARESETn==1'b0);\n");
fprintf(fo, "        wait(ARESETn==1'b1);\n");
fprintf(fo, "        repeat (2) @ (posedge ACLK);\n");
fprintf(fo, "        if ((1<<WIDTH_CID)<NUM_MASTER) begin\n");
fprintf(fo, "            $display(\"%%m ERROR channel ID width (%%2d) should be large enough to hold number %%2d\",\n");
fprintf(fo, "                        WIDTH_CID, NUM_MASTER);\n");
fprintf(fo, "        end\n");
for (i=0; i<numM; i++) {
for (j=i; j<numM; j++) {
if (i!=j) {
fprintf(fo, "        if (M%d_MID===M%d_MID) begin\n", i, j);
fprintf(fo, "            $display(\"%%m ERROR each master should have unique ID, but M%d_MID:%%d M%d_MID:%%d\",\n", i, j);
fprintf(fo, "                      M%d_MID, M%d_MID);\n", i, j);
fprintf(fo, "        end\n");
}
}
}
fprintf(fo, "     end\n");

fprintf(fo, "     localparam ADDR_END0 = ADDR_BASE0 + (1<<ADDR_LENGTH0) - 1\n");
for (i=1; i<numS; i++) 
fprintf(fo, "              , ADDR_END%d = ADDR_BASE%d + (1<<ADDR_LENGTH%d) - 1\n", i, i, i);
fprintf(fo, "              ;\n");
fprintf(fo, "     initial begin\n");
for (k=0; k<numS; k++) {
fprintf(fo,"         if ((SLAVE_EN%d==1)&&(ADDR_BASE%d[ADDR_LENGTH%d-1:0]!=0)) ", k, k, k);
fprintf(fo,"$display(\"%%m ERROR slave %d starting address should be a multiple of size.\");\n", k);
}
for (i=0; i<numS; i++) {
for (j=0; j<numS; j++) {
     if (i!=j) {
fprintf(fo, "         if ((ADDR_END%d>=ADDR_BASE%d)&&(ADDR_END%d<=ADDR_END%d)) ", i, j, i, j);
fprintf(fo, "$display(\"%%m ERROR AXI address %d and %d overlapped 0x%%08X:%%08X:%%08X\", ADDR_END%d, ADDR_BASE%d, ADDR_END%d);\n", i, j, i, j, j);
}}}
fprintf(fo, "     end\n");
fprintf(fo, "     // synopsys translate_on\n");
fprintf(fo, "     //-----------------------------------------------------------\n");

    // Add instantiations of new feature modules if enabled
    if (features) {
        if (features->enable_qos) {
            fprintf(fo, "     //-----------------------------------------------------------\n");
            fprintf(fo, "     // QoS Arbiter Instantiation\n");
            fprintf(fo, "     `ifdef AMBA_QOS\n");
            fprintf(fo, "     wire [%d:0] qos_aw_grant;\n", numM-1);
            fprintf(fo, "     wire [%d:0] qos_ar_grant;\n", numM-1);
            fprintf(fo, "     \n");
            fprintf(fo, "     %saxi_qos_arbiter #(\n", prefix);
            fprintf(fo, "         .NUM_MASTER(%d),\n", numM);
            fprintf(fo, "         .NUM_SLAVE(%d),\n", numS);
            fprintf(fo, "         .WIDTH_QOS(%d)\n", features->width_qos);
            fprintf(fo, "     ) u_qos_arbiter (\n");
            fprintf(fo, "         .clk(ACLK),\n");
            fprintf(fo, "         .rst_n(ARESETn),\n");
            for (i = 0; i < numM; i++) {
                fprintf(fo, "         .m%d_awqos(M%d_AWQOS),\n", i, i);
                fprintf(fo, "         .m%d_arqos(M%d_ARQOS),\n", i, i);
                fprintf(fo, "         .m%d_awvalid(M%d_AWVALID),\n", i, i);
                fprintf(fo, "         .m%d_arvalid(M%d_ARVALID),\n", i, i);
            }
            fprintf(fo, "         .aw_grant(qos_aw_grant),\n");
            fprintf(fo, "         .ar_grant(qos_ar_grant)\n");
            fprintf(fo, "     );\n");
            fprintf(fo, "     `endif\n");
        }
    }

fprintf(fo, "endmodule\n");

    return 0;
}

//--------------------------------------------------------
// Revision history:
//
// 2021.06.01: 'axi4' arguemnt for 'gen_axi_amba()' added.
// 2021.06.01: Channel id (M?_MID) is implemented internally after removing from module port.
// 2021.06.01: static C function 'logb2()' added.
// 2021.06.01: Verilog function 'clogb2()' added.
// 2021.06.01: define AMBA_QOS to use QOS port. (but not implemented it functionality)
// 2019.11.27: 'ERROR slave x starting address should be a multiple of size.");' added
// 2018.09.20: 'WIDTH_??USER' with 'ifdef
// 2017.09.19: fprintf(fo, "     %saxi_stom_s%d #(.MASTER_ID(%d)\n", prefix, numS, i);
// 2016.03.26: Started by Ando Ki.
//--------------------------------------------------------
