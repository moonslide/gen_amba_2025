//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// ACE-Lite Signal Arbiter - Resolves signal conflicts between coherency modules
// Provides proper signal arbitration and module isolation
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include "../../gen_amba_axi.h"
#include "../../gen_axi_utils.h"

//--------------------------------------------------------
// Generate ACE-Lite signal arbiter module
// Resolves conflicts between coherency controller, DVM controller, 
// system coordinator, and other ACE-Lite modules
//--------------------------------------------------------
int gen_ace_lite_signal_arbiter(unsigned int numM, unsigned int numS, 
                                 unsigned int widthAD, unsigned int widthDA,
                                 char *prefix, axi_features_t *features, FILE *fo)
{
    int i;
    
    if (!features || !features->enable_ace_lite) return 0;
    
    fprintf(fo, "\n//---------------------------------------------------------------------------\n");
    fprintf(fo, "// ACE-Lite Signal Arbiter\n");
    fprintf(fo, "// Resolves signal conflicts between multiple coherency modules\n");
    fprintf(fo, "//---------------------------------------------------------------------------\n");
    fprintf(fo, "module %sace_lite_signal_arbiter\n", prefix);
    fprintf(fo, "      #(parameter NUM_MASTER = %d\n", numM);
    fprintf(fo, "              , NUM_SLAVE  = %d\n", numS);
    fprintf(fo, "              , WIDTH_ID   = 4\n");
    fprintf(fo, "              , WIDTH_AD   = 32\n");
    fprintf(fo, "              , WIDTH_DA   = 32)\n");
    fprintf(fo, "(\n");
    fprintf(fo, "      input  wire                       clk\n");
    fprintf(fo, "    , input  wire                       rst_n\n");
    
    // Input signals from different ACE-Lite modules
    fprintf(fo, "    \n");
    fprintf(fo, "    // Input signals from coherency controller\n");
    fprintf(fo, "    , input  wire                       coherency_ctrl_active\n");
    fprintf(fo, "    , input  wire                       coherency_ctrl_snoop_broadcast\n");
    fprintf(fo, "    , input  wire [NUM_MASTER-1:0]      coherency_ctrl_master_coherent\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Input signals from DVM controller\n");
    fprintf(fo, "    , input  wire                       dvm_ctrl_active\n");
    fprintf(fo, "    , input  wire                       dvm_ctrl_broadcast\n");
    fprintf(fo, "    , input  wire [NUM_MASTER-1:0]      dvm_ctrl_master_sync\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Input signals from system coordinator\n");
    fprintf(fo, "    , input  wire                       sys_coord_active\n");
    fprintf(fo, "    , input  wire                       sys_coord_barrier\n");
    fprintf(fo, "    , input  wire [NUM_MASTER-1:0]      sys_coord_master_sync\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Input signals from cache operations\n");
    fprintf(fo, "    , input  wire                       cache_ops_active\n");
    fprintf(fo, "    , input  wire [NUM_MASTER-1:0]      cache_ops_master_maint\n");
    fprintf(fo, "    \n");
    fprintf(fo, "    // Input signals from exclusive monitor\n");
    fprintf(fo, "    , input  wire                       exclusive_mon_active\n");
    fprintf(fo, "    , input  wire [NUM_MASTER-1:0]      exclusive_mon_master_exclusive\n");
    
    // Arbitrated output signals
    fprintf(fo, "    \n");
    fprintf(fo, "    // Arbitrated output signals (single drivers)\n");
    fprintf(fo, "    , output reg                        coherency_active\n");
    fprintf(fo, "    , output reg                        snoop_broadcast_active\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]      master_coherent_transaction\n");
    fprintf(fo, "    , output reg                        barrier_active\n");
    fprintf(fo, "    , output reg                        dvm_operation_active\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]      master_sync_required\n");
    fprintf(fo, "    , output reg                        cache_maintenance_active\n");
    fprintf(fo, "    , output reg  [NUM_MASTER-1:0]      exclusive_access_active\n");
    
    // Status and control outputs
    fprintf(fo, "    , output reg  [2:0]                 active_module_id\n");
    fprintf(fo, "    , output reg                        conflict_detected\n");
    fprintf(fo, "    \n");
    fprintf(fo, ");\n\n");
    
    // Active module ID encodings
    fprintf(fo, "    // Active module ID encodings\n");
    fprintf(fo, "    localparam [2:0] MODULE_IDLE         = 3'b000;\n");
    fprintf(fo, "    localparam [2:0] MODULE_COHERENCY    = 3'b001;\n");
    fprintf(fo, "    localparam [2:0] MODULE_DVM          = 3'b010;\n");
    fprintf(fo, "    localparam [2:0] MODULE_SYSTEM       = 3'b011;\n");
    fprintf(fo, "    localparam [2:0] MODULE_CACHE_OPS    = 3'b100;\n");
    fprintf(fo, "    localparam [2:0] MODULE_EXCLUSIVE    = 3'b101;\n");
    fprintf(fo, "    localparam [2:0] MODULE_CONFLICT     = 3'b111;\n\n");
    
    // Priority encoding - higher priority modules take precedence
    fprintf(fo, "    // Module priority encoding (0 = highest priority)\n");
    fprintf(fo, "    wire [2:0] module_priority [0:5];\n");
    fprintf(fo, "    assign module_priority[0] = 3'd0;  // DVM (highest priority)\n");
    fprintf(fo, "    assign module_priority[1] = 3'd1;  // System coordinator\n");
    fprintf(fo, "    assign module_priority[2] = 3'd2;  // Coherency controller\n");
    fprintf(fo, "    assign module_priority[3] = 3'd3;  // Cache operations\n");
    fprintf(fo, "    assign module_priority[4] = 3'd4;  // Exclusive monitor\n");
    fprintf(fo, "    assign module_priority[5] = 3'd7;  // Idle (lowest priority)\n\n");
    
    // Signal arbitration logic
    fprintf(fo, "    // Signal arbitration logic\n");
    fprintf(fo, "    always @(posedge clk or negedge rst_n) begin\n");
    fprintf(fo, "        if (!rst_n) begin\n");
    fprintf(fo, "            coherency_active <= 1'b0;\n");
    fprintf(fo, "            snoop_broadcast_active <= 1'b0;\n");
    fprintf(fo, "            master_coherent_transaction <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            barrier_active <= 1'b0;\n");
    fprintf(fo, "            dvm_operation_active <= 1'b0;\n");
    fprintf(fo, "            master_sync_required <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            cache_maintenance_active <= 1'b0;\n");
    fprintf(fo, "            exclusive_access_active <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            active_module_id <= MODULE_IDLE;\n");
    fprintf(fo, "            conflict_detected <= 1'b0;\n");
    fprintf(fo, "        end else begin\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Conflict detection\n");
    fprintf(fo, "            reg [4:0] active_modules;\n");
    fprintf(fo, "            active_modules = {exclusive_mon_active, cache_ops_active, sys_coord_active, dvm_ctrl_active, coherency_ctrl_active};\n");
    fprintf(fo, "            conflict_detected <= (active_modules != 5'b00000) && (active_modules & (active_modules - 1)) != 5'b00000;\n");
    fprintf(fo, "            \n");
    fprintf(fo, "            // Priority-based arbitration\n");
    fprintf(fo, "            if (dvm_ctrl_active) begin\n");
    fprintf(fo, "                // DVM controller has highest priority\n");
    fprintf(fo, "                active_module_id <= MODULE_DVM;\n");
    fprintf(fo, "                coherency_active <= dvm_ctrl_active;\n");
    fprintf(fo, "                snoop_broadcast_active <= dvm_ctrl_broadcast;\n");
    fprintf(fo, "                master_coherent_transaction <= dvm_ctrl_master_sync;\n");
    fprintf(fo, "                barrier_active <= 1'b0;\n");
    fprintf(fo, "                dvm_operation_active <= dvm_ctrl_active;\n");
    fprintf(fo, "                master_sync_required <= dvm_ctrl_master_sync;\n");
    fprintf(fo, "                cache_maintenance_active <= 1'b0;\n");
    fprintf(fo, "                exclusive_access_active <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            end else if (sys_coord_active) begin\n");
    fprintf(fo, "                // System coordinator has second priority\n");
    fprintf(fo, "                active_module_id <= MODULE_SYSTEM;\n");
    fprintf(fo, "                coherency_active <= sys_coord_active;\n");
    fprintf(fo, "                snoop_broadcast_active <= 1'b0;\n");
    fprintf(fo, "                master_coherent_transaction <= sys_coord_master_sync;\n");
    fprintf(fo, "                barrier_active <= sys_coord_barrier;\n");
    fprintf(fo, "                dvm_operation_active <= 1'b0;\n");
    fprintf(fo, "                master_sync_required <= sys_coord_master_sync;\n");
    fprintf(fo, "                cache_maintenance_active <= 1'b0;\n");
    fprintf(fo, "                exclusive_access_active <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            end else if (coherency_ctrl_active) begin\n");
    fprintf(fo, "                // Coherency controller has third priority\n");
    fprintf(fo, "                active_module_id <= MODULE_COHERENCY;\n");
    fprintf(fo, "                coherency_active <= coherency_ctrl_active;\n");
    fprintf(fo, "                snoop_broadcast_active <= coherency_ctrl_snoop_broadcast;\n");
    fprintf(fo, "                master_coherent_transaction <= coherency_ctrl_master_coherent;\n");
    fprintf(fo, "                barrier_active <= 1'b0;\n");
    fprintf(fo, "                dvm_operation_active <= 1'b0;\n");
    fprintf(fo, "                master_sync_required <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                cache_maintenance_active <= 1'b0;\n");
    fprintf(fo, "                exclusive_access_active <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            end else if (cache_ops_active) begin\n");
    fprintf(fo, "                // Cache operations has fourth priority\n");
    fprintf(fo, "                active_module_id <= MODULE_CACHE_OPS;\n");
    fprintf(fo, "                coherency_active <= cache_ops_active;\n");
    fprintf(fo, "                snoop_broadcast_active <= 1'b0;\n");
    fprintf(fo, "                master_coherent_transaction <= cache_ops_master_maint;\n");
    fprintf(fo, "                barrier_active <= 1'b0;\n");
    fprintf(fo, "                dvm_operation_active <= 1'b0;\n");
    fprintf(fo, "                master_sync_required <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                cache_maintenance_active <= cache_ops_active;\n");
    fprintf(fo, "                exclusive_access_active <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            end else if (exclusive_mon_active) begin\n");
    fprintf(fo, "                // Exclusive monitor has lowest priority\n");
    fprintf(fo, "                active_module_id <= MODULE_EXCLUSIVE;\n");
    fprintf(fo, "                coherency_active <= exclusive_mon_active;\n");
    fprintf(fo, "                snoop_broadcast_active <= 1'b0;\n");
    fprintf(fo, "                master_coherent_transaction <= exclusive_mon_master_exclusive;\n");
    fprintf(fo, "                barrier_active <= 1'b0;\n");
    fprintf(fo, "                dvm_operation_active <= 1'b0;\n");
    fprintf(fo, "                master_sync_required <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                cache_maintenance_active <= 1'b0;\n");
    fprintf(fo, "                exclusive_access_active <= exclusive_mon_master_exclusive;\n");
    fprintf(fo, "            end else begin\n");
    fprintf(fo, "                // All modules idle\n");
    fprintf(fo, "                active_module_id <= MODULE_IDLE;\n");
    fprintf(fo, "                coherency_active <= 1'b0;\n");
    fprintf(fo, "                snoop_broadcast_active <= 1'b0;\n");
    fprintf(fo, "                master_coherent_transaction <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                barrier_active <= 1'b0;\n");
    fprintf(fo, "                dvm_operation_active <= 1'b0;\n");
    fprintf(fo, "                master_sync_required <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "                cache_maintenance_active <= 1'b0;\n");
    fprintf(fo, "                exclusive_access_active <= {NUM_MASTER{1'b0}};\n");
    fprintf(fo, "            end\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "    end\n\n");
    
    fprintf(fo, "endmodule\n");
    
    return 0;
}