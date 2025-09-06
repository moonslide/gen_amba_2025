//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// Validation and Error Prevention Framework Implementation
//--------------------------------------------------------
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <math.h>
#include "gen_axi_validation.h"
#include "gen_amba_axi.h"

//--------------------------------------------------------
// Global Signal Width Database
//--------------------------------------------------------
static signal_def_t signal_database[1024];
static int signal_count = 0;
static FILE* validation_log = NULL;

//--------------------------------------------------------
// Configuration Matrix Definitions
//--------------------------------------------------------
static const config_matrix_t valid_configs[] = {
    // Basic AXI4 configurations
    {2, 8, 2, 8, 8, 64, 32, 1024, "AXI4_BASIC", 0, 0, 0},
    {8, 16, 8, 16, 16, 64, 64, 1024, "AXI4_STANDARD", 0, 0, 0},
    {16, 32, 16, 32, 32, 64, 128, 1024, "AXI4_LARGE", 0, 0, 0},
    {32, 64, 32, 64, 32, 64, 256, 1024, "AXI4_ULTRA", 0, 0, 0},
    
    // ACE-Lite configurations
    {2, 8, 2, 8, 32, 64, 32, 512, "ACE_LITE_BASIC", 1, 0, 1},
    {8, 16, 8, 16, 32, 64, 64, 512, "ACE_LITE_STANDARD", 1, 1, 1},
    {16, 32, 16, 32, 32, 64, 64, 1024, "ACE_LITE_LARGE", 1, 1, 1},
    {32, 64, 32, 64, 32, 64, 64, 1024, "ACE_LITE_ULTRA", 1, 1, 1},
};

static const int num_valid_configs = sizeof(valid_configs) / sizeof(config_matrix_t);

//--------------------------------------------------------
// Enhanced Error Reporting
//--------------------------------------------------------
void validation_error(const char* context, const char* module_name, int line_number, const char* format, ...) {
    va_list args;
    fprintf(stderr, "ERROR [%s]: ", context);
    if (module_name) fprintf(stderr, "Module '%s' ", module_name);
    if (line_number > 0) fprintf(stderr, "Line %d: ", line_number);
    
    va_start(args, format);
    vfprintf(stderr, format, args);
    va_end(args);
    fprintf(stderr, "\n");
    
    if (validation_log) {
        fprintf(validation_log, "ERROR [%s]: ", context);
        if (module_name) fprintf(validation_log, "Module '%s' ", module_name);
        if (line_number > 0) fprintf(validation_log, "Line %d: ", line_number);
        va_start(args, format);
        vfprintf(validation_log, format, args);
        va_end(args);
        fprintf(validation_log, "\n");
        fflush(validation_log);
    }
}

void validation_warning(const char* context, const char* module_name, int line_number, const char* format, ...) {
    va_list args;
    fprintf(stderr, "WARNING [%s]: ", context);
    if (module_name) fprintf(stderr, "Module '%s' ", module_name);
    if (line_number > 0) fprintf(stderr, "Line %d: ", line_number);
    
    va_start(args, format);
    vfprintf(stderr, format, args);
    va_end(args);
    fprintf(stderr, "\n");
    
    if (validation_log) {
        fprintf(validation_log, "WARNING [%s]: ", context);
        if (module_name) fprintf(validation_log, "Module '%s' ", module_name);
        if (line_number > 0) fprintf(validation_log, "Line %d: ", line_number);
        va_start(args, format);
        vfprintf(validation_log, format, args);
        va_end(args);
        fprintf(validation_log, "\n");
        fflush(validation_log);
    }
}

void validation_info(const char* context, const char* format, ...) {
    va_list args;
    fprintf(stdout, "INFO [%s]: ", context);
    va_start(args, format);
    vfprintf(stdout, format, args);
    va_end(args);
    fprintf(stdout, "\n");
    
    if (validation_log) {
        fprintf(validation_log, "INFO [%s]: ", context);
        va_start(args, format);
        vfprintf(validation_log, format, args);
        va_end(args);
        fprintf(validation_log, "\n");
        fflush(validation_log);
    }
}

//--------------------------------------------------------
// Utility Functions
//--------------------------------------------------------
int calculate_required_width(unsigned int value) {
    if (value <= 1) return 1;
    return (int)ceil(log2(value));
}

int is_power_of_two(unsigned int value) {
    return (value != 0) && ((value & (value - 1)) == 0);
}

//--------------------------------------------------------
// Signal Width Database Management
//--------------------------------------------------------
int register_signal_width(const char* signal_name, const char* width_expr, const char* direction, const char* module_name, int line_number) {
    if (signal_count >= 1024) {
        validation_error("SIGNAL_DB", NULL, 0, "Signal database overflow (max 1024 signals)");
        return -1;
    }
    
    signal_def_t* sig = &signal_database[signal_count];
    strncpy(sig->signal_name, signal_name, sizeof(sig->signal_name) - 1);
    strncpy(sig->width_expr, width_expr, sizeof(sig->width_expr) - 1);
    strncpy(sig->direction, direction, sizeof(sig->direction) - 1);
    strncpy(sig->module_name, module_name, sizeof(sig->module_name) - 1);
    sig->line_number = line_number;
    
    signal_count++;
    validation_info("SIGNAL_REG", "Registered %s signal '%s' with width '%s' in module '%s'", 
                   direction, signal_name, width_expr, module_name);
    return 0;
}

void clear_signal_database(void) {
    signal_count = 0;
    validation_info("SIGNAL_DB", "Signal database cleared");
}

int validate_signal_consistency(FILE* error_log) {
    int errors = 0;
    validation_log = error_log;
    
    validation_info("SIGNAL_CHECK", "Validating signal consistency across %d signals", signal_count);
    
    // Check for signal name conflicts with different widths
    for (int i = 0; i < signal_count; i++) {
        for (int j = i + 1; j < signal_count; j++) {
            if (strcmp(signal_database[i].signal_name, signal_database[j].signal_name) == 0) {
                if (strcmp(signal_database[i].width_expr, signal_database[j].width_expr) != 0) {
                    validation_error("SIGNAL_WIDTH", 
                                   signal_database[i].module_name, 
                                   signal_database[i].line_number,
                                   "Signal '%s' has inconsistent widths: '%s' vs '%s' (module %s:%d)",
                                   signal_database[i].signal_name,
                                   signal_database[i].width_expr,
                                   signal_database[j].width_expr,
                                   signal_database[j].module_name,
                                   signal_database[j].line_number);
                    errors++;
                }
            }
        }
    }
    
    return errors;
}

//--------------------------------------------------------
// Configuration Matrix Validation
//--------------------------------------------------------
int validate_configuration_matrix(unsigned int numM, unsigned int numS, unsigned int widthAD, unsigned int widthDA, axi_features_t* features) {
    validation_info("CONFIG_MATRIX", "Validating configuration: M%d S%d AD%d DA%d", numM, numS, widthAD, widthDA);
    
    // Find matching configuration
    const config_matrix_t* matching_config = NULL;
    for (int i = 0; i < num_valid_configs; i++) {
        const config_matrix_t* config = &valid_configs[i];
        if (numM >= config->min_masters && numM <= config->max_masters &&
            numS >= config->min_slaves && numS <= config->max_slaves &&
            widthAD >= config->min_addr_width && widthAD <= config->max_addr_width &&
            widthDA >= config->min_data_width && widthDA <= config->max_data_width) {
            
            // Check feature requirements
            if (config->requires_ace_lite && !features->enable_ace_lite) continue;
            if (config->requires_firewall && !features->enable_firewall) continue;
            if (config->requires_user && !features->enable_user) continue;
            
            matching_config = config;
            break;
        }
    }
    
    if (!matching_config) {
        validation_error("CONFIG_MATRIX", NULL, 0, 
                        "No valid configuration found for M%d S%d AD%d DA%d with current features", 
                        numM, numS, widthAD, widthDA);
        return -1;
    }
    
    validation_info("CONFIG_MATRIX", "Configuration validated as '%s'", matching_config->config_name);
    return 0;
}

int check_ace_lite_constraints(unsigned int numM, unsigned int numS, axi_features_t* features) {
    int errors = 0;
    
    if (!features->enable_ace_lite) return 0;
    
    validation_info("ACE_LITE_CHECK", "Validating ACE-Lite specific constraints");
    
    // ACE-Lite requires minimum 2 masters
    if (numM < 2) {
        validation_error("ACE_LITE", NULL, 0, "ACE-Lite requires minimum 2 masters, got %d", numM);
        errors++;
    }
    
    // ACE-Lite requires cache signals
    if (!features->enable_cache) {
        validation_error("ACE_LITE", NULL, 0, "ACE-Lite requires cache signals enabled");
        errors++;
    }
    
    // ACE-Lite typically requires USER signals for sideband coherency info
    if (!features->enable_user) {
        validation_warning("ACE_LITE", NULL, 0, "ACE-Lite works best with USER signals enabled for coherency metadata");
    }
    
    // Check SD_USER signal widths are reasonable
    if (features->width_sd_awuser > 32 || features->width_sd_awuser < 1) {
        validation_error("ACE_LITE", NULL, 0, "SD_AWUSER width %d is outside valid range [1-32]", features->width_sd_awuser);
        errors++;
    }
    
    // Similar checks for other SD_USER signals
    if (features->width_sd_wuser > 32 || features->width_sd_wuser < 1) {
        validation_error("ACE_LITE", NULL, 0, "SD_WUSER width %d is outside valid range [1-32]", features->width_sd_wuser);
        errors++;
    }
    
    return errors;
}

int validate_feature_dependencies(axi_features_t* features) {
    int errors = 0;
    
    validation_info("FEATURE_DEP", "Validating feature dependencies");
    
    // QoS requires AXI4
    if (features->enable_qos && !features->enable_cache) {
        validation_warning("FEATURE_DEP", NULL, 0, "QoS typically works best with cache signals enabled");
    }
    
    // Firewall requires address width >= 32 for reasonable memory ranges
    if (features->enable_firewall) {
        validation_info("FEATURE_DEP", "Firewall security feature enabled");
    }
    
    // CDC requires multiple clock domains
    if (features->enable_cdc && features->num_clock_domains < 2) {
        validation_error("FEATURE_DEP", NULL, 0, "CDC enabled but only %d clock domain specified", features->num_clock_domains);
        errors++;
    }
    
    return errors;
}

//--------------------------------------------------------
// RTL Self-Validation Generation
//--------------------------------------------------------
void generate_rtl_parameter_checks(unsigned int numM, unsigned int numS, unsigned int widthAD, unsigned int widthDA, axi_features_t* features, FILE* fo) {
    fprintf(fo, "\n    //--------------------------------------------------------\n");
    fprintf(fo, "    // Auto-generated Parameter Validation Checks\n");
    fprintf(fo, "    //--------------------------------------------------------\n");
    fprintf(fo, "    initial begin : parameter_validation\n");
    fprintf(fo, "        // Master/Slave count validation\n");
    fprintf(fo, "        if (NUM_MASTER < 2) begin\n");
    fprintf(fo, "            $error(\"[PARAM_CHECK] NUM_MASTER (%0d) must be >= 2\", NUM_MASTER);\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "        if (NUM_SLAVE < 1) begin\n");
    fprintf(fo, "            $error(\"[PARAM_CHECK] NUM_SLAVE (%0d) must be >= 1\", NUM_SLAVE);\n");
    fprintf(fo, "        end\n\n");
    
    fprintf(fo, "        // Address/Data width validation\n");
    fprintf(fo, "        if (WIDTH_AD < 8 || WIDTH_AD > 64) begin\n");
    fprintf(fo, "            $error(\"[PARAM_CHECK] WIDTH_AD (%0d) must be 8-64 bits\", WIDTH_AD);\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "        if (WIDTH_DA < 32 || WIDTH_DA > 1024) begin\n");
    fprintf(fo, "            $error(\"[PARAM_CHECK] WIDTH_DA (%0d) must be 32-1024 bits\", WIDTH_DA);\n");
    fprintf(fo, "        end\n");
    fprintf(fo, "        if ((WIDTH_DA & (WIDTH_DA-1)) != 0) begin\n");
    fprintf(fo, "            $error(\"[PARAM_CHECK] WIDTH_DA (%0d) must be power of 2\", WIDTH_DA);\n");
    fprintf(fo, "        end\n\n");
    
    if (features && features->enable_ace_lite) {
        fprintf(fo, "        // ACE-Lite specific validation\n");
        fprintf(fo, "        `ifdef AMBA_ACE_LITE\n");
        fprintf(fo, "        if (CONFLICT_COUNT_WIDTH < $clog2(NUM_MASTER)) begin\n");
        fprintf(fo, "            $warning(\"[ACE_LITE_CHECK] CONFLICT_COUNT_WIDTH (%0d) may be insufficient for NUM_MASTER (%0d)\", CONFLICT_COUNT_WIDTH, NUM_MASTER);\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "        if (MAINT_PRIORITY_WIDTH < 2) begin\n");
        fprintf(fo, "            $error(\"[ACE_LITE_CHECK] MAINT_PRIORITY_WIDTH (%0d) must be >= 2\", MAINT_PRIORITY_WIDTH);\n");
        fprintf(fo, "        end\n");
        fprintf(fo, "        `endif\n\n");
    }
    
    fprintf(fo, "        $display(\"[PARAM_CHECK] Parameter validation completed successfully\");\n");
    fprintf(fo, "    end\n\n");
}

void generate_rtl_signal_assertions(const char* module_name, FILE* fo) {
    fprintf(fo, "    //--------------------------------------------------------\n");
    fprintf(fo, "    // Auto-generated Signal Assertions for %s\n", module_name);
    fprintf(fo, "    //--------------------------------------------------------\n");
    fprintf(fo, "    `ifdef ENABLE_ASSERTIONS\n");
    
    if (strstr(module_name, "ace_lite")) {
        fprintf(fo, "    // ACE-Lite protocol assertions\n");
        fprintf(fo, "    property ace_lite_awsnoop_valid;\n");
        fprintf(fo, "        @(posedge clk) disable iff (!rst_n)\n");
        fprintf(fo, "        $onehot0({awsnoop == 3'b000, awsnoop == 3'b001, awsnoop == 3'b010, awsnoop == 3'b100});\n");
        fprintf(fo, "    endproperty\n");
        fprintf(fo, "    assert property (ace_lite_awsnoop_valid) else $error(\"[ASSERTION] Invalid AWSNOOP value\");\n\n");
        
        fprintf(fo, "    // Coherency state consistency\n");
        fprintf(fo, "    property coherent_transaction_domain;\n");
        fprintf(fo, "        @(posedge clk) disable iff (!rst_n)\n");
        fprintf(fo, "        (awvalid && awdomain != 2'b00) |-> (awsnoop != 3'b000);\n");
        fprintf(fo, "    endproperty\n");
        fprintf(fo, "    assert property (coherent_transaction_domain) else $error(\"[ASSERTION] Non-shareable domain with coherent snoop\");\n\n");
    }
    
    fprintf(fo, "    `endif // ENABLE_ASSERTIONS\n\n");
}

void generate_rtl_protocol_checks(axi_features_t* features, FILE* fo) {
    fprintf(fo, "    //--------------------------------------------------------\n");
    fprintf(fo, "    // Auto-generated Protocol Compliance Checks\n");
    fprintf(fo, "    //--------------------------------------------------------\n");
    fprintf(fo, "    `ifdef ENABLE_PROTOCOL_CHECKS\n");
    
    if (features && features->enable_ace_lite) {
        fprintf(fo, "    // ACE-Lite 4KB boundary check\n");
        fprintf(fo, "    always @(posedge ACLK) begin\n");
        fprintf(fo, "        if (ARESETn) begin\n");
        for (int i = 0; i < 4; i++) { // Example for first 4 masters
            fprintf(fo, "            if (M%d_AWVALID && M%d_AWREADY) begin\n", i, i);
            fprintf(fo, "                if ((M%d_AWADDR & 12'hFFF) + (M%d_AWLEN + 1) * (1 << M%d_AWSIZE) > 4096) begin\n", i, i, i);
            fprintf(fo, "                    $error(\"[PROTOCOL_CHECK] Master %d transaction crosses 4KB boundary at address 0x%%h\", M%d_AWADDR);\n", i, i);
            fprintf(fo, "                end\n");
            fprintf(fo, "            end\n");
        }
        fprintf(fo, "        end\n");
        fprintf(fo, "    end\n\n");
    }
    
    fprintf(fo, "    `endif // ENABLE_PROTOCOL_CHECKS\n\n");
}

//--------------------------------------------------------
// Port Connection Validation
//--------------------------------------------------------
int validate_port_connections(const char* module_name, port_connection_t connections[], int num_connections, FILE* fo) {
    int errors = 0;
    
    validation_info("PORT_CHECK", "Validating %d port connections for module %s", num_connections, module_name);
    
    fprintf(fo, "    // Auto-generated port connection validation for %s\n", module_name);
    fprintf(fo, "    initial begin : port_validation_%s\n", module_name);
    
    for (int i = 0; i < num_connections; i++) {
        port_connection_t* conn = &connections[i];
        if (conn->required && strlen(conn->signal_name) == 0) {
            validation_error("PORT_CHECK", module_name, 0, "Required port '%s' not connected", conn->port_name);
            errors++;
        }
        
        // Generate runtime width check
        fprintf(fo, "        // Port %s width validation\n", conn->port_name);
        fprintf(fo, "        if ($bits(%s) != (%s)) begin\n", conn->signal_name, conn->width_expr);
        fprintf(fo, "            $error(\"[PORT_WIDTH] Port %s expects %%0d bits, got %%0d bits\", (%s), $bits(%s));\n", 
               conn->port_name, conn->width_expr, conn->signal_name);
        fprintf(fo, "        end\n");
    }
    
    fprintf(fo, "    end\n\n");
    return errors;
}

const char* get_width_expression(const char* signal_name) {
    for (int i = 0; i < signal_count; i++) {
        if (strcmp(signal_database[i].signal_name, signal_name) == 0) {
            return signal_database[i].width_expr;
        }
    }
    return "1"; // Default to 1-bit if not found
}