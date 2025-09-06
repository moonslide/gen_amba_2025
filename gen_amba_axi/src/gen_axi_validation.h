//--------------------------------------------------------
// Copyright (c) 2025 - Enhanced AXI Generator
// Validation and Error Prevention Framework
// Comprehensive validation for ACE-Lite generation
//--------------------------------------------------------
#ifndef GEN_AXI_VALIDATION_H
#define GEN_AXI_VALIDATION_H

#include <stdio.h>
#include <stdlib.h>
#include "gen_amba_axi.h"

//--------------------------------------------------------
// Signal Width Database Types
//--------------------------------------------------------
typedef struct {
    char signal_name[64];
    char width_expr[128];
    char direction[16];  // "input", "output", "wire"
    char module_name[64];
    int line_number;
} signal_def_t;

typedef struct {
    char port_name[64];
    char signal_name[64];
    char width_expr[128];
    int required;  // 1 if required, 0 if optional
} port_connection_t;

//--------------------------------------------------------
// Configuration Matrix Types
//--------------------------------------------------------
typedef struct {
    unsigned int min_masters;
    unsigned int max_masters;
    unsigned int min_slaves;
    unsigned int max_slaves;
    unsigned int min_addr_width;
    unsigned int max_addr_width;
    unsigned int min_data_width;
    unsigned int max_data_width;
    char config_name[64];
    int requires_ace_lite;
    int requires_firewall;
    int requires_user;
} config_matrix_t;

//--------------------------------------------------------
// Validation Function Prototypes
//--------------------------------------------------------

// Port Connection Validation
int validate_port_connections(const char* module_name, port_connection_t connections[], int num_connections, FILE* fo);
int auto_validate_port_widths(const char* module_name, const char* instance_name, FILE* fo);
void generate_port_connection_checks(const char* module_name, FILE* fo);

// Signal Width Consistency
int register_signal_width(const char* signal_name, const char* width_expr, const char* direction, const char* module_name, int line_number);
int validate_signal_consistency(FILE* error_log);
void clear_signal_database(void);
int check_cross_module_signals(FILE* error_log);

// Configuration Matrix Validation
int validate_configuration_matrix(unsigned int numM, unsigned int numS, unsigned int widthAD, unsigned int widthDA, axi_features_t* features);
int check_ace_lite_constraints(unsigned int numM, unsigned int numS, axi_features_t* features);
int validate_feature_dependencies(axi_features_t* features);

// RTL Self-Validation Generation
void generate_rtl_parameter_checks(unsigned int numM, unsigned int numS, unsigned int widthAD, unsigned int widthDA, axi_features_t* features, FILE* fo);
void generate_rtl_signal_assertions(const char* module_name, FILE* fo);
void generate_rtl_protocol_checks(axi_features_t* features, FILE* fo);

// Enhanced Error Reporting
void validation_error(const char* context, const char* module_name, int line_number, const char* format, ...);
void validation_warning(const char* context, const char* module_name, int line_number, const char* format, ...);
void validation_info(const char* context, const char* format, ...);

// Utility Functions
int calculate_required_width(unsigned int value);
int is_power_of_two(unsigned int value);
const char* get_width_expression(const char* signal_name);

#endif // GEN_AXI_VALIDATION_H