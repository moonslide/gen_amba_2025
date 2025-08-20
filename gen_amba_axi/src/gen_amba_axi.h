#ifndef GEN_AMBA_AXI_H
#define GEN_AMBA_AXI_H
//--------------------------------------------------------
// Copyright (c) 2016-2021 by Ando Ki (adki@future-ds.com / andoki@gmail.com)
// The contents and codes along with it are prepared      
// in the hope that it will be useful to understand
// Ando Ki's work, but WITHOUT ANY WARRANTY.              
// The design and code are not guaranteed to work on all systems.   
// While there are no known issues with using the design and code, 
// no technical support will be provided for problems     
// that might arise.                                      
//--------------------------------------------------------

// Structure for advanced features
typedef struct {
    int enable_qos;      // Enable QoS support
    int enable_region;   // Enable REGION support
    int enable_user;     // Enable USER signals
    int enable_prot;     // Enable enhanced PROT support
    int enable_cache;    // Enable CACHE support
    int enable_lock;     // Enable LOCK support
    int enable_firewall; // Enable security firewall
    int enable_cdc;      // Enable CDC support
    int num_clock_domains; // Number of clock domains
    int width_qos;       // QoS signal width (default 4)
    int width_region;    // REGION signal width (default 4)
    int width_user;      // USER signal width (configurable)
    // ACE-Lite support
    int enable_ace_lite; // Enable ACE-Lite coherency
    int width_domain;    // Domain signal width (2 bits)
    int width_snoop_aw;  // AWSNOOP width (3 bits)
    int width_snoop_ar;  // ARSNOOP width (4 bits)
    int width_bar;       // Barrier width (2 bits)
} axi_features_t;

extern int gen_axi_amba( unsigned int numM // num of masters
                       , unsigned int numS // num of slaves
                       , unsigned int widthAD // address width
                       , unsigned int widthDA // data width
                       , char *module
                       , char *prefix
                       , int   axi4 // AXI4 if 1
                       , axi_features_t *features // Advanced features
                       , FILE *fo);
extern int gen_axi_amba_core( unsigned int numM // num of masters
                            , unsigned int numS // num of slaves
                            , unsigned int widthAD // address width
                            , unsigned int widthDA // data width
                            , char *module
                            , char *prefix
                            , int   axi4 // AXI4 if 1
                            , axi_features_t *features // Advanced features
                            , FILE *fo);
extern int gen_axi_mtos( unsigned int num // num of masters
                       , char *prefix
                       , int   axi4 // AXI4 if 1
                       , FILE *fo);
extern int gen_axi_stom( unsigned int num // num of slaves
                       , char *prefix
                       , FILE *fo);
extern int gen_axi_arbiter_mtos( unsigned int num // num of masters
                               , char *prefix
                               , FILE *fo);
extern int gen_axi_arbiter_stom( unsigned int num // num of slaves
                               , char *prefix
                               , FILE *fo);
extern int gen_axi_default_slave( char* prefix
                                , int   axi4 // AXI4 if 1
                                , FILE* fo );

extern int gen_axi_wid( char* prefix
                      , FILE* fo );

// Unified testbench generation
extern void gen_axi_unified_tb( char *prefix
                              , unsigned int num_master
                              , unsigned int num_slave  
                              , unsigned int width_id
                              , unsigned int width_ad
                              , unsigned int width_da
                              , unsigned int *slave_en
                              , unsigned int *addr_base
                              , unsigned int *addr_length
                              , char *filename);

// New feature generation functions
extern int gen_axi_qos_arbiter( unsigned int numM
                              , unsigned int numS
                              , char *prefix
                              , axi_features_t *features
                              , FILE *fo);
extern int gen_axi_qos_connections( unsigned int numM
                                  , unsigned int numS
                                  , char *prefix
                                  , axi_features_t *features
                                  , FILE *fo);
extern int gen_axi_firewall( unsigned int numM
                           , unsigned int numS
                           , char *prefix
                           , axi_features_t *features
                           , FILE *fo);
extern int gen_axi_cdc( unsigned int numM
                      , unsigned int numS
                      , char *prefix
                      , axi_features_t *features
                      , FILE *fo);

// ACE-Lite coherency functions
extern int gen_axi_ace_lite( unsigned int numM
                           , unsigned int numS
                           , char *prefix
                           , axi_features_t *features
                           , FILE *fo);
extern int gen_axi_ace_lite_mport( char *prefix
                                 , char *otype
                                 , axi_features_t *features
                                 , FILE *fo);
extern int gen_axi_ace_lite_sport( char *prefix
                                 , char *otype
                                 , axi_features_t *features
                                 , FILE *fo);

// REGION functions for AXI4
extern int gen_axi_region( unsigned int numM
                         , unsigned int numS
                         , char *prefix
                         , axi_features_t *features
                         , FILE *fo);
extern int gen_axi_region_mport( char *prefix
                               , char *otype
                               , axi_features_t *features
                               , FILE *fo);

// Optimized generator for large matrices
extern int gen_axi_amba_optimized( unsigned int numM
                                 , unsigned int numS
                                 , unsigned int widthAD
                                 , unsigned int widthDA
                                 , char *module
                                 , char *prefix
                                 , int axi4
                                 , axi_features_t *features
                                 , FILE *fo);

// Pure Verilog optimized generator
extern int gen_axi_verilog_optimized( unsigned int numM
                                    , unsigned int numS
                                    , unsigned int widthAD
                                    , unsigned int widthDA
                                    , char *module
                                    , char *prefix
                                    , int axi4
                                    , axi_features_t *features
                                    , FILE *fo);
extern int gen_axi_region_sport( char *prefix
                               , char *otype
                               , axi_features_t *features
                               , FILE *fo);

//--------------------------------------------------------
// Revision history
//
// 2021.06.01: 'axi4' argument for 'gen_aix_amba()'.
// 2016.03.26: Startd by Ando Ki.
//--------------------------------------------------------
#endif
