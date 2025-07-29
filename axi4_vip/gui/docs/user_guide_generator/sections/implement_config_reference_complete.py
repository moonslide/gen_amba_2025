#!/usr/bin/env python3
"""
Implement COMPLETE Configuration Reference section (pages 74-77) with full detailed content
NO PLACEHOLDERS - every page fully implemented with real information
4 pages of comprehensive configuration reference content
"""

def create_complete_configuration_reference_section(pdf_generator, pdf):
    """Complete Configuration Reference section - 4 pages of detailed content"""
    
    # Page 74: Configuration Reference Overview
    config_overview = """
This section provides a comprehensive reference for all configuration parameters
available in the AMBA Bus Matrix Configuration Tool. Parameters are organized
by category with detailed descriptions, valid ranges, and usage examples.

CONFIGURATION CATEGORIES:

Global System Parameters:
• Bus protocol selection (AXI4, AXI3, AHB, APB)
• System-wide data and address widths
• Clock domain configuration
• Reset scheme selection
• Debug and trace settings

Master Configuration:
• Master identification and naming
• Outstanding transaction limits
• ID width and allocation
• QoS priority settings
• User signal configuration
• Protocol-specific features

Slave Configuration:
• Slave identification and addressing
• Memory map and address decoding
• Response characteristics
• Error handling configuration
• Security attributes
• Performance settings

Interconnect Configuration:
• Arbitration algorithms and policies
• Pipeline depth and timing
• Bandwidth allocation
• Starvation prevention
• Multi-clock domain support
• Power management features

Advanced Features:
• TrustZone security configuration
• Exclusive access support
• Cache coherency settings
• Debug and trace interfaces
• Custom protocol extensions

CONFIGURATION FILE FORMATS:

JSON Configuration Format:
The tool supports JSON configuration files for batch processing and
version control integration:

{
  "project_info": {
    "name": "automotive_soc",
    "version": "2.1.0",
    "description": "Main SoC interconnect for automotive platform"
  },
  "global_config": {
    "protocol": "AXI4",
    "data_width": 128,
    "addr_width": 40,
    "endianness": "little"
  },
  "masters": [...],
  "slaves": [...],
  "interconnect": {...}
}

XML Configuration Format:
XML format is supported for integration with other EDA tools:

<?xml version="1.0" encoding="UTF-8"?>
<bus_matrix_config version="2.0">
  <project name="automotive_soc" version="2.1.0"/>
  <global protocol="AXI4" data_width="128" addr_width="40"/>
  <masters>
    <master id="0" name="cortex_a78_core0"/>
  </masters>
</bus_matrix_config>

GUI Configuration Storage:
GUI configurations are automatically saved in project files with
.bmcfg extension containing all design parameters and GUI state.

PARAMETER VALIDATION:

All configuration parameters undergo comprehensive validation:
• Range checking for numerical values
• Consistency checking across related parameters
• Protocol compliance verification
• Resource conflict detection
• Performance feasibility analysis

The tool provides detailed error messages and suggestions for
resolving configuration issues, ensuring robust and reliable
system generation.
"""
    pdf_generator.create_text_page(pdf, "6. Configuration Reference", "Overview", config_overview)
    
    # Page 75: Global and Master Configuration Parameters
    global_master_config = """
6.1 Global and Master Configuration Parameters

GLOBAL SYSTEM PARAMETERS:

Protocol Selection:
Parameter: global.protocol
Type: enumeration
Valid Values: "AXI4", "AXI3", "AHB", "APB"
Default: "AXI4"
Description: Primary bus protocol for the interconnect
Example: "protocol": "AXI4"

Data Width Configuration:
Parameter: global.data_width
Type: integer
Valid Values: 8, 16, 32, 64, 128, 256, 512, 1024
Default: 32
Units: bits
Description: System data bus width in bits
Constraints: Must be power of 2, minimum 8 bits
Example: "data_width": 128

Address Width Configuration:
Parameter: global.addr_width  
Type: integer
Valid Values: 12-64
Default: 32
Units: bits
Description: System address width determining addressable space
Memory Space: 2^addr_width bytes total addressable
Example: "addr_width": 40  // 1TB addressable space

Clock Configuration:
Parameter: global.clock_domains
Type: array of objects
Description: Multi-clock domain configuration
Schema: {
  "name": string,
  "frequency_mhz": number,
  "source": string,
  "async_reset": boolean
}
Example:
"clock_domains": [
  {"name": "cpu_clk", "frequency_mhz": 800.0, "source": "pll0", "async_reset": true},
  {"name": "ddr_clk", "frequency_mhz": 400.0, "source": "pll1", "async_reset": true}
]

Reset Configuration:
Parameter: global.reset_scheme
Type: enumeration
Valid Values: "sync", "async", "mixed"
Default: "async"
Description: System reset methodology
- sync: Synchronous reset throughout system
- async: Asynchronous reset, synchronous deassertion
- mixed: Per-domain reset configuration

MASTER CONFIGURATION PARAMETERS:

Master Identification:
Parameter: masters[i].id
Type: integer
Valid Values: 0 to (NUM_MASTERS-1)
Description: Unique master identifier
Constraints: Must be sequential starting from 0
Example: "id": 0

Master Name:
Parameter: masters[i].name
Type: string
Valid Values: Alphanumeric with underscores
Max Length: 64 characters
Description: Human-readable master name
Example: "name": "cortex_a78_core0"

Master Type:
Parameter: masters[i].type
Type: enumeration
Valid Values: "cpu", "dma", "gpu", "dsp", "accelerator", "debug", "custom"
Default: "custom"
Description: Master functional category for optimization hints
Example: "type": "cpu"

Outstanding Transaction Limit:
Parameter: masters[i].max_outstanding
Type: integer
Valid Values: 1-256
Default: 16
Description: Maximum outstanding transactions per master
Constraints: Limited by ID width (max = 2^id_width)
Performance Impact: Higher values increase throughput
Example: "max_outstanding": 32

ID Width Configuration:
Parameter: masters[i].id_width
Type: integer
Valid Values: 1-16
Default: 4
Units: bits
Description: Transaction ID width for this master
Constraints: 2^id_width >= max_outstanding
Example: "id_width": 6  // Supports up to 64 outstanding

Data Width Override:
Parameter: masters[i].data_width
Type: integer
Valid Values: 8, 16, 32, 64, 128, 256, 512, 1024
Default: global.data_width
Description: Master-specific data width (if different from global)
Note: Width conversion will be automatically inserted
Example: "data_width": 64

QoS Configuration:
Parameter: masters[i].qos_config
Type: object
Schema: {
  "default_qos": integer (0-15),
  "qos_override": boolean,
  "priority_class": string
}
Description: Quality of Service settings
Example:
"qos_config": {
  "default_qos": 8,
  "qos_override": true,
  "priority_class": "real_time"
}

User Signal Configuration:
Parameter: masters[i].user_signals
Type: object
Schema: {
  "awuser_width": integer (0-1024),
  "wuser_width": integer (0-1024),
  "buser_width": integer (0-1024),
  "aruser_width": integer (0-1024),
  "ruser_width": integer (0-1024)
}
Default: All widths = 0 (disabled)
Description: User sideband signal widths
Example:
"user_signals": {
  "awuser_width": 8,
  "aruser_width": 8,
  "wuser_width": 4,
  "ruser_width": 4,
  "buser_width": 4
}

Security Configuration:
Parameter: masters[i].security
Type: object
Schema: {
  "trustzone_capable": boolean,
  "default_secure": boolean,
  "security_mode": string
}
Valid security_mode: "always_secure", "always_nonsecure", "configurable"
Description: TrustZone security settings
Example:
"security": {
  "trustzone_capable": true,
  "default_secure": false,
  "security_mode": "configurable"
}

Protocol-Specific Features:
Parameter: masters[i].protocol_features
Type: object
Description: Protocol-specific configuration options

For AXI4:
{
  "region_support": boolean,
  "exclusive_access": boolean,
  "atomic_operations": boolean,
  "cache_coherent": boolean
}

For AXI3:
{
  "write_interleave": boolean,
  "locked_access": boolean,
  "wid_support": boolean
}

Example:
"protocol_features": {
  "region_support": true,
  "exclusive_access": true,
  "atomic_operations": false,
  "cache_coherent": true
}

Connection Constraints:
Parameter: masters[i].connection_constraints
Type: object
Schema: {
  "allowed_slaves": array of integers,
  "prohibited_slaves": array of integers,
  "default_slave": integer
}
Description: Restrict master connectivity
Example:
"connection_constraints": {
  "allowed_slaves": [0, 1, 2],
  "prohibited_slaves": [7],
  "default_slave": 0
}
"""
    pdf_generator.create_text_page(pdf, "6.1 Global and Master Config", None, global_master_config, code_style=True)
    
    # Page 76: Slave and Interconnect Configuration Parameters
    slave_interconnect_config = """
6.2 Slave and Interconnect Configuration Parameters

SLAVE CONFIGURATION PARAMETERS:

Slave Identification:
Parameter: slaves[i].id
Type: integer
Valid Values: 0 to (NUM_SLAVES-1)
Description: Unique slave identifier
Constraints: Must be sequential starting from 0
Example: "id": 0

Slave Name:
Parameter: slaves[i].name
Type: string
Valid Values: Alphanumeric with underscores
Max Length: 64 characters
Description: Human-readable slave name
Example: "name": "ddr4_controller"

Slave Type:
Parameter: slaves[i].type
Type: enumeration
Valid Values: "memory", "peripheral", "bridge", "custom"
Default: "custom"
Description: Slave functional category
Example: "type": "memory"

Address Configuration:
Parameter: slaves[i].address_config
Type: object
Schema: {
  "base_address": string (hex),
  "size": string (hex),
  "alignment": string (hex)
}
Description: Memory map configuration
Constraints: 
- base_address must be aligned to size
- size must be power of 2
- No overlapping address ranges
Example:
"address_config": {
  "base_address": "0x00000000",
  "size": "0x40000000",
  "alignment": "0x40000000"
}

Data Width Configuration:
Parameter: slaves[i].data_width
Type: integer
Valid Values: 8, 16, 32, 64, 128, 256, 512, 1024
Default: global.data_width
Description: Slave interface data width
Note: Width conversion automatically inserted if needed
Example: "data_width": 256

Response Configuration:
Parameter: slaves[i].response_config
Type: object
Schema: {
  "default_response": string,
  "error_response": string,
  "min_latency": integer,
  "max_latency": integer,
  "typical_latency": integer
}
Valid responses: "OKAY", "EXOKAY", "SLVERR", "DECERR"
Latency units: clock cycles
Example:
"response_config": {
  "default_response": "OKAY",
  "error_response": "SLVERR",
  "min_latency": 5,
  "max_latency": 50,
  "typical_latency": 15
}

Memory Model Configuration:
Parameter: slaves[i].memory_model
Type: object
Schema: {
  "model_type": string,
  "memory_size": string,
  "initialization": string,
  "backing_store": boolean
}
Valid model_type: "sparse", "dense", "functional", "none"
Example:
"memory_model": {
  "model_type": "sparse",
  "memory_size": "1GB",
  "initialization": "zero",
  "backing_store": true
}

Security Configuration:
Parameter: slaves[i].security
Type: object
Schema: {
  "secure_only": boolean,
  "secure_regions": array,
  "access_control": object
}
Example:
"security": {
  "secure_only": false,
  "secure_regions": [
    {"base": "0x00000000", "size": "0x10000000"}
  ],
  "access_control": {
    "read_secure": true,
    "write_secure": true,
    "read_nonsecure": true,
    "write_nonsecure": false
  }
}

INTERCONNECT CONFIGURATION PARAMETERS:

Arbitration Configuration:
Parameter: interconnect.arbitration
Type: object
Schema: {
  "algorithm": string,
  "weights": array,
  "qos_enabled": boolean,
  "starvation_timeout": integer
}
Valid algorithms: "round_robin", "priority", "weighted_rr", "qos_aware"
Example:
"arbitration": {
  "algorithm": "weighted_rr",
  "weights": [4, 2, 1, 1],
  "qos_enabled": true,
  "starvation_timeout": 1000
}

Pipeline Configuration:
Parameter: interconnect.pipeline
Type: object
Schema: {
  "address_stages": integer,
  "data_stages": integer,
  "response_stages": integer,
  "register_slicing": boolean
}
Valid stages: 0-8
Description: Pipeline depth for timing closure
Example:
"pipeline": {
  "address_stages": 2,
  "data_stages": 1, 
  "response_stages": 1,
  "register_slicing": true
}

Performance Configuration:
Parameter: interconnect.performance
Type: object
Schema: {
  "optimization_target": string,
  "bandwidth_sharing": string,
  "latency_priority": string,
  "power_optimization": boolean
}
Valid optimization_target: "area", "speed", "power", "balanced"
Valid bandwidth_sharing: "fair", "weighted", "priority"
Valid latency_priority: "minimize", "balanced", "throughput"
Example:
"performance": {
  "optimization_target": "balanced",
  "bandwidth_sharing": "weighted",
  "latency_priority": "minimize",
  "power_optimization": true
}

Multi-Clock Support:
Parameter: interconnect.multi_clock
Type: object
Schema: {
  "enabled": boolean,
  "clock_domains": array,
  "cdc_type": string,
  "fifo_depth": integer
}
Valid cdc_type: "async_fifo", "handshake", "mux_ff"
Example:
"multi_clock": {
  "enabled": true,
  "clock_domains": [
    {"masters": [0, 1], "domain": "cpu_clk"},
    {"slaves": [0], "domain": "ddr_clk"}
  ],
  "cdc_type": "async_fifo",
  "fifo_depth": 8
}

Debug Configuration:
Parameter: interconnect.debug
Type: object
Schema: {
  "debug_ports": boolean,
  "performance_counters": boolean,
  "trace_interface": boolean,
  "assertion_checking": boolean
}
Example:
"debug": {
  "debug_ports": true,
  "performance_counters": true,
  "trace_interface": false,
  "assertion_checking": true
}

Power Management:
Parameter: interconnect.power
Type: object
Schema: {
  "clock_gating": boolean,
  "power_domains": array,
  "retention_support": boolean,
  "dvfs_support": boolean
}
Example:
"power": {
  "clock_gating": true,
  "power_domains": [
    {"name": "always_on", "masters": [3], "slaves": [7]},
    {"name": "cpu_domain", "masters": [0, 1], "slaves": [0, 1]}
  ],
  "retention_support": false,
  "dvfs_support": true
}

Generation Options:
Parameter: generation_options
Type: object
Schema: {
  "target_language": string,
  "include_testbench": boolean,
  "include_assertions": boolean,
  "include_coverage": boolean,
  "optimization_level": integer
}
Valid target_language: "systemverilog", "verilog", "vhdl"
Valid optimization_level: 0-3
Example:
"generation_options": {
  "target_language": "systemverilog",
  "include_testbench": true,
  "include_assertions": true,
  "include_coverage": true,
  "optimization_level": 2
}
"""
    pdf_generator.create_text_page(pdf, "6.2 Slave and Interconnect Config", None, slave_interconnect_config, code_style=True)
    
    # Page 77: Advanced Configuration and Validation
    advanced_config_validation = """
6.3 Advanced Configuration and Validation

ADVANCED FEATURE CONFIGURATION:

TrustZone Security Configuration:
Parameter: advanced_features.trustzone
Type: object
Schema: {
  "enabled": boolean,
  "secure_masters": array of integers,
  "secure_slaves": array of integers,
  "security_violations": string,
  "secure_debug": boolean
}
Valid security_violations: "error_response", "interrupt", "silent"
Example:
"trustzone": {
  "enabled": true,
  "secure_masters": [0, 1],
  "secure_slaves": [0, 2, 3],
  "security_violations": "error_response",
  "secure_debug": false
}

Exclusive Access Configuration:
Parameter: advanced_features.exclusive_access
Type: object
Schema: {
  "enabled": boolean,
  "monitor_count": integer,
  "timeout_cycles": integer,
  "global_monitor": boolean
}
Valid monitor_count: 1-64
Example:
"exclusive_access": {
  "enabled": true,
  "monitor_count": 16,
  "timeout_cycles": 10000,
  "global_monitor": true
}

Cache Coherency Configuration:
Parameter: advanced_features.coherency
Type: object
Schema: {
  "protocol": string,
  "coherency_masters": array,
  "snoop_filter": boolean,
  "cache_line_size": integer
}
Valid protocol: "ACE", "ACE_LITE", "CHI", "none"
Valid cache_line_size: 32, 64, 128 (bytes)
Example:
"coherency": {
  "protocol": "ACE",
  "coherency_masters": [0, 1],
  "snoop_filter": true,
  "cache_line_size": 64
}

Quality of Service Configuration:
Parameter: advanced_features.qos
Type: object
Schema: {
  "enabled": boolean,
  "arbitration_algorithm": string,
  "bandwidth_regulation": boolean,
  "urgency_promotion": boolean,
  "qos_mapping": array
}
Example:
"qos": {
  "enabled": true,
  "arbitration_algorithm": "weighted_round_robin",
  "bandwidth_regulation": true,
  "urgency_promotion": true,
  "qos_mapping": [
    {"qos_level": 15, "bandwidth_percent": 40},
    {"qos_level": 8,  "bandwidth_percent": 30},
    {"qos_level": 0,  "bandwidth_percent": 10}
  ]
}

CONFIGURATION VALIDATION RULES:

System-Level Validation:
• Total master count: 2-32
• Total slave count: 2-64
• Address space coverage: No gaps or overlaps
• Data width compatibility: Automatic conversion insertion
• Clock domain consistency: Proper CDC insertion

Master Validation Rules:
• ID width consistency: 2^id_width >= max_outstanding
• QoS level range: 0-15
• User signal widths: 0-1024 bits
• Connection validity: At least one slave connection
• Protocol feature compatibility: AXI3/AXI4 specific checks

Slave Validation Rules:
• Address alignment: base_address % size == 0
• Size requirements: Must be power of 2
• Address range validity: Within system address space
• Response latency: min_latency <= typical_latency <= max_latency
• Security consistency: Secure masters can access secure slaves

Interconnect Validation Rules:
• Pipeline stages: 0-8 valid range
• Arbitration weights: Sum equals number of masters
• QoS configuration: Consistent with master QoS settings
• Clock domain assignments: All components assigned
• Performance targets: Achievable with given configuration

CONFIGURATION EXAMPLES:

Minimal Configuration:
{
  "global_config": {
    "protocol": "AXI4",
    "data_width": 32,
    "addr_width": 32
  },
  "masters": [
    {"id": 0, "name": "cpu", "type": "cpu"},
    {"id": 1, "name": "dma", "type": "dma"}
  ],
  "slaves": [
    {"id": 0, "name": "memory", "type": "memory",
     "address_config": {"base_address": "0x00000000", "size": "0x40000000"}},
    {"id": 1, "name": "peripheral", "type": "peripheral",
     "address_config": {"base_address": "0x40000000", "size": "0x10000000"}}
  ]
}

High-Performance Configuration:
{
  "global_config": {
    "protocol": "AXI4",
    "data_width": 256,
    "addr_width": 40
  },
  "masters": [
    {"id": 0, "name": "cpu_cluster", "max_outstanding": 64, "id_width": 6,
     "qos_config": {"default_qos": 12}},
    {"id": 1, "name": "gpu", "max_outstanding": 128, "id_width": 7,
     "qos_config": {"default_qos": 15}}
  ],
  "interconnect": {
    "arbitration": {"algorithm": "qos_aware", "qos_enabled": true},
    "pipeline": {"address_stages": 3, "data_stages": 2},
    "performance": {"optimization_target": "speed"}
  }
}

Security-Enabled Configuration:
{
  "global_config": {
    "protocol": "AXI4",
    "data_width": 128,
    "addr_width": 32
  },
  "masters": [
    {"id": 0, "name": "secure_cpu", 
     "security": {"trustzone_capable": true, "default_secure": true}},
    {"id": 1, "name": "nonsecure_cpu",
     "security": {"trustzone_capable": true, "default_secure": false}}
  ],
  "slaves": [
    {"id": 0, "name": "secure_memory", "type": "memory",
     "security": {"secure_only": true}},
    {"id": 1, "name": "shared_memory", "type": "memory",
     "security": {"secure_only": false}}
  ],
  "advanced_features": {
    "trustzone": {"enabled": true, "secure_masters": [0], "secure_slaves": [0]}
  }
}

CONFIGURATION MIGRATION:

Version Compatibility:
The tool supports automatic migration of configuration files
from older versions to maintain project compatibility.

Migration Process:
1. Backup original configuration
2. Parse and validate old format
3. Map parameters to new schema
4. Apply default values for new features
5. Validate migrated configuration
6. Generate migration report

Common Migration Issues:
• Deprecated parameters: Automatically mapped or warnings issued
• Parameter name changes: Transparent mapping applied
• New required parameters: Sensible defaults assigned
• Incompatible values: User intervention required

Configuration Validation Report:
The tool generates comprehensive validation reports:
• Parameter validation status
• Constraint checking results
• Performance estimation
• Resource utilization
• Recommendations for optimization

Error Classifications:
• FATAL: Configuration prevents generation
• ERROR: Issues requiring user attention
• WARNING: Suboptimal but functional
• INFO: Recommendations for improvement
"""
    pdf_generator.create_text_page(pdf, "6.3 Advanced Config and Validation", None, advanced_config_validation, code_style=True)
    
    # Page 78: Configuration Examples and Best Practices (bonus page to start next section)
    config_examples = """
6.4 Configuration Examples and Best Practices

COMPLETE CONFIGURATION EXAMPLES:

Automotive SoC Configuration:  
{
  "project_info": {
    "name": "automotive_gateway_soc",
    "version": "3.1.0",
    "target": "ISO26262_ASIL_D"
  },
  "global_config": {
    "protocol": "AXI4",
    "data_width": 128,
    "addr_width": 40,
    "endianness": "little"
  },
  "masters": [
    {
      "id": 0, "name": "cortex_r52_safety", "type": "cpu",
      "max_outstanding": 16, "id_width": 4,
      "qos_config": {"default_qos": 15, "priority_class": "safety_critical"},
      "security": {"trustzone_capable": true, "default_secure": true},
      "protocol_features": {"exclusive_access": true, "region_support": true}
    },
    {
      "id": 1, "name": "cortex_a78_app", "type": "cpu", 
      "max_outstanding": 32, "id_width": 5,
      "qos_config": {"default_qos": 8, "priority_class": "performance"},
      "security": {"trustzone_capable": true, "default_secure": false}
    },
    {
      "id": 2, "name": "dma_engine", "type": "dma",
      "max_outstanding": 64, "id_width": 6,
      "qos_config": {"default_qos": 4, "priority_class": "bulk_transfer"}
    },
    {
      "id": 3, "name": "gpu_mali", "type": "gpu",
      "max_outstanding": 128, "id_width": 7,
      "qos_config": {"default_qos": 6, "priority_class": "multimedia"}
    }
  ],
  "slaves": [
    {
      "id": 0, "name": "ddr4_main", "type": "memory",
      "address_config": {
        "base_address": "0x0000000000", "size": "0x0200000000"
      },
      "data_width": 256,
      "response_config": {
        "min_latency": 20, "typical_latency": 35, "max_latency": 100
      },
      "security": {"secure_only": false}
    },
    {
      "id": 1, "name": "safety_sram", "type": "memory",
      "address_config": {
        "base_address": "0x0400000000", "size": "0x0001000000"
      },
      "response_config": {"min_latency": 2, "typical_latency": 3, "max_latency": 5},
      "security": {"secure_only": true}
    },
    {
      "id": 2, "name": "can_controller", "type": "peripheral",
      "address_config": {
        "base_address": "0x0500000000", "size": "0x0000010000"
      },
      "response_config": {"typical_latency": 10}
    }
  ],
  "interconnect": {
    "arbitration": {
      "algorithm": "qos_aware",
      "qos_enabled": true,
      "starvation_timeout": 2000
    },
    "pipeline": {"address_stages": 2, "data_stages": 1},
    "performance": {"optimization_target": "balanced"}
  },
  "advanced_features": {
    "trustzone": {
      "enabled": true,
      "secure_masters": [0],
      "secure_slaves": [1]
    },
    "qos": {
      "enabled": true,
      "bandwidth_regulation": true,
      "urgency_promotion": true
    }
  }
}

Data Center SoC Configuration:
{
  "project_info": {
    "name": "datacenter_accelerator",
    "version": "1.0.0",
    "target": "high_performance_computing"
  },
  "global_config": {
    "protocol": "AXI4",
    "data_width": 512,
    "addr_width": 48
  },
  "masters": [
    {
      "id": 0, "name": "cpu_complex", "type": "cpu",
      "max_outstanding": 256, "id_width": 8,
      "qos_config": {"default_qos": 10},
      "user_signals": {"awuser_width": 16, "aruser_width": 16}
    },
    {
      "id": 1, "name": "ai_accelerator", "type": "accelerator",
      "max_outstanding": 512, "id_width": 9,
      "qos_config": {"default_qos": 12},
      "data_width": 1024
    },
    {
      "id": 2, "name": "network_processor", "type": "accelerator", 
      "max_outstanding": 128, "id_width": 7,
      "qos_config": {"default_qos": 14}
    }
  ],
  "interconnect": {
    "arbitration": {"algorithm": "weighted_rr", "weights": [2, 4, 1]},
    "pipeline": {"address_stages": 4, "data_stages": 3},
    "performance": {"optimization_target": "speed"},
    "multi_clock": {
      "enabled": true,
      "cdc_type": "async_fifo",
      "fifo_depth": 16
    }
  }
}

CONFIGURATION BEST PRACTICES:

Performance Optimization:
1. Data Width Alignment:
   • Use power-of-2 data widths
   • Align slave data widths to transfer sizes
   • Consider memory subsystem width

2. Outstanding Transaction Tuning:
   • Set based on latency-bandwidth product
   • Higher for high-latency slaves (memory)
   • Lower for low-latency slaves (peripherals)

3. Pipeline Depth Selection:
   • Shallow pipelines: Lower latency, higher frequency pressure
   • Deep pipelines: Higher latency, easier timing closure
   • Typical: 2-4 stages for balanced designs

4. QoS Configuration:
   • Reserve highest levels (12-15) for real-time/safety
   • Use middle levels (6-11) for performance traffic  
   • Use low levels (0-5) for best-effort traffic

Security Configuration:
1. TrustZone Partitioning:
   • Clearly separate secure and non-secure masters
   • Protect sensitive slaves (crypto, keys, boot ROM)
   • Use secure-only slaves for critical data

2. Address Space Layout:
   • Place secure memory at well-known addresses
   • Use non-overlapping secure regions
   • Consider address aliasing vulnerabilities

Power Optimization:
1. Clock Gating:
   • Enable for all non-critical paths
   • Consider impact on timing closure
   • Use fine-grained gating for maximum savings

2. Multi-Clock Domains:
   • Group functionally related components
   • Minimize CDC crossings
   • Use rational frequency relationships when possible

Verification Configuration:
1. Testbench Generation:
   • Enable comprehensive test suite
   • Include protocol compliance checks
   • Add performance monitoring

2. Coverage Configuration:
   • Enable functional coverage collection
   • Add protocol-specific coverage
   • Monitor QoS and security features

COMMON CONFIGURATION PITFALLS:

Address Map Issues:
• Overlapping slave addresses
• Unaligned base addresses  
• Gaps in address coverage
• Insufficient address decode width

Performance Bottlenecks:
• Inadequate outstanding transaction limits
• Mismatched data widths causing frequent conversions
• Poor QoS level assignment
• Excessive pipeline depth

Security Vulnerabilities:
• Non-secure masters accessing secure slaves
• Insufficient address range protection
• Missing TrustZone configuration
• Weak isolation between security domains

Resource Conflicts:
• Exceeding target device capacity
• Unrealistic timing constraints
• Inadequate power budget
• Insufficient I/O resources
"""
    pdf_generator.create_text_page(pdf, "6.4 Config Examples", None, config_examples, code_style=True)

# This function can be integrated into the main PDF generator