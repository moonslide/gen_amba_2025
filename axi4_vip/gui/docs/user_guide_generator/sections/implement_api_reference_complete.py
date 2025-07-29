#!/usr/bin/env python3
"""
Implement COMPLETE API Reference section (pages 85-89) with full detailed content
NO PLACEHOLDERS - every page fully implemented with real information
5 pages of comprehensive API reference content
"""

def create_complete_api_reference_section(pdf_generator, pdf):
    """Complete API Reference section - 5 pages of detailed content"""
    
    # Page 85: API Reference Overview
    api_overview = """
The AMBA Bus Matrix Configuration Tool provides comprehensive APIs for automation,
integration with other tools, and programmatic control of design generation.
This section documents all available APIs with examples and usage patterns.

API CATEGORIES:

Python API:
• Core configuration classes and methods
• Design validation and manipulation functions
• Generation control and customization
• File I/O and format conversion utilities
• Integration hooks for custom workflows

Command Line Interface:
• Batch processing commands
• Configuration file operations
• Generation control parameters
• Debug and diagnostic options
• Integration with build systems

REST API (Optional):
• Web service interface for remote operation
• JSON-based configuration management
• Distributed generation capabilities
• Multi-user collaboration features
• Cloud integration support

Configuration File API:
• JSON configuration schema
• XML configuration format
• Binary configuration format
• Import/export utilities
• Version migration tools

PROGRAMMING INTERFACES:

Python Module Structure:
bus_matrix_tool/
├── core/
│   ├── configuration.py      # Configuration management
│   ├── validation.py         # Design validation
│   ├── generation.py         # RTL/VIP generation
│   └── utilities.py          # Common utilities
├── gui/
│   ├── main_window.py        # GUI application
│   ├── dialogs.py            # Configuration dialogs
│   └── widgets.py            # Custom widgets
├── formats/
│   ├── json_handler.py       # JSON format support
│   ├── xml_handler.py        # XML format support
│   └── binary_handler.py     # Binary format support
└── integration/
    ├── command_line.py       # CLI interface
    ├── rest_api.py          # REST API server
    └── plugins.py           # Plugin system

API DESIGN PRINCIPLES:

Consistency:
• Uniform naming conventions
• Consistent parameter patterns
• Standardized return values
• Common error handling

Flexibility:
• Multiple interface options
• Configurable behavior
• Extensible architecture
• Plugin-based customization

Reliability:
• Comprehensive error checking
• Input validation
• Safe default values
• Graceful failure handling

Performance:
• Efficient data structures
• Lazy evaluation where appropriate
• Caching for repeated operations
• Minimal memory footprint

GETTING STARTED WITH APIS:

Basic Python Usage:
#!/usr/bin/env python3
from bus_matrix_tool.core import Configuration, Generator
from bus_matrix_tool.core.validation import validate_design

# Load configuration
config = Configuration.from_file("my_design.json")

# Validate design
if validate_design(config):
    # Generate RTL
    generator = Generator(config)
    generator.generate_rtl("output_rtl/")
    print("RTL generation completed successfully")
else:
    print("Design validation failed")

Command Line Usage:
# Generate RTL from configuration file
python3 -m bus_matrix_tool.cli generate-rtl --config design.json --output rtl_output/

# Validate configuration
python3 -m bus_matrix_tool.cli validate --config design.json

# Convert between formats
python3 -m bus_matrix_tool.cli convert --input design.xml --output design.json

API DOCUMENTATION CONVENTIONS:

Parameter Types:
• str: String values
• int: Integer values  
• float: Floating-point values
• bool: Boolean values
• List[T]: List of type T
• Dict[K, V]: Dictionary with key type K and value type V
• Optional[T]: Optional parameter of type T

Return Values:
• Functions return bool for success/failure when appropriate
• Complex operations return result objects with status and data
• Exceptions are raised for error conditions
• None is returned when no meaningful value exists

Error Handling:
• ConfigurationError: Invalid configuration parameters
• ValidationError: Design validation failures
• GenerationError: RTL/VIP generation failures
• FileError: File I/O operations
• ToolError: External tool integration issues

The following sections provide detailed documentation for each API category
with complete method signatures, parameters, return values, and usage examples.
"""
    pdf_generator.create_text_page(pdf, "8. API Reference", "Overview", api_overview)
    
    # Page 86: Python Core API
    python_core_api = """
8.1 Python Core API

CONFIGURATION CLASS:

class Configuration:
    \"\"\"Main configuration management class\"\"\"
    
    def __init__(self, protocol: str = "AXI4"):
        \"\"\"Initialize configuration with default parameters
        
        Args:
            protocol: Bus protocol ("AXI4", "AXI3", "AHB", "APB")
        \"\"\"
        
    @classmethod
    def from_file(cls, filename: str) -> 'Configuration':
        \"\"\"Load configuration from file
        
        Args:
            filename: Path to configuration file (.json, .xml, .bmcfg)
            
        Returns:
            Configuration object
            
        Raises:
            FileError: If file cannot be read
            ConfigurationError: If file format is invalid
        \"\"\"
        
    def to_file(self, filename: str) -> bool:
        \"\"\"Save configuration to file
        
        Args:
            filename: Output file path
            
        Returns:
            True if successful, False otherwise
        \"\"\"
        
    def add_master(self, name: str, master_type: str = "custom", **kwargs) -> int:
        \"\"\"Add master to configuration
        
        Args:
            name: Master name (must be unique)
            master_type: Master type ("cpu", "dma", "gpu", "custom")
            **kwargs: Additional master parameters
            
        Returns:
            Master ID (integer)
            
        Example:
            master_id = config.add_master(
                name="cortex_a78",
                master_type="cpu",
                max_outstanding=32,
                id_width=5,
                qos_config={"default_qos": 8}
            )
        \"\"\"
        
    def add_slave(self, name: str, base_address: str, size: str, **kwargs) -> int:
        \"\"\"Add slave to configuration
        
        Args:
            name: Slave name (must be unique)
            base_address: Base address (hex string)
            size: Address space size (hex string)
            **kwargs: Additional slave parameters
            
        Returns:
            Slave ID (integer)
            
        Example:
            slave_id = config.add_slave(
                name="ddr4_memory",
                base_address="0x00000000",
                size="0x40000000",
                slave_type="memory",
                data_width=256
            )
        \"\"\"
        
    def connect_master_to_slave(self, master_id: int, slave_id: int) -> bool:
        \"\"\"Create connection between master and slave
        
        Args:
            master_id: Master identifier
            slave_id: Slave identifier
            
        Returns:
            True if connection created successfully
        \"\"\"
        
    def get_master(self, master_id: int) -> Dict:
        \"\"\"Get master configuration by ID
        
        Args:
            master_id: Master identifier
            
        Returns:
            Dictionary containing master configuration
            
        Raises:
            ConfigurationError: If master ID not found
        \"\"\"
        
    def get_slave(self, slave_id: int) -> Dict:
        \"\"\"Get slave configuration by ID
        
        Args:
            slave_id: Slave identifier
            
        Returns:
            Dictionary containing slave configuration
        \"\"\"
        
    def list_masters(self) -> List[Dict]:
        \"\"\"Get list of all masters
        
        Returns:
            List of master configuration dictionaries
        \"\"\"
        
    def list_slaves(self) -> List[Dict]:
        \"\"\"Get list of all slaves
        
        Returns:
            List of slave configuration dictionaries
        \"\"\"
        
    def validate(self) -> Tuple[bool, List[str]]:
        \"\"\"Validate current configuration
        
        Returns:
            Tuple of (is_valid, error_messages)
        \"\"\"

VALIDATION MODULE:

def validate_design(config: Configuration) -> bool:
    \"\"\"Comprehensive design validation
    
    Args:
        config: Configuration object to validate
        
    Returns:
        True if design is valid, False otherwise
    \"\"\"

def validate_address_map(config: Configuration) -> Tuple[bool, List[str]]:
    \"\"\"Validate address map for overlaps and alignment
    
    Args:
        config: Configuration object
        
    Returns:
        Tuple of (is_valid, error_messages)
    \"\"\"

def validate_connectivity(config: Configuration) -> Tuple[bool, List[str]]:
    \"\"\"Validate master-slave connectivity
    
    Args:
        config: Configuration object
        
    Returns:
        Tuple of (is_valid, error_messages)
    \"\"\"

def validate_protocol_compliance(config: Configuration) -> Tuple[bool, List[str]]:
    \"\"\"Check protocol-specific constraints
    
    Args:
        config: Configuration object
        
    Returns:
        Tuple of (is_valid, error_messages)
    \"\"\"

GENERATION MODULE:

class Generator:
    \"\"\"RTL and VIP generation controller\"\"\"
    
    def __init__(self, config: Configuration):
        \"\"\"Initialize generator with configuration
        
        Args:
            config: Validated configuration object
        \"\"\"
        
    def generate_rtl(self, output_dir: str, **options) -> bool:
        \"\"\"Generate synthesizable RTL
        
        Args:
            output_dir: Output directory path
            **options: Generation options
            
        Returns:
            True if generation successful
            
        Example:
            success = generator.generate_rtl(
                output_dir="./rtl_output",
                target_language="systemverilog",
                include_testbench=True,
                optimization_level=2
            )
        \"\"\"
        
    def generate_vip(self, output_dir: str, **options) -> bool:
        \"\"\"Generate UVM verification environment
        
        Args:
            output_dir: Output directory path
            **options: VIP generation options
            
        Returns:
            True if generation successful
            
        Example:
            success = generator.generate_vip(
                output_dir="./vip_output",
                uvm_version="1.2",
                include_coverage=True,
                simulator="questa"
            )
        \"\"\"
        
    def generate_documentation(self, output_dir: str, format: str = "html") -> bool:
        \"\"\"Generate design documentation
        
        Args:
            output_dir: Output directory path
            format: Documentation format ("html", "pdf", "markdown")
            
        Returns:
            True if generation successful
        \"\"\"
        
    def estimate_resources(self) -> Dict:
        \"\"\"Estimate hardware resource requirements
        
        Returns:
            Dictionary with resource estimates:
            {
                "logic_cells": int,
                "memory_bits": int,
                "dsp_blocks": int,
                "io_pins": int
            }
        \"\"\"

UTILITIES MODULE:

def convert_address_width(addr: str, from_width: int, to_width: int) -> str:
    \"\"\"Convert address between different widths
    
    Args:
        addr: Address string (hex format)
        from_width: Current address width in bits
        to_width: Target address width in bits
        
    Returns:
        Converted address string
    \"\"\"

def calculate_address_alignment(addr: str, size: int) -> str:
    \"\"\"Calculate aligned address for given size
    
    Args:
        addr: Base address (hex string)
        size: Alignment size in bytes
        
    Returns:
        Aligned address (hex string)
    \"\"\"

def parse_size_string(size_str: str) -> int:
    \"\"\"Parse size string with units to bytes
    
    Args:
        size_str: Size with units ("1MB", "512KB", "2GB")
        
    Returns:
        Size in bytes
        
    Example:
        bytes_val = parse_size_string("256MB")  # Returns 268435456
    \"\"\"

def format_size_string(bytes_val: int) -> str:
    \"\"\"Format byte count as human-readable string
    
    Args:
        bytes_val: Size in bytes
        
    Returns:
        Formatted string with appropriate units
        
    Example:
        size_str = format_size_string(268435456)  # Returns "256MB"
    \"\"\"

EXAMPLE USAGE:

#!/usr/bin/env python3
\"\"\"Complete example using Python API\"\"\"

from bus_matrix_tool.core import Configuration, Generator
from bus_matrix_tool.core.validation import validate_design
from bus_matrix_tool.core.utilities import parse_size_string

def create_automotive_soc():
    \"\"\"Create automotive SoC configuration programmatically\"\"\"
    
    # Create base configuration
    config = Configuration(protocol="AXI4")
    
    # Configure global parameters
    config.set_global_parameter("data_width", 128)
    config.set_global_parameter("addr_width", 40)
    
    # Add masters
    cpu_id = config.add_master(
        name="cortex_r52_safety",
        master_type="cpu",
        max_outstanding=16,
        id_width=4,
        qos_config={"default_qos": 15, "priority_class": "safety_critical"},
        security={"trustzone_capable": True, "default_secure": True}
    )
    
    dma_id = config.add_master(
        name="dma_engine",
        master_type="dma", 
        max_outstanding=64,
        id_width=6,
        qos_config={"default_qos": 4}
    )
    
    # Add slaves
    ddr_id = config.add_slave(
        name="ddr4_main",
        base_address="0x0000000000",
        size="0x0200000000",  # 8GB
        slave_type="memory",
        data_width=256
    )
    
    sram_id = config.add_slave(
        name="safety_sram", 
        base_address="0x0400000000",
        size="0x0001000000",  # 16MB
        slave_type="memory",
        security={"secure_only": True}
    )
    
    # Create connections
    config.connect_master_to_slave(cpu_id, ddr_id)
    config.connect_master_to_slave(cpu_id, sram_id)
    config.connect_master_to_slave(dma_id, ddr_id)
    
    # Configure advanced features
    config.enable_trustzone(
        secure_masters=[cpu_id],
        secure_slaves=[sram_id]
    )
    
    config.enable_qos(
        algorithm="qos_aware",
        bandwidth_regulation=True
    )
    
    return config

def main():
    # Create configuration
    config = create_automotive_soc()
    
    # Validate design
    is_valid, errors = validate_design(config)
    if not is_valid:
        print("Validation failed:")
        for error in errors:
            print(f"  - {error}")
        return
    
    # Save configuration
    config.to_file("automotive_soc.json")
    
    # Generate RTL and VIP
    generator = Generator(config)
    
    if generator.generate_rtl("./rtl_output", include_testbench=True):
        print("RTL generation successful")
    
    if generator.generate_vip("./vip_output", uvm_version="1.2"):
        print("VIP generation successful")
    
    # Generate documentation
    generator.generate_documentation("./docs", format="html")
    
    print("Design generation complete!")

if __name__ == "__main__":
    main()
"""
    pdf_generator.create_text_page(pdf, "8.1 Python Core API", None, python_core_api, code_style=True)
    
    # Page 87: Command Line Interface API
    cli_api = """
8.2 Command Line Interface API

COMMAND STRUCTURE:

python3 -m bus_matrix_tool.cli <command> [options] [arguments]

AVAILABLE COMMANDS:

generate-rtl - Generate synthesizable RTL
Usage: generate-rtl --config <file> --output <dir> [options]

Required Arguments:
  --config FILE         Configuration file path (.json, .xml, .bmcfg)
  --output DIR          Output directory for generated RTL

Optional Arguments:
  --target-language STR Target HDL language (systemverilog, verilog, vhdl)
  --include-testbench   Generate testbench along with RTL
  --include-assertions  Include SystemVerilog assertions
  --include-coverage    Include coverage collection points
  --optimization LEVEL  Optimization level (0-3, default: 2)
  --target-tool STR     Target synthesis tool (vivado, quartus, dc)
  --pipeline-depth INT  Override pipeline depth (0-8)
  --verbose             Enable verbose output

Examples:
# Basic RTL generation
python3 -m bus_matrix_tool.cli generate-rtl \\
    --config my_design.json --output ./rtl_output

# Advanced RTL generation with options
python3 -m bus_matrix_tool.cli generate-rtl \\
    --config automotive_soc.json \\
    --output ./automotive_rtl \\
    --target-language systemverilog \\
    --include-testbench \\
    --include-assertions \\
    --optimization 3 \\
    --target-tool vivado \\
    --verbose

generate-vip - Generate UVM verification environment
Usage: generate-vip --config <file> --output <dir> [options]

Required Arguments:
  --config FILE         Configuration file path
  --output DIR          Output directory for VIP

Optional Arguments:
  --uvm-version STR     UVM version (1.1, 1.2, 2.0, default: 1.2)
  --simulator STR       Target simulator (vcs, questa, xcelium)
  --include-coverage    Generate coverage models
  --include-assertions  Include protocol assertions
  --test-suite STR      Test suite type (basic, comprehensive, custom)
  --regression-ready    Generate regression infrastructure
  --debug-features      Include debug and trace features

Examples:
# Basic VIP generation
python3 -m bus_matrix_tool.cli generate-vip \\
    --config my_design.json --output ./vip_output

# Comprehensive VIP with all features
python3 -m bus_matrix_tool.cli generate-vip \\
    --config complex_soc.json \\
    --output ./verification_ip \\
    --uvm-version 1.2 \\
    --simulator questa \\
    --include-coverage \\
    --include-assertions \\
    --test-suite comprehensive \\
    --regression-ready \\
    --debug-features

validate - Validate configuration
Usage: validate --config <file> [options]

Required Arguments:
  --config FILE         Configuration file to validate

Optional Arguments:
  --verbose             Show detailed validation results
  --fix-errors          Attempt to fix correctable errors
  --output FILE         Save corrected configuration
  --report-format STR   Report format (text, json, xml)

Examples:
# Basic validation
python3 -m bus_matrix_tool.cli validate --config design.json

# Detailed validation with error fixing
python3 -m bus_matrix_tool.cli validate \\
    --config design.json \\
    --verbose \\
    --fix-errors \\
    --output design_corrected.json

convert - Convert between configuration formats
Usage: convert --input <file> --output <file> [options]

Required Arguments:
  --input FILE          Input configuration file
  --output FILE         Output configuration file

Optional Arguments:
  --format STR          Force output format (json, xml, binary)
  --validate            Validate during conversion
  --preserve-comments   Preserve comments where possible

Examples:
# Convert XML to JSON
python3 -m bus_matrix_tool.cli convert \\
    --input design.xml --output design.json

# Convert with validation
python3 -m bus_matrix_tool.cli convert \\
    --input design.bmcfg --output design.json \\
    --validate

estimate-resources - Estimate hardware resources
Usage: estimate-resources --config <file> [options]

Required Arguments:
  --config FILE         Configuration file

Optional Arguments:
  --target-device STR   Target device family for accurate estimates
  --format STR          Output format (text, json, csv)
  --detail-level STR    Detail level (summary, detailed, component)

Examples:
# Basic resource estimation
python3 -m bus_matrix_tool.cli estimate-resources --config design.json

# Detailed estimation for specific device
python3 -m bus_matrix_tool.cli estimate-resources \\
    --config design.json \\
    --target-device "xc7z020clg484" \\
    --format json \\
    --detail-level detailed

analyze-performance - Analyze performance characteristics
Usage: analyze-performance --config <file> [options]

Required Arguments:
  --config FILE         Configuration file

Optional Arguments:
  --workload FILE       Workload specification file
  --metrics STR         Metrics to analyze (bandwidth, latency, all)
  --output FILE         Save analysis results

Examples:
# Performance analysis
python3 -m bus_matrix_tool.cli analyze-performance \\
    --config high_perf_soc.json \\
    --metrics all \\
    --output performance_report.json

BATCH PROCESSING:

batch-generate - Process multiple configurations
Usage: batch-generate --config-dir <dir> [options]

Arguments:
  --config-dir DIR      Directory containing configuration files
  --output-dir DIR      Base output directory
  --jobs INT            Number of parallel jobs (default: 4)
  --rtl                 Generate RTL for all configurations
  --vip                 Generate VIP for all configurations
  --continue-on-error   Continue processing if one config fails

Examples:
# Batch process all configs in directory
python3 -m bus_matrix_tool.cli batch-generate \\
    --config-dir ./designs \\
    --output-dir ./generated \\
    --rtl --vip \\
    --jobs 8

INTEGRATION COMMANDS:

export-ip-xact - Export IP-XACT description
Usage: export-ip-xact --config <file> --output <file>

Arguments:
  --config FILE         Configuration file
  --output FILE         Output IP-XACT file (.xml)
  --vendor STR          Vendor identifier
  --library STR         Library identifier
  --version STR         Version string

generate-makefile - Generate build Makefile
Usage: generate-makefile --config <file> --output <file>

Arguments:
  --config FILE         Configuration file
  --output FILE         Output Makefile
  --tool STR            Build tool (make, cmake, scons)
  --targets STR         Comma-separated target list

DEBUGGING AND DIAGNOSTICS:

debug - Enable debug mode
Usage: debug <subcommand> [arguments]

Subcommands:
  config                Show effective configuration
  templates             List available templates
  paths                 Show search paths
  version               Show version information

Examples:
# Show debug information
python3 -m bus_matrix_tool.cli debug config --config design.json
python3 -m bus_matrix_tool.cli debug templates
python3 -m bus_matrix_tool.cli debug version

CONFIGURATION FILE OPTIONS:

Environment Variables:
BUS_MATRIX_CONFIG_PATH    Default configuration search path
BUS_MATRIX_TEMPLATE_PATH  Template search path
BUS_MATRIX_LICENSE_FILE   License file location
BUS_MATRIX_LOG_LEVEL      Default logging level

Configuration File Precedence:
1. Command line --config argument
2. BUS_MATRIX_CONFIG_PATH environment variable
3. Current directory
4. User home directory (~/.bus_matrix_tool/)
5. System directory (/etc/bus_matrix_tool/)

RETURN CODES:

0    Success
1    General error
2    Configuration error
3    Validation error
4    Generation error
5    File I/O error
10   License error

SHELL INTEGRATION:

Bash Completion:
# Add to ~/.bashrc
eval "$(python3 -m bus_matrix_tool.cli --completion bash)"

# Or install completion script
python3 -m bus_matrix_tool.cli --completion bash > /etc/bash_completion.d/bus_matrix_tool

Zsh Completion:
# Add to ~/.zshrc
eval "$(python3 -m bus_matrix_tool.cli --completion zsh)"

SCRIPTING EXAMPLES:

#!/bin/bash
# Automated design flow script

set -e  # Exit on error

CONFIG_FILE="automotive_soc.json"
OUTPUT_BASE="./output"

echo "Starting automated design flow..."

# Validate configuration
echo "Validating configuration..."
python3 -m bus_matrix_tool.cli validate --config "$CONFIG_FILE" --verbose

# Generate RTL
echo "Generating RTL..."
python3 -m bus_matrix_tool.cli generate-rtl \\
    --config "$CONFIG_FILE" \\
    --output "$OUTPUT_BASE/rtl" \\
    --include-testbench \\
    --target-tool vivado

# Generate VIP
echo "Generating VIP..."
python3 -m bus_matrix_tool.cli generate-vip \\
    --config "$CONFIG_FILE" \\
    --output "$OUTPUT_BASE/vip" \\
    --simulator questa \\
    --regression-ready

# Estimate resources
echo "Estimating resources..."
python3 -m bus_matrix_tool.cli estimate-resources \\
    --config "$CONFIG_FILE" \\
    --target-device "xc7z045ffg900" \\
    --format json > "$OUTPUT_BASE/resources.json"

echo "Design flow completed successfully!"

# Parallel Processing Script
#!/bin/bash
# Process multiple designs in parallel

DESIGNS=("cpu_subsystem.json" "gpu_subsystem.json" "dma_subsystem.json")
MAX_JOBS=4

process_design() {
    local config=$1
    local base_name=$(basename "$config" .json)
    
    echo "Processing $config..."
    
    python3 -m bus_matrix_tool.cli generate-rtl \\
        --config "$config" \\
        --output "./output/$base_name/rtl" \\
        --include-testbench &
    
    python3 -m bus_matrix_tool.cli generate-vip \\
        --config "$config" \\
        --output "./output/$base_name/vip" &
    
    wait  # Wait for both processes to complete
    echo "Completed $config"
}

# Limit concurrent jobs
for config in "${DESIGNS[@]}"; do
    (($(jobs -r | wc -l) >= MAX_JOBS)) && wait
    process_design "$config" &
done

wait  # Wait for all jobs to complete
echo "All designs processed!"
"""
    pdf_generator.create_text_page(pdf, "8.2 Command Line API", None, cli_api, code_style=True)
    
    # Page 88: REST API and Integration
    rest_api = """
8.3 REST API and Integration Interfaces

REST API SERVER:

Starting the API Server:
python3 -m bus_matrix_tool.api_server --port 8080 --host 0.0.0.0

Server Configuration:
{
  "server": {
    "host": "0.0.0.0",
    "port": 8080,
    "workers": 4,
    "timeout": 300
  },
  "security": {
    "api_key_required": true,
    "cors_enabled": true,
    "rate_limiting": {
      "requests_per_minute": 60
    }
  },
  "storage": {
    "type": "filesystem",
    "base_path": "/var/lib/bus_matrix_tool"
  }
}

API ENDPOINTS:

Configuration Management:

GET /api/v1/configurations
List all configurations
Response: 200 OK
{
  "configurations": [
    {
      "id": "automotive_soc_v2",
      "name": "Automotive SoC v2.0",
      "created": "2024-01-15T10:30:00Z",
      "modified": "2024-01-20T14:45:00Z",
      "status": "validated"
    }
  ]
}

POST /api/v1/configurations
Create new configuration
Request Body:
{
  "name": "New Design",
  "protocol": "AXI4",
  "configuration": { ... }
}
Response: 201 Created
{
  "id": "new_design_123",
  "message": "Configuration created successfully"
}

GET /api/v1/configurations/{id}
Get specific configuration
Parameters:
  id: Configuration identifier
Response: 200 OK
{
  "id": "automotive_soc_v2",
  "name": "Automotive SoC v2.0", 
  "configuration": { ... },
  "metadata": { ... }
}

PUT /api/v1/configurations/{id}
Update configuration
Request Body:
{
  "configuration": { ... },
  "validation_required": true
}
Response: 200 OK
{
  "message": "Configuration updated successfully",
  "validation_status": "passed"
}

DELETE /api/v1/configurations/{id}
Delete configuration
Response: 204 No Content

Validation Endpoints:

POST /api/v1/configurations/{id}/validate
Validate configuration
Response: 200 OK
{
  "valid": true,
  "errors": [],
  "warnings": [
    "Suboptimal pipeline depth for target frequency"
  ],
  "performance_estimates": {
    "max_frequency": "400 MHz",
    "resource_utilization": "65%"
  }
}

Generation Endpoints:

POST /api/v1/configurations/{id}/generate/rtl
Generate RTL
Request Body:
{
  "options": {
    "target_language": "systemverilog",
    "include_testbench": true,
    "optimization_level": 2
  },
  "callback_url": "https://my-server.com/webhook/rtl-complete"
}
Response: 202 Accepted
{
  "job_id": "rtl_gen_789",
  "status": "queued",
  "estimated_completion": "2024-01-15T11:00:00Z"
}

POST /api/v1/configurations/{id}/generate/vip
Generate VIP
Request Body:
{
  "options": {
    "uvm_version": "1.2",
    "simulator": "questa",
    "include_coverage": true
  }
}
Response: 202 Accepted
{
  "job_id": "vip_gen_456",
  "status": "queued"
}

Job Management:

GET /api/v1/jobs/{job_id}
Get job status
Response: 200 OK
{
  "job_id": "rtl_gen_789",
  "status": "running",
  "progress": 65,
  "started": "2024-01-15T10:45:00Z",
  "estimated_completion": "2024-01-15T11:00:00Z",
  "logs": [
    "Starting RTL generation...",
    "Generating address decoder...",
    "Generating arbitration logic..."
  ]
}

GET /api/v1/jobs/{job_id}/results
Download job results
Response: 200 OK (for completed jobs)
Content-Type: application/zip
[Binary ZIP file containing generated files]

DELETE /api/v1/jobs/{job_id}
Cancel job
Response: 204 No Content

WEBHOOK NOTIFICATIONS:

Webhook Payload:
{
  "event": "generation_completed",
  "job_id": "rtl_gen_789", 
  "configuration_id": "automotive_soc_v2",
  "status": "success",
  "timestamp": "2024-01-15T11:05:00Z",
  "results": {
    "files_generated": 15,
    "total_lines": 12543,
    "warnings": 2,
    "errors": 0
  },
  "download_url": "/api/v1/jobs/rtl_gen_789/results"
}

CLIENT LIBRARIES:

Python Client:
#!/usr/bin/env python3
import requests
import json

class BusMatrixClient:
    def __init__(self, base_url, api_key):
        self.base_url = base_url
        self.headers = {
            'Authorization': f'Bearer {api_key}',
            'Content-Type': 'application/json'
        }
    
    def create_configuration(self, name, config):
        \"\"\"Create new configuration\"\"\"
        data = {
            'name': name,
            'configuration': config
        }
        response = requests.post(
            f'{self.base_url}/api/v1/configurations',
            headers=self.headers,
            json=data
        )
        return response.json()
    
    def generate_rtl(self, config_id, options=None):
        \"\"\"Generate RTL for configuration\"\"\"
        data = {'options': options or {}}
        response = requests.post(
            f'{self.base_url}/api/v1/configurations/{config_id}/generate/rtl',
            headers=self.headers,
            json=data
        )
        return response.json()
    
    def get_job_status(self, job_id):
        \"\"\"Get job status\"\"\"
        response = requests.get(
            f'{self.base_url}/api/v1/jobs/{job_id}',
            headers=self.headers
        )
        return response.json()
    
    def download_results(self, job_id, output_file):
        \"\"\"Download job results\"\"\"
        response = requests.get(
            f'{self.base_url}/api/v1/jobs/{job_id}/results',
            headers=self.headers
        )
        with open(output_file, 'wb') as f:
            f.write(response.content)

# Usage example
client = BusMatrixClient('http://localhost:8080', 'your-api-key')

# Create configuration
config = {
    'global_config': {'protocol': 'AXI4', 'data_width': 128},
    'masters': [{'name': 'cpu', 'type': 'cpu'}],
    'slaves': [{'name': 'memory', 'base_address': '0x00000000', 'size': '0x40000000'}]
}

result = client.create_configuration('Test Design', config)
config_id = result['id']

# Generate RTL
job = client.generate_rtl(config_id, {
    'target_language': 'systemverilog',
    'include_testbench': True
})
job_id = job['job_id']

# Monitor job
import time
while True:
    status = client.get_job_status(job_id)
    print(f"Job status: {status['status']} ({status['progress']}%)")
    
    if status['status'] in ['completed', 'failed']:
        break
    
    time.sleep(5)

# Download results
if status['status'] == 'completed':
    client.download_results(job_id, 'rtl_output.zip')
    print("RTL generation completed and downloaded!")

JavaScript Client:
class BusMatrixClient {
    constructor(baseUrl, apiKey) {
        this.baseUrl = baseUrl;
        this.headers = {
            'Authorization': `Bearer ${apiKey}`,
            'Content-Type': 'application/json'
        };
    }
    
    async createConfiguration(name, config) {
        const response = await fetch(`${this.baseUrl}/api/v1/configurations`, {
            method: 'POST',
            headers: this.headers,
            body: JSON.stringify({
                name: name,
                configuration: config
            })
        });
        return await response.json();
    }
    
    async generateRTL(configId, options = {}) {
        const response = await fetch(
            `${this.baseUrl}/api/v1/configurations/${configId}/generate/rtl`,
            {
                method: 'POST',
                headers: this.headers,
                body: JSON.stringify({ options })
            }
        );
        return await response.json();
    }
    
    async getJobStatus(jobId) {
        const response = await fetch(`${this.baseUrl}/api/v1/jobs/${jobId}`, {
            headers: this.headers
        });
        return await response.json();
    }
}

// Usage
const client = new BusMatrixClient('http://localhost:8080', 'your-api-key');

// Async function to handle generation
async function generateDesign() {
    try {
        // Create configuration
        const config = {
            global_config: { protocol: 'AXI4', data_width: 128 },
            masters: [{ name: 'cpu', type: 'cpu' }],
            slaves: [{ name: 'memory', base_address: '0x00000000', size: '0x40000000' }]
        };
        
        const result = await client.createConfiguration('JS Test Design', config);
        console.log('Configuration created:', result.id);
        
        // Generate RTL
        const job = await client.generateRTL(result.id, {
            target_language: 'systemverilog',
            include_testbench: true
        });
        console.log('RTL generation started:', job.job_id);
        
        // Monitor job (simplified)
        const status = await client.getJobStatus(job.job_id);
        console.log('Job status:', status);
        
    } catch (error) {
        console.error('Error:', error);
    }
}

INTEGRATION PATTERNS:

CI/CD Integration (Jenkins):
pipeline {
    agent any
    
    environment {
        BUS_MATRIX_API_KEY = credentials('bus-matrix-api-key')
        BUS_MATRIX_URL = 'http://bus-matrix-server:8080'
    }
    
    stages {
        stage('Validate Configuration') {
            steps {
                script {
                    def response = sh(
                        script: '''
                            curl -X POST \\
                                -H "Authorization: Bearer \${BUS_MATRIX_API_KEY}" \\
                                -H "Content-Type: application/json" \\
                                -d @design.json \\
                                \${BUS_MATRIX_URL}/api/v1/configurations/\${BUILD_ID}/validate
                        ''',
                        returnStdout: true
                    )
                    def result = readJSON text: response
                    if (!result.valid) {
                        error("Configuration validation failed: \${result.errors}")
                    }
                }
            }
        }
        
        stage('Generate RTL') {
            steps {
                script {
                    // Start RTL generation
                    def jobResponse = sh(
                        script: '''
                            curl -X POST \\
                                -H "Authorization: Bearer \${BUS_MATRIX_API_KEY}" \\
                                -H "Content-Type: application/json" \\
                                -d '{"options": {"include_testbench": true}}' \\
                                \${BUS_MATRIX_URL}/api/v1/configurations/\${BUILD_ID}/generate/rtl
                        ''',
                        returnStdout: true
                    )
                    def job = readJSON text: jobResponse
                    
                    // Wait for completion
                    timeout(time: 30, unit: 'MINUTES') {
                        waitUntil {
                            def statusResponse = sh(
                                script: '''
                                    curl -H "Authorization: Bearer \${BUS_MATRIX_API_KEY}" \\
                                        \${BUS_MATRIX_URL}/api/v1/jobs/\${job.job_id}
                                ''',
                                returnStdout: true
                            )
                            def status = readJSON text: statusResponse
                            return status.status in ['completed', 'failed']
                        }
                    }
                    
                    # Download results
                    # sh command:
                    # curl -H "Authorization: Bearer ${BUS_MATRIX_API_KEY}"
                    #     -o rtl_output.zip
                    #     ${BUS_MATRIX_URL}/api/v1/jobs/${job.job_id}/results
                }
            }
        }
    }
    
    post {
        always {
            archiveArtifacts artifacts: 'rtl_output.zip', fingerprint: true
        }
    }
}

Docker Integration:
# Dockerfile for API server:
# FROM python:3.9-slim
# WORKDIR /app
# COPY requirements.txt .
# RUN pip install -r requirements.txt
# COPY . .
# EXPOSE 8080
# CMD ["python", "-m", "bus_matrix_tool.api_server", "--host", "0.0.0.0", "--port", "8080"]

# docker-compose.yml:
# version: '3.8'
# services:
#   bus-matrix-api:
#     build: .
#     ports:
#       - "8080:8080"
#     environment:
#       - BUS_MATRIX_LICENSE_FILE=/app/license.dat
#       - BUS_MATRIX_LOG_LEVEL=INFO
#     volumes:
#       - ./data:/var/lib/bus_matrix_tool
#       - ./license.dat:/app/license.dat:ro
#   redis:
#     image: redis:alpine
#     ports:
#       - "6379:6379"
#   nginx:
#     image: nginx:alpine
#     ports:
#       - "80:80"
#     volumes:
#       - ./nginx.conf:/etc/nginx/nginx.conf:ro
#     depends_on:
#       - bus-matrix-api
"""
    pdf_generator.create_text_page(pdf, "8.3 REST API", None, rest_api, code_style=True)
    
    # Page 89: Configuration File Formats and Schemas
    config_formats = """
8.4 Configuration File Formats and Schemas

JSON CONFIGURATION SCHEMA:

Complete JSON Schema:
{
  "$schema": "http://json-schema.org/draft-07/schema#",
  "title": "AMBA Bus Matrix Configuration",
  "type": "object",
  "required": ["global_config", "masters", "slaves"],
  "properties": {
    "project_info": {
      "type": "object",
      "properties": {
        "name": {"type": "string", "maxLength": 64},
        "version": {"type": "string", "pattern": "^\\\\d+\\\\.\\\\d+\\\\.\\\\d+$"},
        "description": {"type": "string", "maxLength": 256},
        "author": {"type": "string", "maxLength": 64},
        "created": {"type": "string", "format": "date-time"},
        "modified": {"type": "string", "format": "date-time"}
      }
    },
    "global_config": {
      "type": "object",
      "required": ["protocol", "data_width", "addr_width"],
      "properties": {
        "protocol": {
          "type": "string", 
          "enum": ["AXI4", "AXI3", "AHB", "APB"]
        },
        "data_width": {
          "type": "integer",
          "enum": [8, 16, 32, 64, 128, 256, 512, 1024]
        },
        "addr_width": {
          "type": "integer",
          "minimum": 12, "maximum": 64
        },
        "endianness": {
          "type": "string",
          "enum": ["little", "big"]
        }
      }
    },
    "masters": {
      "type": "array",
      "minItems": 2,
      "maxItems": 32,
      "items": {
        "$ref": "#/definitions/master"
      }
    },
    "slaves": {
      "type": "array", 
      "minItems": 2,
      "maxItems": 64,
      "items": {
        "$ref": "#/definitions/slave"  
      }
    },
    "interconnect": {
      "$ref": "#/definitions/interconnect_config"
    },
    "advanced_features": {
      "$ref": "#/definitions/advanced_features"
    }
  },
  "definitions": {
    "master": {
      "type": "object",
      "required": ["id", "name"],
      "properties": {
        "id": {"type": "integer", "minimum": 0},
        "name": {"type": "string", "pattern": "^[a-zA-Z][a-zA-Z0-9_]*$"},
        "type": {
          "type": "string",
          "enum": ["cpu", "dma", "gpu", "dsp", "accelerator", "debug", "custom"]
        },
        "max_outstanding": {
          "type": "integer", "minimum": 1, "maximum": 256
        },
        "id_width": {
          "type": "integer", "minimum": 1, "maximum": 16
        },
        "data_width": {
          "type": "integer",
          "enum": [8, 16, 32, 64, 128, 256, 512, 1024]
        },
        "qos_config": {
          "type": "object",
          "properties": {
            "default_qos": {"type": "integer", "minimum": 0, "maximum": 15},
            "qos_override": {"type": "boolean"},
            "priority_class": {"type": "string"}
          }
        },
        "user_signals": {
          "type": "object", 
          "properties": {
            "awuser_width": {"type": "integer", "minimum": 0, "maximum": 1024},
            "wuser_width": {"type": "integer", "minimum": 0, "maximum": 1024},
            "buser_width": {"type": "integer", "minimum": 0, "maximum": 1024},
            "aruser_width": {"type": "integer", "minimum": 0, "maximum": 1024},
            "ruser_width": {"type": "integer", "minimum": 0, "maximum": 1024}
          }
        }
      }
    },
    "slave": {
      "type": "object",
      "required": ["id", "name", "address_config"],
      "properties": {
        "id": {"type": "integer", "minimum": 0},
        "name": {"type": "string", "pattern": "^[a-zA-Z][a-zA-Z0-9_]*$"},
        "type": {
          "type": "string",
          "enum": ["memory", "peripheral", "bridge", "custom"]
        },
        "address_config": {
          "type": "object",
          "required": ["base_address", "size"],
          "properties": {
            "base_address": {
              "type": "string", 
              "pattern": "^0x[0-9A-Fa-f]+$"
            },
            "size": {
              "type": "string",
              "pattern": "^0x[0-9A-Fa-f]+$"
            }
          }
        },
        "data_width": {
          "type": "integer",
          "enum": [8, 16, 32, 64, 128, 256, 512, 1024]
        }
      }
    }
  }
}

XML CONFIGURATION FORMAT:

XML Schema (XSD):
<?xml version="1.0" encoding="UTF-8"?>
<xs:schema xmlns:xs="http://www.w3.org/2001/XMLSchema"
           targetNamespace="http://bus-matrix-tool.org/config/v1"
           xmlns:bm="http://bus-matrix-tool.org/config/v1"
           elementFormDefault="qualified">

  <xs:element name="bus_matrix_config">
    <xs:complexType>
      <xs:sequence>
        <xs:element name="project" type="bm:ProjectInfo" minOccurs="0"/>
        <xs:element name="global" type="bm:GlobalConfig"/>
        <xs:element name="masters" type="bm:Masters"/>
        <xs:element name="slaves" type="bm:Slaves"/>
        <xs:element name="interconnect" type="bm:Interconnect" minOccurs="0"/>
        <xs:element name="advanced_features" type="bm:AdvancedFeatures" minOccurs="0"/>
      </xs:sequence>
      <xs:attribute name="version" type="xs:string" use="required"/>
    </xs:complexType>
  </xs:element>

  <xs:complexType name="GlobalConfig">
    <xs:attribute name="protocol" use="required">
      <xs:simpleType>
        <xs:restriction base="xs:string">
          <xs:enumeration value="AXI4"/>
          <xs:enumeration value="AXI3"/>
          <xs:enumeration value="AHB"/>
          <xs:enumeration value="APB"/>
        </xs:restriction>
      </xs:simpleType>
    </xs:attribute>
    <xs:attribute name="data_width" type="bm:DataWidthType" use="required"/>
    <xs:attribute name="addr_width" use="required">
      <xs:simpleType>
        <xs:restriction base="xs:integer">
          <xs:minInclusive value="12"/>
          <xs:maxInclusive value="64"/>
        </xs:restriction>
      </xs:simpleType>
    </xs:attribute>
  </xs:complexType>

  <xs:simpleType name="DataWidthType">
    <xs:restriction base="xs:integer">
      <xs:enumeration value="8"/>
      <xs:enumeration value="16"/>
      <xs:enumeration value="32"/>
      <xs:enumeration value="64"/>
      <xs:enumeration value="128"/>
      <xs:enumeration value="256"/>
      <xs:enumeration value="512"/>
      <xs:enumeration value="1024"/>
    </xs:restriction>
  </xs:simpleType>

</xs:schema>

Example XML Configuration:
<?xml version="1.0" encoding="UTF-8"?>
<bus_matrix_config xmlns="http://bus-matrix-tool.org/config/v1" version="2.0">
  <project name="automotive_soc" version="2.1.0" 
           description="Main SoC interconnect"/>
  
  <global protocol="AXI4" data_width="128" addr_width="40"/>
  
  <masters>
    <master id="0" name="cortex_a78_core0" type="cpu" 
            max_outstanding="32" id_width="5">
      <qos_config default_qos="8" priority_class="performance"/>
      <user_signals awuser_width="8" aruser_width="8"/>
    </master>
    
    <master id="1" name="dma_controller" type="dma"
            max_outstanding="64" id_width="6">
      <qos_config default_qos="4" priority_class="bulk_transfer"/>
    </master>
  </masters>
  
  <slaves>
    <slave id="0" name="ddr4_memory" type="memory" data_width="256">
      <address_config base_address="0x0000000000" size="0x0200000000"/>
      <response_config min_latency="20" typical_latency="35" max_latency="100"/>
    </slave>
    
    <slave id="1" name="sram_memory" type="memory">
      <address_config base_address="0x0400000000" size="0x0001000000"/>
      <response_config min_latency="2" typical_latency="3" max_latency="5"/>
    </slave>
  </slaves>
  
  <interconnect>
    <arbitration algorithm="qos_aware" qos_enabled="true" starvation_timeout="2000"/>
    <pipeline address_stages="2" data_stages="1"/>
    <performance optimization_target="balanced"/>
  </interconnect>
  
  <advanced_features>
    <trustzone enabled="true">
      <secure_masters>0</secure_masters>
      <secure_slaves>1</secure_slaves>
    </trustzone>
    
    <qos enabled="true" bandwidth_regulation="true" urgency_promotion="true"/>
  </advanced_features>
</bus_matrix_config>

BINARY CONFIGURATION FORMAT:

Binary Format Specification:
The binary format provides compact storage and fast loading for large configurations.

File Structure:
[Header: 32 bytes]
[Global Config: Variable]
[Masters Section: Variable]  
[Slaves Section: Variable]
[Interconnect Section: Variable]
[Advanced Features: Variable]
[Checksum: 4 bytes]

Header Format (32 bytes):
Offset  Size  Description
0       4     Magic number (0x42534D54 - "BSMT")
4       2     Format version (major.minor)
6       1     Flags (compression, encryption)
7       1     Reserved
8       4     Total file size
12      4     Global config offset
16      4     Masters section offset
20      4     Slaves section offset
24      4     Interconnect offset
28      4     Checksum (CRC32)

Python Binary Format Handler:
import struct
import zlib

class BinaryConfigHandler:
    MAGIC = 0x42534D54  # "BSMT"
    VERSION = 0x0200    # v2.0
    
    def save_binary(self, config, filename):
        \"\"\"Save configuration to binary format\"\"\"
        with open(filename, 'wb') as f:
            # Write header placeholder
            header = bytearray(32)
            f.write(header)
            
            # Write sections and track offsets
            offsets = {}
            
            # Global config
            offsets['global'] = f.tell()
            global_data = self._serialize_global(config['global_config'])
            f.write(global_data)
            
            # Masters
            offsets['masters'] = f.tell()
            masters_data = self._serialize_masters(config['masters'])
            f.write(masters_data)
            
            # Slaves
            offsets['slaves'] = f.tell()
            slaves_data = self._serialize_slaves(config['slaves'])
            f.write(slaves_data)
            
            # Calculate checksum
            f.seek(32)  # Skip header
            data = f.read()
            checksum = zlib.crc32(data) & 0xffffffff
            
            # Write actual header
            f.seek(0)
            header = struct.pack('<IHHI' + 'I' * 6,
                self.MAGIC,           # Magic number
                self.VERSION,         # Version
                0,                    # Flags
                len(data) + 32,       # Total size
                offsets['global'],    # Global offset
                offsets['masters'],   # Masters offset
                offsets['slaves'],    # Slaves offset
                0,                    # Interconnect offset
                checksum,             # Checksum
                0                     # Reserved
            )
            f.write(header)
    
    def load_binary(self, filename):
        \"\"\"Load configuration from binary format\"\"\"
        with open(filename, 'rb') as f:
            # Read and validate header
            header = f.read(32)
            magic, version, flags, total_size, global_off, masters_off, slaves_off, ic_off, checksum, reserved = \\
                struct.unpack('<IHHI' + 'I' * 6, header)
            
            if magic != self.MAGIC:
                raise ValueError("Invalid binary format")
            
            # Verify checksum
            data = f.read()
            if zlib.crc32(data) & 0xffffffff != checksum:
                raise ValueError("Checksum verification failed")
            
            # Parse sections
            config = {}
            
            f.seek(global_off)
            config['global_config'] = self._deserialize_global(f)
            
            f.seek(masters_off)
            config['masters'] = self._deserialize_masters(f)
            
            f.seek(slaves_off)  
            config['slaves'] = self._deserialize_slaves(f)
            
            return config

FORMAT CONVERSION UTILITIES:

python3 -m bus_matrix_tool.formats convert \\
    --input design.json --output design.xml

python3 -m bus_matrix_tool.formats convert \\
    --input design.xml --output design.bmcfg --format binary

python3 -m bus_matrix_tool.formats validate \\
    --file design.json --schema axi4.schema.json

python3 -m bus_matrix_tool.formats info \\
    --file design.bmcfg

CONFIGURATION MIGRATION:

Version 1.x to 2.x Migration:
#!/usr/bin/env python3
\"\"\"Configuration migration utility\"\"\"

def migrate_v1_to_v2(old_config):
    \"\"\"Migrate v1.x configuration to v2.x format\"\"\"
    new_config = {
        'project_info': {
            'name': old_config.get('name', 'Migrated Design'),
            'version': '2.0.0',
            'created': datetime.now().isoformat()
        },
        'global_config': {
            'protocol': old_config['protocol'],
            'data_width': old_config['bus_width'],  # Renamed field
            'addr_width': old_config.get('address_width', 32)
        },
        'masters': [],
        'slaves': []
    }
    
    # Migrate masters
    for old_master in old_config['masters']:
        new_master = {
            'id': old_master['id'],
            'name': old_master['name'],
            'type': old_master.get('type', 'custom'),
            'max_outstanding': old_master.get('outstanding_limit', 16),
            'id_width': old_master.get('id_bits', 4)
        }
        
        # Convert old QoS format
        if 'priority' in old_master:
            new_master['qos_config'] = {
                'default_qos': old_master['priority'],
                'qos_override': True
            }
        
        new_config['masters'].append(new_master)
    
    # Migrate slaves  
    for old_slave in old_config['slaves']:
        new_slave = {
            'id': old_slave['id'],
            'name': old_slave['name'],
            'type': old_slave.get('type', 'custom'),
            'address_config': {
                'base_address': old_slave['base_addr'],
                'size': old_slave['addr_size']
            }
        }
        new_config['slaves'].append(new_slave)
    
    return new_config

# Usage
with open('old_config.json', 'r') as f:
    old_config = json.load(f)

new_config = migrate_v1_to_v2(old_config)

with open('new_config.json', 'w') as f:
    json.dump(new_config, f, indent=2)
"""
    pdf_generator.create_text_page(pdf, "8.4 Configuration Formats", None, config_formats, code_style=True)

# This function can be integrated into the main PDF generator