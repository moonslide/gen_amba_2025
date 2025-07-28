# AMBA Bus Matrix Configuration Tool

A comprehensive Python-based GUI tool for designing, configuring, and generating AMBA AXI4/AXI3/AHB/APB bus interconnects with integrated verification IP (VIP) support.

## Table of Contents

- [Overview](#overview)
- [Features](#features)
- [Architecture](#architecture)
- [Installation](#installation)
- [Quick Start](#quick-start)
- [Usage Guide](#usage-guide)
- [Configuration](#configuration)
- [VIP Integration](#vip-integration)
- [Examples](#examples)
- [API Reference](#api-reference)
- [Troubleshooting](#troubleshooting)
- [Contributing](#contributing)
- [License](#license)

## Overview

The AMBA Bus Matrix Configuration Tool provides a visual interface for designing complex System-on-Chip (SoC) bus architectures. It generates synthesizable RTL for AMBA interconnects and comprehensive UVM-based verification environments.

### Key Capabilities

- **Visual Design**: Drag-and-drop interface for bus matrix design
- **Multi-Protocol Support**: AXI4, AXI3, AHB, and APB protocols
- **RTL Generation**: Synthesizable Verilog with parameterizable configurations
- **VIP Generation**: Complete UVM verification environment
- **Protocol Compliance**: Fully compliant with ARM AMBA specifications

## Features

### Bus Design Features

- **Flexible Topology**: Support for N masters × M slaves configurations
- **Address Mapping**: Visual address space configuration with overlap detection
- **Access Control**: Security and privilege-based access configuration
- **QoS Support**: Quality of Service and priority-based arbitration
- **Protocol Features**: 
  - AXI4: Outstanding transactions, burst support, exclusive access
  - AHB: Multi-layer AHB with arbitration
  - APB: APB3/APB4 with PPROT and PSTRB support

### Code Generation

- **RTL Output**: 
  - Parameterizable Verilog modules
  - Automatic tie-off generation
  - Synthesis-ready code
  - FPGA/ASIC compatible

- **Verification Environment**:
  - UVM 1.2 compliant testbench
  - Configurable BFMs (Bus Functional Models)
  - Constrained random stimulus
  - Functional coverage
  - Protocol checkers
  - Scoreboard and reference model

### GUI Features

- **Interactive Canvas**: Zoom, pan, and grid-snap functionality
- **Templates**: Pre-configured system templates
- **Validation**: Real-time configuration validation
- **Import/Export**: JSON-based configuration files
- **Batch Mode**: Command-line interface for CI/CD integration

## Architecture

```
axi4_vip/gui/
├── src/
│   ├── bus_matrix_gui.py          # Main GUI application
│   ├── bus_config.py              # Configuration data structures
│   ├── axi_verilog_generator.py   # RTL generation engine
│   ├── vip_environment_generator.py # VIP generation engine
│   ├── axi_vip_components.py      # VIP component library
│   ├── axi_test_sequences.py      # Test sequence library
│   ├── address_safety_checker.py  # Address validation
│   ├── uvm_config_exporter.py     # UVM configuration export
│   ├── vip_gui_integration.py     # GUI-VIP integration
│   └── verdi_integration.py       # Debug tool integration
├── templates/                      # System templates
├── tests/                         # Unit tests
├── docs/                          # Documentation
└── examples/                      # Example configurations
```

## Installation

### Prerequisites

- Python 3.6 or higher
- Tkinter (usually included with Python)
- SystemVerilog simulator (VCS, Questa, or Xcelium)
- UVM 1.2 library

### Install Steps

1. Clone the repository:
```bash
cd /home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui
```

2. Install Python dependencies:
```bash
pip install -r requirements.txt
```

3. Verify installation:
```bash
python3 src/bus_matrix_gui.py --version
```

## Quick Start

### 1. Launch the GUI

```bash
./launch_gui.sh
```

### 2. Create a Simple Design

1. Select "AXI4" as the bus type
2. Add masters: Click "Add Master" and configure
3. Add slaves: Click "Add Slave" and set address ranges
4. Connect: Draw connections between masters and slaves
5. Generate: Click "Generate RTL" and "Generate VIP"

### 3. Run Simulation

```bash
cd output/sim
make compile
make run TEST=axi_basic_test
```

## Usage Guide

### Creating a Bus Matrix

#### Step 1: Configure Bus Parameters

```python
# Via GUI
- Set Data Width: 32, 64, 128, 256, 512, 1024 bits
- Set Address Width: 32, 40, 48, 64 bits  
- Select Arbitration: Fixed, Round-Robin, QoS-based
```

#### Step 2: Add Masters

Each master can be configured with:
- **Name**: Descriptive identifier
- **ID Width**: Transaction ID bits (affects outstanding capability)
- **QoS Support**: Enable quality of service
- **Exclusive Access**: Enable exclusive transactions
- **User Width**: Custom sideband signals
- **Priority**: Arbitration priority
- **Protection**: Default AxPROT value

#### Step 3: Add Slaves

Each slave requires:
- **Name**: Descriptive identifier
- **Base Address**: Starting address (must be aligned)
- **Size**: Address range size
- **Memory Type**: Memory or Peripheral
- **Latency**: Read/write latency cycles
- **Security**: Access restrictions
- **Regions**: Number of protection regions

#### Step 4: Configure Connections

- Click and drag to connect masters to slaves
- Right-click connections to set specific routing parameters
- Use the access matrix to configure per-master/slave permissions

### Generating Output

#### RTL Generation

```bash
# GUI Method
Click "Generate RTL" button

# Command Line
python3 src/axi_verilog_generator.py --config my_design.json --output rtl_output/
```

Generated files:
- `axi4_interconnect_mNsM.v` - Top-level interconnect
- `axi4_address_decoder.v` - Address decoding logic
- `axi4_arbiter.v` - Arbitration logic
- `axi4_router.v` - Transaction routing
- `tb_axi4_interconnect.v` - Basic testbench

#### VIP Generation

```bash
# GUI Method
Click "Generate VIP" button

# Command Line  
python3 src/vip_environment_generator.py --config my_design.json --output vip_output/
```

Generated structure:
```
vip_output/
├── env/           # UVM environment
├── tests/         # Test library
├── sequences/     # Sequence library
├── tb/           # Testbench top
├── sim/          # Simulation scripts
└── docs/         # Generated documentation
```

## Configuration

### JSON Configuration Format

```json
{
  "bus_type": "AXI4",
  "data_width": 128,
  "addr_width": 40,
  "arbitration": "QOS",
  "masters": [
    {
      "name": "CPU_0",
      "id_width": 6,
      "qos_support": true,
      "exclusive_support": true,
      "user_width": 4,
      "priority": 15,
      "default_prot": 2,
      "default_cache": 3,
      "default_region": 0
    }
  ],
  "slaves": [
    {
      "name": "DDR_Controller",
      "base_address": 0,
      "size": 8388608,
      "memory_type": "Memory",
      "read_latency": 20,
      "write_latency": 10,
      "num_regions": 4,
      "secure_only": false,
      "privileged_only": false
    }
  ]
}
```

### Environment Variables

```bash
# Simulator selection
export AXI_VIP_SIMULATOR=vcs  # or questa, xcelium

# UVM library path
export UVM_HOME=/path/to/uvm-1.2

# Waveform format
export AXI_VIP_WAVES=fsdb  # or vcd, shm

# Debug level
export AXI_VIP_DEBUG=1  # Enable debug messages
```

## VIP Integration

### Test Development

Create custom tests by extending the base test class:

```systemverilog
class my_custom_test extends axi_base_test;
  `uvm_component_utils(my_custom_test)
  
  function new(string name = "my_custom_test", uvm_component parent);
    super.new(name, parent);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    my_sequence seq;
    phase.raise_objection(this);
    
    seq = my_sequence::type_id::create("seq");
    seq.start(env.vsequencer);
    
    phase.drop_objection(this);
  endtask
endclass
```

### Sequence Development

```systemverilog
class burst_sequence extends axi_base_sequence;
  `uvm_object_utils(burst_sequence)
  
  function new(string name = "burst_sequence");
    super.new(name);
  endfunction
  
  virtual task body();
    axi_transaction tr;
    
    `uvm_do_with(tr, {
      tr.burst_type == INCR;
      tr.burst_length == 16;
      tr.size == 3'b011; // 8 bytes
    })
  endtask
endclass
```

## Examples

### Example 1: Simple 2×3 System

```bash
# Load template
./launch_gui.sh --template templates/simple_axi4_2m3s.json

# Or create from scratch
python3 examples/create_simple_system.py
```

### Example 2: Complex SoC Design

```bash
# High-performance computing system
./launch_gui.sh --template templates/complex_axi4_system.json

# Features:
# - 8 masters (CPU clusters, GPU, DMA, PCIe)
# - 8 slaves (DDR, SRAM, peripherals)
# - QoS-based arbitration
# - Security zones
```

### Example 3: Mixed Protocol System

```bash
# AXI4 to APB bridge system
python3 examples/create_mixed_protocol.py
```

## API Reference

### Core Classes

#### BusConfig
```python
class BusConfig:
    """Main bus configuration container"""
    def __init__(self)
    def add_master(self, master: Master)
    def add_slave(self, slave: Slave)
    def validate(self) -> List[str]
    def export_json(self, filename: str)
    def import_json(self, filename: str)
```

#### AXIVerilogGenerator
```python
class AXIVerilogGenerator:
    """RTL generation engine"""
    def __init__(self, config: BusConfig)
    def generate(self) -> str  # Returns output directory
    def generate_interconnect(self)
    def generate_arbiter(self)
    def generate_decoder(self)
```

#### VIPEnvironmentGenerator
```python
class VIPEnvironmentGenerator:
    """VIP generation engine"""
    def __init__(self, config: BusConfig, mode: str)
    def generate_full_environment(self, output_dir: str, 
                                 project_name: str,
                                 num_masters: int,
                                 num_slaves: int)
```

## Troubleshooting

### Common Issues

#### 1. Port Width Mismatch Warnings

**Problem**: Lint warnings about port connection width mismatches
```
Lint-[PCWM-L] Port connection width mismatch
```

**Solution**: The tool now generates parameterized ID_WIDTH. Regenerate your RTL.

#### 2. Python Module Import Errors

**Problem**: ImportError when launching GUI
```
ImportError: No module named 'tkinter'
```

**Solution**: Install tkinter
```bash
# Ubuntu/Debian
sudo apt-get install python3-tk

# CentOS/RHEL
sudo yum install python3-tkinter
```

#### 3. Simulation Compilation Errors

**Problem**: UVM package not found
```
Error: Package 'uvm_pkg' not found
```

**Solution**: Set UVM_HOME environment variable
```bash
export UVM_HOME=/path/to/uvm-1.2
```

#### 4. Address Overlap Detection

**Problem**: GUI shows address overlap error

**Solution**: 
- Check slave address ranges don't overlap
- Ensure base addresses are properly aligned
- Use the address map viewer to visualize

### Debug Features

#### Enable Debug Logging
```bash
export AXI_VIP_DEBUG=1
./launch_gui.sh
```

#### Waveform Debugging
```bash
# Generate FSDB for Verdi
make run_fsdb TEST=my_test

# Auto-load in Verdi
make verdi
```

#### Protocol Checking
The VIP includes built-in protocol checkers. Enable with:
```systemverilog
env.enable_protocol_checks = 1;
```

## Contributing

We welcome contributions! Please see our [Contributing Guide](CONTRIBUTING.md) for details.

### Development Setup

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests
5. Submit a pull request

### Coding Standards

- Python: PEP 8 style guide
- SystemVerilog: IEEE 1800-2017 standard
- Documentation: Markdown with examples

## License

This project is licensed under the BSD 2-Clause License. See [LICENSE](LICENSE) file for details.

## Support

- **Documentation**: See `docs/` directory
- **Examples**: See `examples/` directory  
- **Issues**: Submit via GitHub issues
- **Email**: support@amba-tools.com

## Acknowledgments

- ARM for the AMBA protocol specifications
- Accellera for SystemVerilog and UVM standards
- Contributors and users of this tool

---

For more detailed information, see the [PDF User Guide](userguide.pdf) or run:
```bash
python3 src/bus_matrix_gui.py --help
```