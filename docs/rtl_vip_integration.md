# RTL and VIP Integration Guide

## Overview

The gen_amba_2025 project now supports seamless integration between generated RTL and the SystemVerilog/UVM Verification IP (VIP). This allows you to verify your generated AXI4 interconnect RTL using the comprehensive VIP test environment.

## Features

### 1. Dual Mode VIP
The VIP supports two modes of operation:

- **Behavioral Mode (Default)**: Uses a behavioral model of the interconnect for fast simulation
- **RTL Mode**: Integrates your generated RTL interconnect for accurate verification

### 2. GUI Integration
The Bus Matrix GUI now includes:
- VIP mode selection (Behavioral vs RTL)
- RTL path configuration
- One-click RTL generation for VIP
- Automated UVM configuration export

### 3. Seamless Flow
1. Design your bus matrix in the GUI
2. Generate RTL with one click
3. Select RTL mode in VIP settings
4. Export UVM configuration
5. Run comprehensive verification

## Usage

### From GUI

1. **Configure Bus Matrix**
   - Add masters and slaves
   - Set up address mapping
   - Configure arbitration

2. **Navigate to VIP Tab**
   - Click on "UVM Export" tab
   - Select "RTL Integration (Generated RTL)"
   - Click "Generate RTL First" button

3. **Export Configuration**
   - Click "Export UVM Config"
   - Configuration files will be generated in `axi4_vip_sim/output/`

4. **Run Simulation**
   ```bash
   cd axi4_vip_sim
   make run TEST=axi4_basic_test CONFIG_FILE=output/configs/<your_config>.json
   ```

### From Command Line

#### Behavioral Mode (Default)
```bash
make run TEST=axi4_basic_test
```

#### RTL Integration Mode
```bash
make run TEST=axi4_basic_test \
         VIP_MODE=RTL \
         RTL_PATH=output/rtl/axi4_interconnect.v \
         CONFIG_FILE=output/configs/axi4_config.json
```

### Using Test Script
A complete test script is provided:
```bash
./test_rtl_integration.sh
```

This script:
1. Generates RTL from a sample configuration
2. Exports UVM configuration with RTL mode
3. Runs the VIP test with RTL integration
4. Reports pass/fail status

## Architecture

### RTL Wrapper
The `axi4_rtl_wrapper.sv` module provides:
- Dynamic selection between behavioral and RTL models
- Proper interface connections
- Parameter propagation from UVM configuration

### Configuration Flow
```
GUI Configuration → JSON Export → UVM Config Reader → RTL Wrapper → DUT
```

### File Structure
```
axi4_vip_sim/
├── src/
│   ├── testbench/
│   │   ├── axi4_rtl_wrapper.sv    # RTL/Behavioral selection
│   │   └── axi4_tb_top.sv         # Updated for multi-mode
│   └── config/
│       └── axi4_config_reader.sv   # Reads VIP mode from JSON
├── output/
│   ├── rtl/                        # Generated RTL files
│   ├── configs/                    # Exported configurations
│   └── logs/                       # Simulation logs
└── Makefile                        # Updated with VIP_MODE support
```

## Makefile Options

New Makefile parameters:
- `VIP_MODE`: Set to `BEHAVIORAL` or `RTL`
- `RTL_PATH`: Path to generated RTL file (required when VIP_MODE=RTL)

Example:
```bash
make help                    # Show all options
make run VIP_MODE=RTL RTL_PATH=my_rtl.v TEST=axi4_basic_test
```

## Benefits

1. **Verification Confidence**: Verify actual generated RTL, not just behavioral models
2. **Bug Detection**: Find RTL-specific issues early
3. **Performance Analysis**: Measure actual RTL timing and throughput
4. **Coverage**: Leverage VIP's comprehensive test suite on your RTL

## Troubleshooting

### RTL Not Found
- Ensure RTL is generated before selecting RTL mode
- Check RTL path is correct
- Verify file permissions

### Compilation Errors
- Check RTL syntax is compatible with your simulator
- Ensure all RTL dependencies are included
- Verify parameter compatibility

### Simulation Failures
- Check address mapping matches between GUI and RTL
- Verify master/slave counts are consistent
- Review simulation logs in `output/logs/`

## Next Steps

1. Try the test script: `./test_rtl_integration.sh`
2. Generate your own RTL and test it
3. Run comprehensive test suite on your RTL
4. Analyze coverage reports