# VIP Environment Setup Feature

## Overview

The VIP Environment Setup feature provides a dialog-based workflow for generating complete verification environments. When you click "Create VIP Environment" in the VIP panel, you can now choose between two modes:

1. **RTL Integration Mode** - For integrating VIP with existing RTL DUT
2. **VIP Standalone Mode** - For self-contained VIP testing

## How to Use

### Step 1: Configure Bus Matrix
First, configure your bus matrix in the main GUI:
- Add masters and slaves
- Set bus parameters (type, width, etc.)
- Configure connections

### Step 2: Open VIP Panel
Click on the VIP panel at the bottom of the GUI to access VIP features.

### Step 3: Create VIP Environment
1. Click the "Create VIP Environment" button
2. The VIP Environment Setup dialog will appear

### Step 4: Select Mode

#### RTL Integration Mode
Choose this when you have an existing RTL DUT that you want to verify:
- Generates testbench templates with DUT instantiation points
- Creates RTL wrapper templates
- Provides connection guides for your RTL

#### VIP Standalone Mode  
Choose this for testing the VIP itself or creating reference models:
- Generates self-contained testbench
- Includes memory model for testing
- Creates loopback configurations

### Step 5: Configure Options
- **Include example test cases** - Generates starter tests
- **Generate documentation** - Creates README files
- **Target Simulator** - Select VCS, Questa, Xcelium, or Vivado

### Step 6: Select Output Directory
After clicking "Next", browse to select where the environment should be generated.

## Generated Directory Structure

### RTL Integration Mode
```
rtl_integration_env/
├── tb/                    # Testbench files
│   ├── top_tb.sv         # Top-level testbench
│   └── tests/            # Test cases
├── vip/                   # VIP components
│   ├── agents/           # VIP agents
│   └── monitors/         # Protocol monitors
├── interfaces/           # Interface definitions
│   └── axi4_interface.sv # AXI4 interface
├── rtl_wrapper/          # RTL integration
│   └── dut_wrapper.sv    # DUT wrapper template
├── configs/              # Configuration files
│   └── bus_config.json   # Bus configuration
├── scripts/              # Build/run scripts
│   ├── compile.sh        # Compilation script
│   └── run_test.sh       # Test execution script
└── docs/                 # Documentation
    └── README.md         # Setup instructions
```

### VIP Standalone Mode
```
vip_standalone_env/
├── tb/                    # Testbench files
│   ├── top_tb.sv         # Top-level testbench
│   └── tests/            # Test cases
├── vip/                   # VIP components
│   ├── agents/           # VIP agents
│   ├── monitors/         # Protocol monitors
│   └── memory_model/     # Memory for testing
├── interfaces/           # Interface definitions
├── configs/              # Configuration files
├── scripts/              # Build/run scripts
└── docs/                 # Documentation
```

## Next Steps After Generation

### For RTL Integration Mode
1. Copy your RTL files to `rtl_wrapper/`
2. Edit `rtl_wrapper/dut_wrapper.sv` to instantiate your DUT
3. Update filelist.f with your RTL files
4. Run `./scripts/compile.sh` to compile
5. Run `./scripts/run_test.sh axi4_basic_test` to execute tests

### For VIP Standalone Mode
1. Run `./scripts/compile.sh` to compile
2. Run `./scripts/run_test.sh axi4_loopback_test` to execute tests
3. Add custom tests in `tb/tests/`

## Simulator Support

The generated scripts support multiple simulators:
- **VCS** - Synopsys VCS
- **Questa** - Mentor Graphics Questa
- **Xcelium** - Cadence Xcelium
- **Vivado** - Xilinx Vivado Simulator

Scripts are automatically customized based on your selection.

## Tips

- The bus configuration from the GUI is automatically exported to `configs/bus_config.json`
- Generated code uses SystemVerilog interfaces for clean connectivity
- All generated files include helpful TODO comments
- Documentation is generated in Markdown format for easy reading

## Troubleshooting

### Dialog doesn't appear
- Ensure you have configured at least one master and one slave
- Check console for error messages

### Generation fails
- Verify you have write permissions to the selected directory
- Check that the path doesn't contain special characters

### Scripts don't run
- Ensure scripts have execute permissions (should be set automatically)
- Check that your simulator environment variables are set correctly