# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

This is the gen_amba_2025 project - a set of C programs that generate synthesizable Verilog RTL for AMBA bus systems (AXI4/AXI3, AHB, APB). The project consists of three code generators that create parameterizable bus interconnects and bridges.

## Build Commands

### Building the Generators
```bash
# Build all generators
make

# Build specific generator
cd gen_amba_axi && make
cd gen_amba_ahb && make  
cd gen_amba_apb && make

# Clean build
make cleanup    # removes executables and objects
make cleanupall # complete clean including generated files
```

### Running the Generators
```bash
# Generate AXI bus (default AXI4, use --axi3 for AXI3)
./gen_amba_axi --master=2 --slave=3 --output=amba_axi_m2s3.v

# Generate AHB bus  
./gen_amba_ahb --mst=2 --slv=3 --out=amba_ahb_m2s3.v

# Generate APB bridge (from AXI or AHB)
./gen_amba_apb --axi --slave=4 --out=axi_to_apb_s4.v
./gen_amba_apb --ahb --slave=4 --out=ahb_to_apb_s4.v
```

## Verification and Testing

### Running Simulations
```bash
# Example: AXI verification with Icarus Verilog
cd gen_amba_axi/verification/sim/iverilog
make MST=2 SLV=3    # 2 masters, 3 slaves

# Example: AHB verification with Vivado XSIM
cd gen_amba_ahb/verification/sim/xsim
make MST=2 SLV=2 SIZE=1024

# View waveforms
gtkwave wave.vcd
```

### Generate Top-Level Testbenches
```bash
cd gen_amba_axi/verification
./gen_axi_top.sh -mst 2 -slv 3 -siz 1024 -out top.v

cd gen_amba_ahb/verification  
./gen_ahb_top.sh -mst 2 -slv 3 -siz 1024 -out top.v
```

### Test Scenarios
- Modify test parameters in `sim_define.v` (WIDTH_AD, WIDTH_DA)
- Enable specific tests with plusargs: `+BURST_TEST=1`
- Add custom test scenarios in `axi_tester.v` or `ahb_tester.v`

## Architecture Overview

### Code Generation Flow
Each generator follows the pattern:
```
main.c → arg_parser.c → gen_xxx_amba.c → component generators
```

### Generator Components

**AXI Generator** (`gen_amba_axi/src/`):
- `gen_axi_amba.c` - Top-level orchestrator
- `gen_axi_mtos.c` - Master-to-slave interconnect
- `gen_axi_stom.c` - Slave-to-master interconnect
- `gen_axi_arbiter_*.c` - Arbitration logic
- `gen_axi_default_slave.c` - DECERR response generator
- `gen_axi_wid.c` - Write ID management (AXI3)

**AHB Generator** (`gen_amba_ahb/src/`):
- `gen_ahb_amba.c` - Top-level orchestrator
- `gen_ahb_arbiter.c` - Bus arbitration
- `gen_ahb_m2s.c` - Master-to-slave mux
- `gen_ahb_s2m.c` - Slave-to-master mux
- `gen_ahb_decoder.c` - Address decoder
- `gen_ahb_lite.c` - AHB-Lite variant

**APB Generator** (`gen_amba_apb/src/`):
- `gen_apb_amba.c` - APB bus generator
- `gen_ahb2apb_*.c` - AHB-to-APB bridge components
- `gen_axi2apb_*.c` - AXI-to-APB bridge components
- `gen_apb_decoder.c` - Address decoder
- `gen_apb_mux.c` - Response multiplexer

### Key Architectural Patterns

1. **Parameterization**: All generated modules use Verilog parameters for flexibility
2. **Memory Mapping**: Configurable base addresses and sizes for each slave
3. **Protocol Support**: 
   - AXI: Both AXI3 (with WID) and AXI4 supported
   - APB: APB3 (PREADY/PSLVERR) and APB4 (PPROT/PSTRB) supported
4. **Prefix Support**: `--prefix` option prevents module name conflicts when using multiple buses

### Verification Infrastructure

**Bus Functional Models (BFMs)**:
- `axi_master_tasks.v` - AXI transaction tasks (read/write)
- `ahb_tasks.v` - AHB transaction tasks
- Memory models: `mem_axi.v`, `mem_ahb.v`, `mem_apb.v`

**Protocol Converters** (in `gen_amba_axi/verification/ip/`):
- `axi3to4.v` - AXI3 to AXI4 converter
- `axi4to3.v` - AXI4 to AXI3 converter

## Important Constraints

- AXI generator requires minimum 2 masters and 2 slaves
- AHB-Lite is automatically generated when master count is 1
- All generators produce synthesizable RTL targeting FPGA/ASIC
- Generated code includes BSD 2-clause license footer

## Platform Detection

The build system automatically detects:
- Linux (32/64-bit)
- Windows via Cygwin
- Windows via MinGW

Platform-specific flags are set in Makefiles for proper compilation.