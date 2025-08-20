# Technical Documentation - GEN_AMBA_2025

## Project Overview
GEN_AMBA_2025 is a comprehensive AMBA bus generator suite that creates synthesizable Verilog RTL for AXI4/AXI3, AHB, and APB bus systems. Enhanced with a full UVM-based verification IP suite and GUI interface.

## Key Components

### 1. Core Generators
- **gen_amba_axi**: AXI4/AXI3 interconnect generator
- **gen_amba_ahb**: AHB bus generator  
- **gen_amba_apb**: APB bridge generator

### 2. Verification IP Suite
- Complete UVM environment with BFMs
- 80+ test sequences
- Traffic monitoring and analysis
- Support for 2x2 to 64x64 matrices

### 3. GUI Interface
- Visual bus matrix configuration
- Real-time generation
- Project management capabilities

## Recent Bug Fixes (August 2025)

### W-Channel Routing Bug Fix
**Problem**: Write data was routing to wrong slave in multi-slave configurations

**Root Cause**: The arbiter was only checking the Master ID portion of the transaction ID instead of the full transaction ID.

**Location**: `gen_amba_axi/src/gen_axi_arbiter_mtos.c` lines 438-441

**Fix Applied**:
```c
// Before (incorrect):
if (fifo_pop_dout[WIDTH_SID-1:WIDTH_ID]==MID0) WGRANT = 2'h1;

// After (correct):
if (fifo_pop_dout==WSID0) WGRANT = 2'h1;
```

### Timescale Directive Addition
**Location**: `gen_amba_axi/src/main.c` line 50
**Fix**: Added `timescale 1ns/1ps` to all generated RTL files

### Slave Timing Fix
**Problem**: Slave read data showing X's when sampled by master
**Fix**: Modified slave read logic to set data immediately when accepting read request

## Enhanced Features

### Unified Testbench Generator
New script `gen_axi_with_tb.sh` generates both RTL and testbench:
```bash
./gen_axi_with_tb.sh --master=2 --slave=3 --output=design.v --tb=testbench.v
```

Test modes available:
- SIMPLE: Basic read/write test
- COMPREHENSIVE: Multiple addresses and slaves
- BURST: Burst transfer testing
- SLAVE: Slave-specific tests
- STRESS: Performance testing
- ALL: Run all test scenarios

### GUI Capabilities
- Visual bus matrix design
- Drag-and-drop interface
- Real-time validation
- Direct RTL generation
- VIP integration support

## Architecture Details

### AXI4 Protocol Implementation
- Full AXI4 compliance (IHI0022D specification)
- Support for all burst types (FIXED, INCR, WRAP)
- 4KB boundary enforcement
- Exclusive access support (optional)
- QoS, REGION, USER signal support

### Code Generation Flow
```
main.c → arg_parser.c → gen_axi_amba.c → component generators
                                          ├── gen_axi_mtos.c (master-to-slave)
                                          ├── gen_axi_stom.c (slave-to-master)
                                          ├── gen_axi_arbiter_*.c (arbitration)
                                          └── gen_axi_default_slave.c (DECERR)
```

### Verification Infrastructure
- Bus Functional Models (BFMs) in `verification/ip/`
- Memory models for AXI, AHB, APB
- Protocol converters (AXI3↔AXI4)
- Comprehensive test scenarios

## File Structure

```
gen_amba_2025/
├── gen_amba_axi/          # AXI generator
│   ├── src/               # Source code
│   ├── verification/      # Test infrastructure
│   └── gen_axi_with_tb.sh # Enhanced generator script
├── gen_amba_ahb/          # AHB generator
├── gen_amba_apb/          # APB generator
├── axi4_vip/              # Verification IP suite
│   ├── gui/               # Original GUI
│   └── gui_v3/            # Streamlined GUI
├── external/tim_axi4_vip/ # Reference VIP
├── doc/                   # Documentation
├── README.md              # Main documentation
├── CLAUDE.md              # AI assistant guidance
└── COMPLETE_FLOW_TEST_REPORT.md # Test verification
```

## Testing and Verification

### Compilation
```bash
vcs -full64 -sverilog design.v testbench.v -o simv
```

### Simulation
```bash
./simv +TEST_MODE=ALL +fsdbfile+waves/test.fsdb
```

### Waveform Viewing
```bash
verdi -ssf waves/test.fsdb
```

## Platform Requirements
- Linux (RHEL 8, Ubuntu 20.04+)
- GNU GCC compiler
- Python 3.6+
- HDL simulator (VCS, ModelSim, Xcelium, Vivado XSIM, Icarus)
- Optional: Verdi for waveform viewing

## Known Limitations
1. Minimum 2 masters and 2 slaves for AXI generator
2. Unified testbench may timeout for >2x2 configurations
3. Template path hardcoded in gen_axi_with_tb.sh

## Performance Optimizations
- Automatic optimization for matrices >8x8
- Pure Verilog generation for large configurations
- Memory optimizations for >32x32 matrices
- JVM memory allocation for UVM elaboration

## Support and Contact
- GitHub Issues: https://github.com/anthropics/claude-code/issues
- Original Author: Ando Ki (adki@gmail.com)
- Enhanced by: Claude AI Assistant (2025)

## License
BSD 2-clause license for open and closed source compatibility.

---
*Last Updated: August 20, 2025*