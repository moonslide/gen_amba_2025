# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

This is the gen_amba_2025 project - a set of C programs that generate synthesizable Verilog RTL for AMBA bus systems (AXI4/AXI3, AHB, APB). The project consists of three code generators that create parameterizable bus interconnects and bridges.

### Reference Documentation
- **AMBA AXI Protocol Specification**: `IHI0022D_amba_axi_protocol_spec.pdf` - ARM IHI 0022D specification document
- **Architecture Guide**: `arch.md` - Detailed AXI4 verification IP architecture (Chinese)
- **Development Guide**: `develop.md` - Complete AXI4 implementation guide (Chinese)

### Key AXI Protocol Information (from IHI0022D spec)

#### AXI3 vs AXI4 Differences
- **Burst Length**: AXI4 supports up to 256 transfers for INCR (vs 16 in AXI3)
- **Write Interleaving**: Removed in AXI4 (no WID signal)
- **New Signals**: AXI4 adds QoS, REGION, and USER signals
- **Lock Type**: AXI4 supports only exclusive access (no locked transfers)

#### Critical Implementation Constraints
- **4KB Boundary**: No transaction can cross a 4KB address boundary
- **WRAP Bursts**: Length must be 2, 4, 8, or 16 transfers
- **Exclusive Access**: Maximum 128 bytes, must be power of 2
- **Burst Types**: FIXED (0b00), INCR (0b01), WRAP (0b10)
- **Response Types**: OKAY (0b00), EXOKAY (0b01), SLVERR (0b10), DECERR (0b11)

#### Signal Widths and Ranges
- **Data Bus**: 8, 16, 32, 64, 128, 256, 512, or 1024 bits
- **Burst Size**: 1 to 128 bytes per transfer
- **Burst Length**: 1-256 for INCR (AXI4), 1-16 for others
- **ID Width**: Configurable, typically 4-16 bits
- **Address Width**: Configurable, typically 32 or 64 bits

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

## Development To-Do List

### AXI4 Verification IP Development Tasks

Based on the architecture and development guidelines in `arch.md` and `develop.md`, here are the key implementation tasks for developing a complete AXI4 verification IP suite:

#### Core Signal Implementation
- [ ] Implement AxPROT (Protection Type) signal handling
  - [ ] Complete 3-bit signal transmission in all components
  - [ ] Add access control logic in Slave models
  - [ ] Implement security isolation based on AxPROT[1]
  - [ ] Add configurable memory maps with permission settings
- [ ] Implement QoS (Quality of Service) support
  - [ ] Add 4-bit AxQoS ports to Master and Interconnect
  - [ ] Implement QoS-based arbitration in Interconnect
  - [ ] Maintain AXI ordering rules priority over QoS
  - [ ] Add weighted round-robin or strict priority arbitration
- [ ] Implement AxREGION (Region Identifier) signal
  - [ ] Add region generation logic in Interconnect
  - [ ] Implement region parsing in Slave models
  - [ ] Ensure AxREGION remains constant within 4KB boundaries
  - [ ] Add programmable address-to-region mapping table
- [ ] Implement AxCACHE attribute handling
  - [ ] Handle Modifiable vs Non-modifiable transactions correctly
  - [ ] Implement transaction merging/splitting for Modifiable
  - [ ] Support Bufferable write early response
  - [ ] Add checker for Non-modifiable transaction integrity

#### Functional Logic Implementation
- [ ] Implement Exclusive Access support
  - [ ] Add Exclusive Access Monitor in Slave models
  - [ ] Track exclusive addresses per AXI ID
  - [ ] Implement EXOKAY response generation
  - [ ] Add success/failure path testing
  - [ ] Validate exclusive access restrictions (alignment, size)
- [ ] Implement complete response handling
  - [ ] Support all four responses: OKAY, EXOKAY, SLVERR, DECERR
  - [ ] Add Default Slave for unmapped addresses (DECERR)
  - [ ] Implement error injection capabilities
  - [ ] Add response handling in Master models
- [ ] Implement burst transfer support
  - [ ] Support INCR bursts up to 256 transfers
  - [ ] Implement correct WRAP boundary calculations
  - [ ] Add 4KB boundary crossing detection
  - [ ] Validate FIXED burst address stability
- [ ] Implement Low Power Interface (optional)
  - [ ] Add CSYSREQ, CSYSACK, CACTIVE signals
  - [ ] Implement proper handshake timing
  - [ ] Allow power state request rejection

#### Transaction Processing Implementation
- [ ] Implement AXI ID-based ordering
  - [ ] Add ID tracking in Interconnect and Slave
  - [ ] Enforce same-ID transaction ordering
  - [ ] Support out-of-order completion for different IDs
  - [ ] Implement read/write channel independence
  - [ ] Add in-flight transaction scoreboard
- [ ] Implement AxUSER signal support
  - [ ] Add configurable-width USER ports
  - [ ] Implement transparent pass-through in Interconnect
  - [ ] Handle width mismatches appropriately
  - [ ] Document USER signal usage

#### Verification Environment Components
- [ ] Develop AXI Master Agent
  - [ ] Transaction-level sequence interface
  - [ ] Configurable timing and delays
  - [ ] Support for all burst types
  - [ ] Protocol-compliant signal generation
- [ ] Develop AXI Slave Agent
  - [ ] Memory and peripheral modes
  - [ ] Configurable memory maps
  - [ ] Latency modeling
  - [ ] Backend memory implementation
- [ ] Develop AXI Interconnect model
  - [ ] N-to-M routing capability
  - [ ] Configurable arbitration strategies
  - [ ] Address decoding and mapping
  - [ ] Optional protocol conversion features
- [ ] Develop Monitor and Checker
  - [ ] Signal-level monitoring
  - [ ] Transaction reconstruction
  - [ ] Protocol assertion library
  - [ ] Timing and ordering checks

#### Test Sequence Development
- [ ] Create basic transaction sequences
  - [ ] Single read/write operations
  - [ ] All burst type sequences
  - [ ] Data width and WSTRB combinations
- [ ] Create advanced feature sequences
  - [ ] Out-of-order transaction tests
  - [ ] Same-ID ordering tests
  - [ ] Exclusive access scenarios
  - [ ] QoS/PROT/REGION variations
- [ ] Create error injection sequences
  - [ ] SLVERR trigger scenarios
  - [ ] DECERR trigger scenarios
  - [ ] Illegal burst generation
  - [ ] Protocol violation tests
- [ ] Create stress test scenarios
  - [ ] High throughput tests
  - [ ] Fully randomized scenarios
  - [ ] Multi-master contention
  - [ ] Corner case coverage

#### Documentation and Integration
- [ ] Create comprehensive user documentation
- [ ] Develop integration guidelines
- [ ] Add example testbenches
- [ ] Create regression test suite

#### GUI Development for Bus Matrix Configuration
- [ ] Develop Python GUI application for bus matrix design
  - **Purpose**: Create an intuitive visual tool to design and configure AMBA bus matrices, replacing manual command-line parameter entry with a graphical interface that validates configurations and generates appropriate gen_amba commands or Verilog directly
  - [ ] Create main application framework (tkinter/PyQt/Kivy)
  - [ ] Implement visual bus matrix editor
    - [ ] Drag-and-drop interface for masters/slaves
    - [ ] Visual connection routing
    - [ ] Real-time constraint validation
  - [ ] Add configuration panels
    - [ ] Master configuration (ID width, features)
    - [ ] Slave configuration (address range, memory map)
    - [ ] Interconnect settings (arbitration, QoS)
  - [ ] Implement parameter validation
    - [ ] Check address range conflicts
    - [ ] Validate 4KB boundary rules
    - [ ] Ensure minimum master/slave requirements
  - [ ] Add code generation backend
    - [ ] Generate command-line arguments
    - [ ] Direct Verilog generation option
    - [ ] Export configuration files (JSON/XML)
  - [ ] Create visualization features
    - [ ] Address map visualization
    - [ ] Bandwidth analysis display
    - [ ] Transaction flow animation
  - [ ] Add project management
    - [ ] Save/load bus configurations
    - [ ] Configuration templates
    - [ ] Multi-bus project support

### AXI Protocol Implementation Guidelines (per IHI0022D spec)

#### Channel Handshake Rules
- **Valid Before Ready**: VALID can be asserted before or after READY
- **Valid Stability**: Once VALID is asserted, it must remain high until handshake
- **Ready Default**: READY can have any default value (high or low)
- **No Combinatorial Path**: READY should not depend combinatorially on VALID

#### Address Calculation Formulas
```verilog
// INCR burst address calculation
Address_N = Start_Address + (N × Number_Bytes)

// WRAP burst address calculation  
Wrap_Boundary = (INT(Start_Address / (Number_Bytes × Burst_Length))) × (Number_Bytes × Burst_Length)
// Address wraps back to Wrap_Boundary when it reaches Wrap_Boundary + (Number_Bytes × Burst_Length)

// FIXED burst - address remains constant
Address_N = Start_Address
```

#### Atomic Access Rules (Exclusive)
- Exclusive read marks address/ID pair
- Exclusive write must match read's address/ID
- Any intervening write clears exclusive state
- EXOKAY indicates atomic success, OKAY indicates failure

#### Unaligned Transfer Support
- Use WSTRB for writes to handle unaligned data
- For reads, master must extract relevant bytes
- Address must indicate actual starting byte
- Size must reflect actual transfer width

#### Error Response Handling
- **SLVERR**: Slave detected an error condition
- **DECERR**: No slave at target address (Interconnect generates)
- Errors don't terminate burst early
- Write response covers entire burst
- Read can have different response per beat

#### Key Timing Parameters
- No maximum wait states defined
- Interconnect can register and pipeline stages
- Default slave should respond to prevent deadlock
- Exclusive access has no timeout requirement