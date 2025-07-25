# VIP Generation Following tim_axi4_vip Structure

## Overview

The VIP environment generator now creates a complete UVM-based verification environment that follows the exact structure of the tim_axi4_vip repository. This ensures compatibility, maintainability, and adherence to industry best practices.

## Generated Directory Structure

When you generate a VIP environment, the following directory structure is created:

```
axi4_vip_env_<mode>/
├── agent/                  # BFM agents (Bus Functional Models)
│   ├── master_agent_bfm/   # Master agent BFM interfaces
│   └── slave_agent_bfm/    # Slave agent BFM interfaces
├── assertions/             # Protocol assertions
├── bm/                     # Bus matrix components
├── doc/                    # Documentation
├── env/                    # Environment level components
├── include/                # Common includes and defines
├── intf/                   # Interface definitions
│   └── axi4_interface/     # AXI4 interface
├── master/                 # Master agent components
├── pkg/                    # Package definitions
├── seq/                    # Sequences (test patterns)
│   ├── master_sequences/   # Master-specific sequences
│   └── slave_sequences/    # Slave-specific sequences
├── sim/                    # Simulation infrastructure
│   ├── scripts/            # Simulation scripts
│   ├── results/            # Test results
│   ├── logs/               # Simulation logs
│   ├── waves/              # Waveform files
│   └── coverage/           # Coverage reports
├── slave/                  # Slave agent components
├── test/                   # Test cases
├── testlists/              # Regression test lists
├── top/                    # Top-level modules
├── virtual_seq/            # Virtual sequences
├── virtual_seqr/           # Virtual sequencer
└── rtl_wrapper/            # RTL wrapper (RTL integration mode only)
    └── generated_rtl/      # Tool-generated RTL files
```

## Key Generated Files

### 1. Package Files (`pkg/`)

#### `axi4_globals_pkg.sv`
- Global parameters from GUI configuration
- Number of masters/slaves
- Data/address widths
- Type definitions (burst, response, etc.)
- Master/slave configurations

### 2. Interface Files (`intf/`)

#### `axi4_if.sv`
- Complete AXI4 interface definition
- All AXI4 channels (AW, W, B, AR, R)
- Master, slave, and monitor modports
- Parameterized widths

### 3. Agent BFMs (`agent/`)

#### Master/Slave Agent BFMs
- Interface wrappers for UVM agents
- Driver and monitor BFM instances
- Connection points for UVM components

### 4. Sequence Files (`seq/`)

#### Base Sequences
- `axi4_master_base_seq.sv` - Base class for master sequences
- `axi4_master_write_seq.sv` - Basic write sequence
- `axi4_master_read_seq.sv` - Basic read sequence

### 5. Environment Files (`env/`)

#### `axi4_env_config.sv`
- Environment configuration class
- Agent configuration instances
- Coverage and scoreboard enables

#### `axi4_env.sv`
- Top-level environment class
- Agent instantiation
- Virtual sequencer
- Scoreboard and coverage components

### 6. Test Files (`test/`)

#### `axi4_base_test.sv`
- Base test class
- Environment instantiation
- Configuration setup

#### `axi4_basic_rw_test.sv`
- Simple read/write test example
- Virtual sequence usage

### 7. Top-Level Files (`top/`)

#### `hdl_top.sv`
- Clock/reset generation
- Interface instantiation
- BFM instantiation
- DUT connection (RTL mode)

#### `hvl_top.sv`
- UVM test execution
- run_test() call

### 8. Simulation Files (`sim/`)

#### `Makefile`
- Multi-simulator support (VCS, Questa, Xcelium, Vivado)
- Compile and run targets
- Random seed control
- Coverage collection

#### `axi4_compile.f`
- Compilation file list
- Include directories
- Package compilation order

## RTL Integration Mode Features

When generating in RTL Integration mode, additional features include:

### RTL Wrapper (`rtl_wrapper/`)

#### `dut_wrapper.sv`
- Connects VIP to generated/external RTL
- Multi-master/slave support
- Master 0 connected to VIP
- Other masters terminated properly
- All slaves with response logic

#### `rtl_files.f`
- Auto-populated with generated RTL files
- Or manually edited for external RTL

## Generated Configuration

The generator captures your GUI configuration:

### Masters
- Name, ID width
- QoS support
- Exclusive access support

### Slaves  
- Name, base address, size
- Memory type
- Access permissions
- Allowed masters

## Usage After Generation

### 1. Navigate to the generated environment:
```bash
cd axi4_vip_env_rtl_integration/sim
```

### 2. Run simulation:
```bash
make run TEST=axi4_base_test
```

### 3. Run with different simulator:
```bash
make run SIM=questa TEST=axi4_basic_rw_test
```

### 4. Run with random seed:
```bash
make run TEST=axi4_basic_rw_test SEED=12345
```

## Integration with tim_axi4_vip

The generated environment is designed to work seamlessly with tim_axi4_vip components. The structure matches exactly, allowing you to:

1. Use tim_axi4_vip sequences and tests
2. Leverage existing protocol checkers
3. Reuse coverage models
4. Maintain consistency with established VIP architecture

## Customization

After generation, you can:

1. Add custom sequences in `seq/`
2. Create new tests in `test/`
3. Extend agent configurations
4. Add protocol-specific checks
5. Implement custom scoreboards

## Best Practices

1. **Keep Configuration in GUI**: Use the GUI for all bus configuration changes
2. **Version Control**: Commit generated environment to track changes
3. **Extend, Don't Modify**: Create new classes that extend generated base classes
4. **Use Virtual Sequences**: Coordinate multi-agent scenarios
5. **Document Changes**: Update README in `doc/` with customizations