# tim_axi4_vip Integration

## Overview

The gen_amba_2025 tool now fully integrates tim_axi4_vip (https://github.com/moonslide/tim_axi4_vip) as the default AXI4 verification IP. This replaces the previous non-functional VIP with a proven, comprehensive solution.

## What is tim_axi4_vip?

tim_axi4_vip is a complete UVM-based AXI4 verification IP that includes:
- Full AXI4 protocol support
- Master and slave agents
- Bus Functional Models (BFMs)
- Protocol checkers and assertions
- Coverage collection
- Memory model for standalone testing
- Extensive test library (100+ tests)
- Scoreboard and monitors

## Integration Details

### 1. Repository Structure
```
gen_amba_2025/
├── external/
│   └── tim_axi4_vip/        # Cloned repository
└── generated_environments/
    └── tim_axi4_vip/        # Symbolic link in each environment
```

### 2. Key Components Integrated

#### BFM Modules
- `axi4_master_agent_bfm.sv` - Master bus functional model
- `axi4_slave_agent_bfm.sv` - Slave bus functional model
- `axi4_master_driver_bfm.sv` - Master driver BFM
- `axi4_slave_driver_bfm.sv` - Slave driver BFM
- `axi4_master_monitor_bfm.sv` - Master monitor BFM
- `axi4_slave_monitor_bfm.sv` - Slave monitor BFM

#### Package Hierarchy
1. `axi4_globals_pkg` - Global definitions
2. `axi4_master_pkg` - Master agent components
3. `axi4_slave_pkg` - Slave agent components
4. `axi4_master_seq_pkg` - Master sequences
5. `axi4_slave_seq_pkg` - Slave sequences
6. `axi4_env_pkg` - Environment components
7. `axi4_test_pkg` - Test definitions

#### Key Classes
- `axi4_master_agent` - Complete master agent
- `axi4_slave_agent` - Complete slave agent
- `axi4_env` - Verification environment
- `axi4_base_test` - Base test class
- `axi4_virtual_sequencer` - Virtual sequencer

### 3. Testbench Architecture

```systemverilog
top_tb
├── axi4_if (interface)
├── master_bfm (BFM instance)
├── slave_bfm (BFM instance)
├── dut_wrapper (Your DUT)
└── UVM environment
    ├── Master agents
    ├── Slave agents
    ├── Virtual sequencer
    ├── Scoreboard
    └── Coverage
```

### 4. Configuration

The testbench configures tim_axi4_vip through UVM config DB:

```systemverilog
// Number of agents
uvm_config_db#(int)::set(null, "*", "no_of_masters", 1);
uvm_config_db#(int)::set(null, "*", "no_of_slaves", 1);

// Interface registration
uvm_config_db#(virtual axi4_if)::set(null, "*", "vif", dut_if);

// BFM registration
uvm_config_db#(axi4_master_agent_bfm)::set(null, "*master_agent*", "master_agent_bfm", master_bfm);
uvm_config_db#(axi4_slave_agent_bfm)::set(null, "*slave_agent*", "slave_agent_bfm", slave_bfm);

// Memory model for standalone
uvm_config_db#(bit)::set(null, "*slave*", "slave_memory_mode_enable", 1'b1);
```

## Available Tests

### Basic Tests
- `axi4_write_test` - Basic write operations
- `axi4_read_test` - Basic read operations
- `axi4_write_read_test` - Combined write/read

### Blocking Transfer Tests
- `axi4_blocking_write_read_test`
- `axi4_blocking_16b_write_read_test`
- `axi4_blocking_32b_write_read_test`
- `axi4_blocking_64b_write_read_test`

### Advanced Tests
- `axi4_non_blocking_write_read_test`
- `axi4_4k_boundary_cross_test`
- `axi4_outstanding_transfer_test`
- `axi4_protocol_violation_tests`

### Stress Tests
- Over 100 additional tests covering all AXI4 features

## Running Tests

### Compile
```bash
cd scripts
./compile.sh
```

### Run Specific Test
```bash
./run_test.sh axi4_write_read_test
```

### Run with Waveforms
```bash
./run_test.sh axi4_write_read_test +waves
```

## Customization

### Adding Custom Tests

1. Create test extending `axi4_base_test`:
```systemverilog
class my_custom_test extends axi4_base_test;
    `uvm_component_utils(my_custom_test)
    
    function new(string name = "my_custom_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        // Your test logic
    endtask
endclass
```

2. Add to filelist.f
3. Run with test name

### Using Virtual Sequences

tim_axi4_vip provides virtual sequences for coordinated testing:

```systemverilog
axi4_virtual_write_read_seq virtual_seq;
virtual_seq = axi4_virtual_write_read_seq::type_id::create("virtual_seq");
virtual_seq.start(env.virtual_seqr);
```

## Advantages

1. **Proven Solution** - Used in real projects
2. **Complete Coverage** - All AXI4 features supported
3. **Extensive Tests** - 100+ pre-built tests
4. **Full UVM** - Modern verification methodology
5. **BFM Architecture** - Efficient simulation
6. **Built-in Checks** - Protocol assertions included

## Troubleshooting

### Common Issues

1. **Compilation Errors**
   - Ensure UVM is properly set up
   - Check simulator environment variables
   - Verify all files in filelist.f exist

2. **BFM Connection Issues**
   - BFMs must be instantiated in testbench
   - Check config DB paths match

3. **Memory Model Issues**
   - Enable with `slave_memory_mode_enable`
   - Check address ranges are valid

## Migration from Old VIP

If you have existing tests:
1. Replace old VIP imports with tim_axi4_vip packages
2. Update test base class to `axi4_base_test`
3. Use tim_axi4_vip sequences
4. Update configuration parameters

## Resources

- GitHub: https://github.com/moonslide/tim_axi4_vip
- Documentation: See `external/tim_axi4_vip/doc/`
- Examples: See `external/tim_axi4_vip/test/`