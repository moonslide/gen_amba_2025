# AXI4 VIP SystemVerilog/UVM Simulation Environment

A complete SystemVerilog/UVM-based AXI4 Verification IP (VIP) implementation supporting the full AXI4 protocol specification. This simulation environment provides comprehensive verification capabilities for AXI4-based designs.

## 🌟 Features

### Protocol Support
- **Complete AXI4 Protocol**: Full implementation of AMBA AXI4 specification (IHI0022D)
- **All 5 Channels**: AW, W, B, AR, R with proper handshaking
- **Burst Types**: FIXED, INCR, WRAP with full compliance
- **Advanced Features**: QoS, Region, User signals, Exclusive access
- **4KB Boundary Protection**: Automatic checking and constraint handling
- **Response Types**: OKAY, EXOKAY, SLVERR, DECERR support

### UVM Architecture
- **Master Agent**: Configurable active/passive master with driver, monitor, sequencer
- **Slave Agent**: Intelligent slave with memory model and configurable responses
- **Monitor**: Protocol compliance checking and functional coverage collection
- **Scoreboard**: Transaction comparison and data integrity verification
- **Sequences**: Comprehensive test sequence library

### Test Coverage
- **Basic Transactions**: Single read/write operations
- **Burst Testing**: Long bursts up to 256 beats
- **WRAP Bursts**: All valid WRAP configurations (2,4,8,16 beats)
- **Exclusive Access**: Exclusive read/write pairs with proper tracking
- **QoS Testing**: Quality of Service level verification
- **Security Testing**: All AxPROT combinations
- **Error Injection**: Protocol violations and error response testing
- **Stress Testing**: High-throughput randomized transactions

## 📁 Directory Structure

```
axi4_vip_sim/
├── src/
│   ├── interfaces/
│   │   └── axi4_if.sv              # AXI4 interface with clocking blocks
│   ├── sequences/
│   │   ├── axi4_transaction.sv     # UVM sequence item
│   │   └── axi4_sequences.sv       # Test sequence library
│   ├── agents/
│   │   ├── axi4_master_driver.sv   # Master driver implementation
│   │   ├── axi4_slave_driver.sv    # Slave driver with memory model
│   │   ├── axi4_monitor.sv         # Protocol monitor
│   │   └── axi4_master_agent.sv    # Agent wrapper classes
│   ├── testbench/
│   │   ├── axi4_scoreboard.sv      # Transaction scoreboard
│   │   ├── axi4_test_env.sv        # Test environment
│   │   └── axi4_tb_top.sv          # Top-level testbench
│   └── axi4_vip_pkg.sv            # Complete UVM package
├── scripts/
│   └── run_sim.sh                  # Automated simulation runner
├── Makefile                        # Build system
└── README.md
```

## 🚀 Quick Start

### Prerequisites
- SystemVerilog simulator (VCS, Questa, or Xcelium)
- UVM library (typically included with simulator)
- Make utility

### Basic Usage

1. **Compile and run basic test:**
```bash
make run TEST=axi4_basic_test
```

2. **Run comprehensive test suite:**
```bash
make run TEST=axi4_comprehensive_test
```

3. **Run with GUI configuration from Bus Matrix GUI:**
```bash
make run TEST=axi4_basic_test CONFIG_FILE=output/configs/axi4_config_20250724_143022.json
```

4. **Run with GUI (VCS):**
```bash
make gui TEST=axi4_basic_test
```

5. **Using the automated script:**
```bash
./scripts/run_sim.sh -t axi4_basic_test -g -c
```

### Simulator Selection
The default simulator is VCS. To use other simulators:
```bash
make run SIM=questa TEST=axi4_basic_test
make run SIM=xcelium TEST=axi4_basic_test
```

## 🧪 Available Tests

### `axi4_basic_test`
- **Purpose**: Basic functionality verification
- **Coverage**: Simple read/write transactions, short bursts
- **Duration**: ~50 transactions, fast execution
- **Use Case**: Smoke testing, quick verification

### `axi4_comprehensive_test`
- **Purpose**: Complete protocol verification
- **Coverage**: All burst types, QoS, security, exclusive access, error injection
- **Duration**: 8 test phases, ~500+ transactions
- **Use Case**: Full verification, regression testing

## 📊 Test Sequences

| Sequence | Description | Transactions | Features |
|----------|-------------|--------------|----------|
| `axi4_basic_sequence` | Simple transactions | 20-50 | Short bursts, basic patterns |
| `axi4_burst_sequence` | Long burst testing | 15-20 | 8-256 beat bursts |
| `axi4_wrap_sequence` | WRAP burst testing | 12 | All valid WRAP combinations |
| `axi4_exclusive_sequence` | Exclusive access | 8 pairs | Exclusive read/write pairs |
| `axi4_qos_sequence` | QoS verification | 16 | All priority levels |
| `axi4_security_sequence` | Security testing | 16 | All AxPROT combinations |
| `axi4_error_sequence` | Error injection | 6 | Protocol violations |
| `axi4_stress_sequence` | Stress testing | 200+ | High-throughput random |

## 🔧 Configuration

### Environment Variables
```bash
export VCS_HOME=/path/to/vcs          # For VCS
export QUESTA_HOME=/path/to/questa    # For Questa  
export XCELIUM_HOME=/path/to/xcelium  # For Xcelium
```

### Test Configuration
The `axi4_vip_config` class provides easy configuration:
```systemverilog
axi4_vip_config cfg = new();
cfg.addr_width = 32;
cfg.data_width = 64;
cfg.slave_base_addr = 64'h1000_0000;
cfg.slave_size = 64'h1000_0000;
cfg.slave_error_rate = 5; // 5% error injection
uvm_config_db#(axi4_vip_config)::set(null, "*", "cfg", cfg);
```

## 📈 Coverage and Analysis

### Functional Coverage
- **Burst Types**: FIXED, INCR, WRAP coverage
- **Transfer Sizes**: 1B to 128B coverage
- **QoS Levels**: All 16 priority levels
- **Protection Types**: All 8 AxPROT combinations
- **Response Types**: All 4 response codes
- **Cross Coverage**: Important parameter combinations

### Protocol Assertions
- **Handshake Stability**: VALID/READY signal stability
- **4KB Boundary**: Automatic violation detection
- **WRAP Constraints**: Valid length and alignment checking
- **Signal Stability**: Address/data stability during handshakes

### Performance Metrics
- **Latency Tracking**: Per-transaction timing analysis
- **Throughput Analysis**: Bandwidth utilization
- **Outstanding Transactions**: Concurrent transaction monitoring

## 🎯 Advanced Usage

### Custom Test Creation
```systemverilog
class my_custom_test extends axi4_base_test;
    `uvm_component_utils(my_custom_test)
    
    virtual task main_phase(uvm_phase phase);
        my_custom_sequence seq = my_custom_sequence::type_id::create("seq");
        phase.raise_objection(this);
        seq.start(m_env.m_master_agent.m_sequencer);
        phase.drop_objection(this);
    endtask
endclass
```

### Memory Initialization
```systemverilog
// Initialize slave memory with test patterns
m_env.m_slave_agent.write_memory(64'h1000_0000, 8'hAA);
m_env.m_slave_agent.write_memory(64'h1000_0001, 8'h55);
```

### Error Rate Configuration
```systemverilog
// Configure 10% error injection rate
m_env.m_slave_agent.set_error_rate(10);
m_env.m_slave_agent.set_latency_range(1, 20, 1, 15);
```

## 🐛 Debugging

### Waveform Dumping
```bash
make run TEST=axi4_basic_test +DUMP_VCD
make run TEST=axi4_basic_test +DUMP_FSDB
```

### Verbosity Control
```bash
make run TEST=axi4_basic_test UVM_VERBOSITY=UVM_HIGH
./scripts/run_sim.sh -t axi4_basic_test -v UVM_HIGH
```

### Debug Mode
```bash
make debug TEST=axi4_basic_test  # Opens GUI with debug access
```

## 📋 Makefile Targets

| Target | Description |
|--------|-------------|
| `help` | Show available targets and options |
| `compile` | Compile design and testbench |
| `run` | Run specified test |
| `gui` | Run with GUI interface |
| `regression` | Run all tests in regression mode |
| `clean` | Clean build artifacts |
| `coverage` | Generate coverage reports |
| `lint` | Run lint checking |
| `debug` | Start debug session |

## 🔍 Results Analysis

### Log Files
- **Compilation**: `logs/compile.log`
- **Test Results**: `logs/<testname>_<timestamp>.log`
- **Coverage**: `logs/coverage_report/`

### Success Indicators
```
*** TEST PASSED ***
✓ Test PASSED: axi4_basic_test
Protocol Coverage: 98.5%
Functional Coverage: 94.2%
```

### Failure Analysis
- Check for `UVM_ERROR` or `UVM_FATAL` messages
- Look for protocol violations in monitor reports
- Verify scoreboard transaction matching
- Review assertion failures

## 🤝 Integration with Bus Matrix GUI

This SystemVerilog/UVM simulation environment is designed to work with the Python-based Bus Matrix GUI:

### **Proper Workflow:**
1. **Configure in GUI**: Use the Bus Matrix GUI to design your system
   - Add masters and slaves visually
   - Configure address maps and priorities
   - Set up interconnect routing

2. **Export from GUI**: Use the VIP tab in GUI
   - Click "Export UVM Config"
   - This generates JSON configuration files in `../axi4_vip_sim/output/configs/`
   - Also creates test scripts and Makefile arguments

3. **Run UVM Simulation**: Use Makefile or scripts
   ```bash
   cd ../axi4_vip_sim
   make run TEST=axi4_basic_test CONFIG_FILE=output/configs/<exported_config>.json
   ```

4. **View Results**: Check the `output/` directory
   - Logs in `output/logs/`
   - Waveforms in `output/waves/`
   - Coverage in `output/coverage/`

### **Important Notes:**
- ⚠️  **GUI does NOT run SystemVerilog simulations directly**
- ✅  **GUI exports configurations for UVM to read**
- ✅  **UVM simulations run via Makefile with proper tools**
- ✅  **All outputs go to organized `output/` directory structure**

## 📚 Additional Resources

- **AXI4 Specification**: ARM IHI0022D AMBA AXI Protocol Specification
- **UVM Documentation**: IEEE 1800.2-2017 UVM Standard
- **SystemVerilog LRM**: IEEE 1800-2017 SystemVerilog Standard

## 🎉 Project Status

✅ **Complete SystemVerilog/UVM AXI4 VIP implementation**
- Full protocol support with all AXI4 features
- Comprehensive test suite with 8+ sequence types
- Professional UVM architecture with proper layering
- Multi-simulator support (VCS, Questa, Xcelium)
- Automated build and test infrastructure
- Extensive documentation and examples

This AXI4 VIP simulation environment provides enterprise-grade verification capabilities for AXI4-based designs, supporting both academic learning and production verification workflows.