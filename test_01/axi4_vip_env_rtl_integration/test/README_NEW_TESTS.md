# AXI4 VIP Comprehensive Test Suite

This document describes the new comprehensive test cases added to the AXI4 VIP environment to enhance verification coverage and ensure robust testing of all AXI4 protocol features.

## Overview

The new test suite includes 7 comprehensive test cases that cover advanced AXI4 protocol scenarios, performance testing, error injection, and data integrity validation. These tests are designed to work with the updated VIP generation flow and provide extensive coverage of AXI4 specification requirements per IHI0022D.

## New Test Cases

### 1. AXI4 Comprehensive Burst Test (`axi4_comprehensive_burst_test.sv`)

**Purpose**: Extensive testing of all AXI4 burst types with various lengths and sizes.

**Key Features**:
- Tests FIXED, INCR, and WRAP burst types
- Validates burst lengths from 1 to 256 transfers (AXI4 limit)
- Tests all valid burst sizes (1 to 128 bytes)
- WRAP burst validation with proper alignment
- Concurrent burst operations from multiple masters
- Validates burst address calculations and boundary handling

**Test Scenarios**:
- FIXED bursts with different lengths and sizes
- INCR bursts up to 256 transfers (AXI4 enhancement)
- WRAP bursts with valid lengths (2, 4, 8, 16) and proper alignment
- Concurrent burst testing across multiple masters

### 2. AXI4 4KB Boundary Test (`axi4_4kb_boundary_test.sv`)

**Purpose**: Critical validation of the AXI4 requirement that no transaction can cross a 4KB address boundary.

**Key Features**:
- Tests transactions at 4KB boundaries
- Validates address calculation for all burst types
- Tests unaligned transfers near boundaries
- Maximum size transfers at boundaries
- Boundary crossing detection and prevention

**Test Scenarios**:
- Single transfers at 4KB boundaries
- INCR bursts approaching but not crossing boundaries
- WRAP bursts within 4KB pages
- FIXED bursts at boundaries (address doesn't change)
- Unaligned transfers near boundaries
- Maximum size transfers (32 × 128 = 4096 bytes exactly)

### 3. AXI4 Exclusive Access Test (`axi4_exclusive_access_test.sv`)

**Purpose**: Comprehensive testing of atomic operations and exclusive access mechanisms.

**Key Features**:
- Exclusive read/write pairs with EXOKAY responses
- Exclusive access failure scenarios (intervening writes)
- Multi-master exclusive contention
- Size and alignment validation for exclusive transfers
- Different AXI ID handling for exclusive access

**Test Scenarios**:
- Basic exclusive read-write pairs (expect EXOKAY)
- Exclusive access failures due to intervening writes (expect OKAY)
- Multi-master exclusive access contention
- Different AXI IDs from same master
- Exclusive access size validation (1-128 bytes, power of 2)

### 4. AXI4 Protocol Compliance Test (`axi4_protocol_compliance_test.sv`)

**Purpose**: Comprehensive validation of AXI4 protocol compliance per IHI0022D specification.

**Key Features**:
- Channel handshake compliance testing
- VALID/READY signal timing validation
- Address, data, and response channel compliance
- Write strobe (WSTRB) compliance testing
- AXI ID consistency and ordering rules
- AXI4-specific signals (AxCACHE, AxPROT, AxQOS, AxREGION)

**Test Scenarios**:
- VALID before/after READY handshake patterns
- VALID signal stability requirements
- Address channel compliance for all burst types
- Data ordering and WLAST signal validation
- Write interleaving prevention (AXI4 requirement)
- Response ordering for same ID transactions
- WSTRB patterns for different data widths
- AXI4 signal value testing

### 5. AXI4 Advanced Error Test (`axi4_advanced_error_test.sv`)

**Purpose**: Comprehensive error injection and recovery testing.

**Key Features**:
- SLVERR and DECERR response injection
- Protocol violation detection
- Timeout and deadlock scenarios
- Error recovery mechanisms
- Burst-specific error scenarios
- Multi-master error isolation

**Test Scenarios**:
- SLVERR injection for protected/reserved addresses
- DECERR injection for unmapped addresses
- Protocol violations (invalid burst types, 4KB crossing)
- Address, data, and response channel timeouts
- Error recovery after SLVERR/DECERR
- Error injection at different burst beats
- Multi-master error isolation testing

### 6. AXI4 Multi-Master Contention Test (`axi4_multi_master_contention_test.sv`)

**Purpose**: Testing arbitration, QoS handling, and high-contention scenarios.

**Key Features**:
- Multi-master access to same slave
- QoS-based arbitration testing
- Priority level arbitration
- Bandwidth sharing and fairness
- Hot slave contention scenarios
- Maximum throughput stress testing

**Test Scenarios**:
- 8 masters accessing same slave simultaneously
- QoS priority arbitration (0-15 levels)
- Priority-based scheduling with preemption
- Fair bandwidth sharing algorithms
- Hot slave scenarios with backoff strategies
- Distributed load across all slaves
- Burst interference testing
- Maximum throughput stress (100 transactions per master)

### 7. AXI4 Data Integrity Test (`axi4_data_integrity_test.sv`)

**Purpose**: End-to-end data integrity validation including unaligned transfers and WSTRB patterns.

**Key Features**:
- Write-read data integrity verification
- Unaligned transfer testing
- WSTRB pattern validation
- Data width variations (1-128 bytes)
- Burst data consistency
- Multi-master data coherency

**Test Scenarios**:
- Various data patterns (all 0s, all 1s, alternating, sequential)
- Unaligned addresses with different transfer sizes
- All possible WSTRB patterns for partial writes
- Different data widths (8, 16, 32, 64, 128, 256, 512, 1024 bits)
- Burst data patterns and continuity
- Overlapping address scenarios
- Walking 1s/0s patterns
- Multi-master shared memory coherency

## Usage Instructions

### Running Individual Tests

```bash
# Run comprehensive burst test
./simv +UVM_TESTNAME=axi4_comprehensive_burst_test +UVM_VERBOSITY=UVM_MEDIUM

# Run 4KB boundary test
./simv +UVM_TESTNAME=axi4_4kb_boundary_test +UVM_VERBOSITY=UVM_MEDIUM

# Run exclusive access test
./simv +UVM_TESTNAME=axi4_exclusive_access_test +UVM_VERBOSITY=UVM_HIGH

# Run protocol compliance test
./simv +UVM_TESTNAME=axi4_protocol_compliance_test +UVM_VERBOSITY=UVM_MEDIUM

# Run advanced error test
./simv +UVM_TESTNAME=axi4_advanced_error_test +UVM_VERBOSITY=UVM_LOW

# Run multi-master contention test
./simv +UVM_TESTNAME=axi4_multi_master_contention_test +UVM_VERBOSITY=UVM_MEDIUM

# Run data integrity test
./simv +UVM_TESTNAME=axi4_data_integrity_test +UVM_VERBOSITY=UVM_MEDIUM
```

### Test Configuration Options

Most tests support additional plusargs for customization:

```bash
# Enable waveform dumping
+enable_wave

# Set specific random seed
+ntb_random_seed=12345

# Enable protocol checking
+enable_protocol_checks

# Set error injection rate
+error_rate=10

# Enable performance monitoring
+enable_perf_mon
```

### Expected Runtime

| Test Case | Approximate Runtime | Transaction Count |
|-----------|-------------------|------------------|
| Comprehensive Burst | ~2-3 minutes | ~500 transactions |
| 4KB Boundary | ~1-2 minutes | ~200 transactions |
| Exclusive Access | ~1-2 minutes | ~150 transactions |
| Protocol Compliance | ~3-4 minutes | ~400 transactions |
| Advanced Error | ~2-3 minutes | ~300 transactions |
| Multi-Master Contention | ~4-5 minutes | ~1600 transactions |
| Data Integrity | ~3-4 minutes | ~800 transactions |

## Coverage Goals

The new test suite aims to achieve:

- **Functional Coverage**: >95% of AXI4 protocol features
- **Code Coverage**: >90% of RTL code paths
- **Assertion Coverage**: 100% of protocol assertions
- **Error Coverage**: All error response types and recovery paths
- **Performance Coverage**: Stress testing under maximum load

## Integration with VIP Generator

These tests are designed to work seamlessly with the updated VIP generator that fixes the interface array issues. The tests leverage:

- All 8 masters in concurrent scenarios
- Proper interface array connections
- Enhanced virtual sequences for multi-master coordination
- Improved error injection and monitoring capabilities

## Regression Testing

For regression testing, run all tests in sequence:

```bash
# Create test list
echo "axi4_comprehensive_burst_test" > regression.list
echo "axi4_4kb_boundary_test" >> regression.list  
echo "axi4_exclusive_access_test" >> regression.list
echo "axi4_protocol_compliance_test" >> regression.list
echo "axi4_advanced_error_test" >> regression.list
echo "axi4_multi_master_contention_test" >> regression.list
echo "axi4_data_integrity_test" >> regression.list

# Run regression
for test in $(cat regression.list); do
    echo "Running $test..."
    ./simv +UVM_TESTNAME=$test +UVM_VERBOSITY=UVM_LOW -l logs/${test}.log
done
```

## Debugging and Analysis

### Waveform Analysis
- Use `+enable_wave` to capture waveforms
- Focus on channel handshakes during protocol violations
- Monitor arbitration signals during contention tests
- Check data integrity during burst operations

### Log Analysis
- Search for "ERROR" or "FATAL" messages
- Monitor UVM_INFO messages for test progress
- Check for assertion failures in protocol compliance
- Verify transaction completion counts

### Performance Analysis
- Monitor transaction throughput in contention tests
- Check latency measurements in performance tests
- Analyze bandwidth utilization across masters
- Verify QoS arbitration effectiveness

## Known Limitations

1. **Simulation Performance**: Large burst tests may take significant simulation time
2. **Memory Requirements**: Data integrity tests require substantial memory models
3. **Platform Dependencies**: Some timing-sensitive tests may vary on different simulators
4. **Coverage Dependencies**: Full coverage requires specific RTL implementation features

## Future Enhancements

Potential areas for expansion:
- AXI4-Stream protocol testing
- AXI4-Lite specific scenarios  
- Power management interface testing
- Cross-clock domain scenarios
- Advanced coherency protocols
- SystemVerilog assertions integration

## Contact and Support

For questions about these test cases or issues with the VIP generation flow, refer to the main project documentation or contact the verification team.