# AXI4 VIP Waveform Dumping Guide

## Overview
This guide explains how to generate and view waveforms from AXI4 VIP simulations.

## Quick Start

### Method 1: Using the Helper Script (Easiest)
```bash
cd sim
./run_with_waves.sh [test_name] [seed] [dump_type]

# Examples:
./run_with_waves.sh                              # Default: axi4_base_test, seed=1, fsdb
./run_with_waves.sh axi4_burst_test              # Specific test, seed=1, fsdb
./run_with_waves.sh axi4_burst_test 123 vcd      # Specific test, seed, and VCD format
```

### Method 2: Using Make Targets
```bash
# For FSDB format (Verdi)
make run_fsdb TEST=axi4_burst_test SEED=1

# For VCD format (GTKWave/DVE)
make run_vcd TEST=axi4_burst_test SEED=1
```

### Method 3: Manual Compilation with Defines
```bash
# Compile with FSDB support
make compile DUMP_FSDB=1

# Run simulation
./simv +UVM_TESTNAME=axi4_burst_test +fsdb_file=waves/my_test.fsdb
```

## Viewing Waveforms

### FSDB Files (Verdi)
```bash
# Auto-load most recent FSDB
make verdi

# Or manually specify file
verdi -ssf waves/axi4_burst_test_1.fsdb -dbdir ./simv.daidir/kdb &
```

### VCD Files
```bash
# Using DVE
dve -vpd waves/axi4_burst_test_1.vcd &

# Using GTKWave (open source)
gtkwave waves/axi4_burst_test_1.vcd &
```

## What Gets Dumped?

The waveform dump includes:
- All signals in `hdl_top` module
- All signals in `dut` (dut_wrapper) module
- All internal DUT signals (interconnect, arbiters, etc.)
- SystemVerilog assertions (FSDB only)
- Multi-dimensional arrays (FSDB only)
- UVM transactions and sequences (visible in Verdi)

## Performance Considerations

### Selective Dumping
To reduce file size and improve performance:

1. **Time-based control** - Use tasks in your test:
```systemverilog
// In your test
initial begin
    hdl_top.disable_wave_dump();  // Start with dumping off
    #1000ns;
    hdl_top.enable_wave_dump();   // Enable for specific window
    #5000ns;
    hdl_top.disable_wave_dump();  // Disable when done
end
```

2. **Scope-based control** - Modify hdl_top.sv:
```systemverilog
// Dump only specific modules
$fsdbDumpvars(0, dut.generated_interconnect);
```

## Troubleshooting

### FSDB not generated
1. Check if Verdi is available: `which verdi`
2. Verify VERDI_HOME in Makefile points to correct installation
3. Check simulation log for FSDB-related errors

### VCD file is too large
1. Use FSDB format instead (much better compression)
2. Enable dumping only for specific time windows
3. Dump only specific hierarchy levels

### Signals show as 'X' or 'Z'
1. Check reset sequence completes properly
2. Verify clock is running
3. Check DUT connections in hdl_top.sv

## File Locations
- Waveform files: `sim/waves/`
- Simulation logs: `sim/logs/`
- Compile logs: `sim/logs/compile.log`

## Tips
1. FSDB format is preferred for large designs (better compression)
2. Use meaningful test names and seeds for easy identification
3. Clean old waveforms regularly: `rm -rf waves/*`
4. For debugging specific issues, use time-based selective dumping