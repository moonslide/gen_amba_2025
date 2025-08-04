# FSDB Waveform Dumping Guide

This VIP supports FSDB waveform dumping for debugging with Verdi.

## Quick Start

### 1. Run simulation with FSDB dumping:
```bash
make run_fsdb TEST=axi4_basic_rw_test
```

### 2. View waveform in Verdi:
```bash
make verdi
```

## Manual Control

### Enable FSDB dumping:
```bash
make run DUMP_FSDB=1
```

### Specify custom FSDB file:
```bash
make run DUMP_FSDB=1 FSDB_FILE=my_waves.fsdb
```

### Runtime control with plusargs:
```bash
./simv +fsdb_file=custom.fsdb +enable_wave
```

## Test Control

Tests can control waveform dumping:
- `+enable_wave` - Enable dumping at start
- `+disable_wave` - Disable dumping at start

## VCD Alternative

For environments without Verdi:
```bash
make run_vcd TEST=axi4_basic_rw_test
make dve  # View in DVE
```

## Compilation Requirements

1. Set VERDI_HOME environment variable:
```bash
export VERDI_HOME=/path/to/verdi/installation
```

2. Ensure Verdi PLI libraries are accessible

## Waveform Files

Generated waveforms are stored in:
- FSDB: `sim/waves/<TEST>_<SEED>.fsdb`
- VCD: `sim/waves/<TEST>_<SEED>.vcd`

## Selective Dumping

To reduce file size, you can:
1. Use `hdl_top.enable_wave_dump()` and `hdl_top.disable_wave_dump()` in tests
2. Modify the `$fsdbDumpvars` scope in hdl_top.sv
3. Use Verdi commands for selective dumping

## Troubleshooting

### FSDB not generated:
- Check VERDI_HOME is set correctly
- Verify +define+DUMP_FSDB is passed during compilation
- Check for PLI loading errors in simulation log

### Verdi won't open:
- Ensure Verdi is in PATH
- Check FSDB file exists in waves directory
- Verify FSDB file is not corrupted
