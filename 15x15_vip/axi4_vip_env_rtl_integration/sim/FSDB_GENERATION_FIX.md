# FSDB Generation Fix for 15x15 VIP Environment

## Problem
The command `make run_fsdb TEST=axi4_basic_rw_test` was not generating FSDB waveform files in the waves/ directory.

## Root Cause
1. Missing FSDB dumping code in the testbench
2. Incorrect Makefile configuration for FSDB support
3. Missing waves directory setup

## Fixes Applied

### 1. Updated hvl_top.sv
Added FSDB dumping system tasks controlled by the DUMP_FSDB define:
```systemverilog
`ifdef DUMP_FSDB
    // FSDB dumping using system tasks
    $fsdbDumpfile("waves/axi4_vip.fsdb");
    $fsdbDumpvars(0, hdl_top, "+all");
    $fsdbDumpvars(0, hvl_top, "+all");
    $display("[%0t] FSDB dumping enabled to waves/axi4_vip.fsdb", $time);
`endif
```

### 2. Updated Makefile
Enhanced FSDB support with proper compilation flags:
```makefile
# Waveform dump options
DUMP_FSDB ?= 0
FSDB_FILE ?= $(WAVE_DIR)/axi4_vip.fsdb

# Add waveform defines
ifeq ($(DUMP_FSDB), 1)
    COMMON_OPTS += +define+DUMP_FSDB
    VERDI_HOME ?= /home/eda_tools/synopsys/verdi/W-2024.09-SP1
    VCS_COMP_OPTS += -P $(VERDI_HOME)/share/PLI/VCS/LINUX64/novas.tab $(VERDI_HOME)/share/PLI/VCS/LINUX64/pli.a
    # Add debug access for FSDB dumping
    VCS_COMP_OPTS += -debug_access+all -debug_region+cell+encrypt -debug_pp
endif
```

### 3. Created waves/dump_fsdb.tcl
Added TCL script for advanced FSDB configuration (optional, for future use).

## Verification
After applying the fixes:
1. Compilation succeeds with DUMP_FSDB=1
2. FSDB file is generated: `waves/axi4_vip.fsdb` (24KB)
3. File can be opened with Verdi for waveform viewing

## Usage
```bash
# Generate FSDB waveforms
make run_fsdb TEST=axi4_basic_rw_test

# The FSDB file will be created at:
# waves/axi4_vip.fsdb

# View with Verdi
verdi -ssf waves/axi4_vip.fsdb &
```

## Additional Features
The fix also adds support for VCD dumping:
```bash
# Generate VCD waveforms (alternative to FSDB)
make run_vcd TEST=axi4_basic_rw_test

# View with GTKWave or other VCD viewers
gtkwave waves/axi4_vip.vcd &
```

## Notes
- FSDB files are more compact and efficient than VCD
- The dump includes all signals from hdl_top and hvl_top modules
- Debug access is enabled for full signal visibility
- The same approach can be applied to other VIP environments