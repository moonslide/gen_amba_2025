# Verdi Integration Guide for AXI4 VIP

## Overview

The AXI4 VIP generation flow now includes enhanced Verdi integration features:
1. **-lca -kdb flags** added to VCS compilation for better debugging
2. **make verdi** command that automatically loads the last run's FSDB and elaboration database

## Features Added

### 1. VCS Compilation Enhancements

The Makefile now includes:
```makefile
VCS_COMP_OPTS = -full64 -sverilog -ntb_opts uvm-1.2 -timescale=1ns/1ps
VCS_COMP_OPTS += -debug_access+all +vcs+lic+wait -lca -kdb
```

- **-lca**: Enables Low-Cost Assertions for better performance
- **-kdb**: Generates Knowledge Database for Verdi debugging

### 2. Enhanced make verdi Target

The new `make verdi` target automatically:
- Finds the most recent FSDB file in the waves directory
- Loads the FSDB file in Verdi
- Loads the KDB elaboration database
- Provides error messages if no FSDB files exist

```makefile
# Open waveform in Verdi with auto-load last run
verdi:
	@echo "Auto-loading last run in Verdi..."
	@# Find the most recent FSDB file
	@LAST_FSDB=$$(ls -t $(WAVE_DIR)/*.fsdb 2>/dev/null | head -1); \
	if [ -z "$$LAST_FSDB" ]; then \
		echo "No FSDB files found. Run 'make run_fsdb' first."; \
		exit 1; \
	fi; \
	echo "Loading FSDB: $$LAST_FSDB"; \
	echo "Loading KDB: ./simv.daidir/kdb"; \
	verdi -ssf $$LAST_FSDB -dbdir ./simv.daidir/kdb -nologo &
```

## Usage

### Step 1: Run Simulation with FSDB Dumping

```bash
cd <vip_output_dir>/sim
make run_fsdb TEST=axi4_basic_rw_test
```

This will:
- Compile with -lca -kdb flags
- Run the test with FSDB dumping enabled
- Generate FSDB file in `waves/` directory
- Create KDB database in `simv.daidir/kdb/`

### Step 2: Open in Verdi

```bash
make verdi
```

This will:
- Automatically find the latest FSDB file
- Launch Verdi with the FSDB loaded
- Load the KDB elaboration database
- Open without the logo splash screen

## Additional Verdi Features

### 1. Signal Grouping File
Located at: `sim/scripts/axi4_signals.rc`

Pre-configured signal groups:
- Clock_Reset: Clock and reset signals
- M0_AW: Master 0 write address channel
- M0_W: Master 0 write data channel
- M0_B: Master 0 write response channel
- M0_AR: Master 0 read address channel
- M0_R: Master 0 read data channel
- UVM_Test_Info: UVM test hierarchy

### 2. Verdi Session File
Located at: `sim/scripts/axi4_session.ses`

Provides default window layout and signal loading.

### 3. Auto-Load Script
Located at: `sim/scripts/verdi_auto_load.tcl`

TCL script that can be sourced in Verdi to automatically set up the environment.

### 4. Verdi Configuration
Located at: `sim/.verdirc`

Sets up Verdi environment variables for optimal performance.

## Workflow Example

```bash
# 1. Generate VIP environment (from GUI or command line)
cd axi4_vip/gui
python src/vip_gui_app.py

# 2. Navigate to simulation directory
cd <output_dir>/axi4_vip_env_rtl_integration/sim

# 3. Run test with FSDB dumping
make run_fsdb TEST=axi4_burst_test SEED=12345

# 4. Open in Verdi (automatically loads last run)
make verdi

# 5. In Verdi, you can:
#    - View pre-grouped signals
#    - Navigate source with KDB
#    - Debug UVM components
#    - Analyze transactions
```

## Troubleshooting

### No FSDB Files Found
If you see "No FSDB files found", ensure you:
1. Run simulation with FSDB dumping: `make run_fsdb`
2. Check that simulation completed successfully
3. Verify FSDB files exist in `waves/` directory

### KDB Not Loading
If KDB doesn't load:
1. Ensure compilation used `-kdb` flag
2. Check that `simv.daidir/kdb` directory exists
3. Verify Verdi version supports KDB

### Signal Groups Not Loading
If signal groups don't appear:
1. Check that `scripts/axi4_signals.rc` exists
2. Load manually: File → Load Signal File in Verdi
3. Verify signal paths match your design hierarchy

## Benefits

1. **Faster Debug Cycles**: No need to manually locate and load files
2. **Consistent Environment**: Same setup every time
3. **Better Performance**: -lca flag optimizes assertion checking
4. **Enhanced Navigation**: KDB enables source code browsing
5. **Organized Signals**: Pre-configured signal groups save time

## Future Enhancements

Potential improvements:
- Add transaction-level debugging setup
- Create test-specific signal groupings
- Add coverage viewing integration
- Support for multiple FSDB comparison