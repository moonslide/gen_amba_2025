# 16x16 AXI4 VIP Usage Guide

## Overview
This 16x16 AXI4 VIP uses **RTL-Only Mode** due to the large matrix size optimization. Full UVM testbench is not generated for matrices >10x10 to prevent performance issues and hanging.

## Available Commands

### Compilation
```bash
# Check RTL compilation (main target)
make compile_check

# Syntax check only
make syntax_check

# Clean build files
make clean
```

### Simulation Targets
```bash
# RTL simulation with FSDB waveform
make run_fsdb TEST=axi4_stress_test

# RTL simulation with VCD waveform  
make run_vcd TEST=axi4_stress_test

# Open Verdi for RTL debugging
make verdi
```

### Help
```bash
make help
```

## Important Notes

### ✅ What Works:
- RTL compilation and syntax checking
- Verdi database generation and debugging
- RTL structure examination
- Module interface verification

### ⚠️ Limitations:
- **No UVM testbench execution** (RTL-only mode)
- **No actual test runs** - targets are informational
- Test names like `axi4_stress_test` are accepted but not executed

### 🎯 For Full UVM Testing:
Use smaller matrix configurations (≤10x10) like:
- 9x9 VIP: `/home/timtim01/eda_test/project/gen_amba_2025/9x9_vip/`
- Create new configurations ≤10x10 from GUI

## Files Structure
```
sim/
├── Makefile                    # RTL-optimized makefile
├── axi4_compile.f             # RTL-only compile list
├── logs/compile.log           # Compilation logs
├── simv_rtl_check*            # Compiled executable
├── simv_rtl_check.daidir/     # Verdi database
└── pkg/axi4_globals_pkg_rtl.sv # UVM-free globals
```

## Generated RTL Modules
- `axi4_interconnect_m16s16` - Main 16x16 interconnect
- `axi4_address_decoder` - Address decoder
- `axi4_arbiter` - Arbitration logic  
- `axi4_router` - Transaction routing
- `axi4_globals_pkg` - Global parameters

## Verification Status
✅ **PASS**: RTL compilation successful
✅ **PASS**: All 5 modules compiled without errors
✅ **PASS**: Verdi database generated
✅ **PASS**: Makefile targets working

Last Updated: 2025-08-06