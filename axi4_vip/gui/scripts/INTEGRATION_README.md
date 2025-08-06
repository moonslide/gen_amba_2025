# VIP Detailed Logging Integration

## Overview
The VIP GUI now automatically applies detailed UVM_INFO logging patches after generating any VIP environment.

## What's Added
1. **Automatic Patch Application**: After VIP generation, the GUI automatically runs `apply_detailed_logging.sh`
2. **Enhanced Logging**: All BFMs, monitors, drivers, and scoreboards include detailed UVM_INFO messages
3. **Configurable Verbosity**: Makefiles support `UVM_VERBOSITY` parameter

## Features
- BFM initialization messages
- Transaction generation logging  
- Monitor transaction counting
- Driver transaction details
- Scoreboard throughput analysis
- Environment build/connect phase logging

## Usage
1. Generate VIP normally through GUI
2. Patches are automatically applied
3. Run tests with desired verbosity:
   ```bash
   make run_fsdb TEST=axi4_stress_test UVM_VERBOSITY=UVM_HIGH
   ```

## Manual Application
If needed, patches can be manually applied:
```bash
./apply_detailed_logging.sh /path/to/vip/axi4_vip_env_rtl_integration
```

## Verification
After generation, check for:
- BFM messages: "Master BFM signals initialized"
- Transaction messages: "Starting AXI transaction generation"
- Monitor messages: "Collected X transactions"
- Throughput reports: "Throughput Analysis"
