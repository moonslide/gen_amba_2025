# Enhanced VIP Generation with Comprehensive Logging

This enhanced version of the VIP generator includes comprehensive debugging features to help trace VIP activity in waveforms and logs.

## Features Added

### 1. BFM Integration
- Full Bus Functional Model implementation
- Task-based transaction APIs
- Timeout detection on all handshakes
- Protocol-compliant signal generation

### 2. Enhanced Logging
- Transaction-level UVM_INFO messages
- Driver transaction counters
- Monitor channel activity tracking
- BFM operation timestamps
- Interface signal debugging

### 3. Protocol Checking
- Valid signal stability assertions
- Ready signal monitoring
- 4KB boundary crossing detection
- Response timeout detection

### 4. Debug Visibility
- Configurable verbosity levels
- Timestamp correlation with waveforms
- Ready/valid handshake tracking
- Transaction completion status

## Usage

### Method 1: Enhanced GUI Launcher
```bash
python3 bus_matrix_gui_enhanced.py
```

### Method 2: Patch Existing GUI
```python
import enhanced_vip_patch  # This auto-applies the patch
from bus_matrix_gui import main
main()
```

### Method 3: Direct Import
```python
from vip_environment_generator_enhanced import VIPEnvironmentGeneratorEnhanced

# Use instead of VIPEnvironmentGenerator
vip_gen = VIPEnvironmentGeneratorEnhanced(config, mode)
vip_gen.generate_environment_enhanced(output_path)
```

## Debugging with Enhanced VIP

### Console Output
Look for these log patterns:
- `[BFM]` - BFM operation messages
- `[MONITOR]` - Monitor observations
- `[axi4_master_driver]` - Driver transactions
- `[BFM_CONNECTOR]` - Signal connections

### Waveform Signals
Key signals to observe:
- `master_bfm[n].master_driver_bfm_h.*` - BFM driver signals
- `master_bfm[n].master_monitor_bfm_h.*` - BFM monitor signals
- `axi_if[n].*` - AXI interface signals
- `bfm_connector.* ` - Connection debugging

### Common Issues
1. **No ready signal**: Check "Waiting for AWREADY" messages
2. **Timeout**: Look for "ERROR - timeout" in BFM messages
3. **Protocol violation**: Check assertion failures
4. **Missing handshake**: Verify ready/valid in logs

## Configuration

Set these options in generated tests:
- `+UVM_VERBOSITY=UVM_HIGH` - Maximum debug visibility
- `+fsdb_file=debug.fsdb` - Waveform output file
- `+UVM_TESTNAME=debug_bfm_test` - Run debug test

## Integration

The enhanced generator is backward compatible and can be used as a drop-in replacement for the standard VIPEnvironmentGenerator.
