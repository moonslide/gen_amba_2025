# Changelog

## RTL/VIP Integration (Latest)

### Added
- **Dual Mode VIP Support**: VIP now supports both Behavioral and RTL integration modes
- **GUI VIP Mode Selection**: Added radio buttons in UVM Export tab for mode selection
- **RTL Path Configuration**: Added RTL path entry and browse button (enabled in RTL mode)
- **RTL Wrapper Module**: Created `axi4_rtl_wrapper.sv` for seamless RTL/behavioral switching
- **Enhanced Config Export**: Updated `uvm_config_exporter.py` to include VIP mode and RTL path
- **Makefile VIP Support**: Added VIP_MODE and RTL_PATH parameters to Makefile
- **Multi-Master/Slave Support**: Updated testbench top to support configurable numbers of masters/slaves
- **Config Reader Updates**: Enhanced `axi4_config_reader.sv` to handle VIP mode from JSON

### Modified
- **UVM Export Tab**: Changed from simulation runner to proper configuration exporter
- **Testbench Architecture**: Updated `axi4_tb_top.sv` to instantiate RTL wrapper
- **Configuration Flow**: Added VIP mode to JSON export and UVM configuration

### Files Changed
1. `/axi4_vip/gui/src/uvm_config_exporter.py` - Added VIP mode support
2. `/axi4_vip/gui/src/vip_gui_integration.py` - Added mode selection UI
3. `/axi4_vip_sim/src/testbench/axi4_rtl_wrapper.sv` - New RTL integration wrapper
4. `/axi4_vip_sim/src/testbench/axi4_tb_top.sv` - Updated for multi-mode support
5. `/axi4_vip_sim/src/config/axi4_config_reader.sv` - Added VIP mode handling
6. `/axi4_vip_sim/Makefile` - Added VIP_MODE and RTL_PATH parameters

### Documentation
- Added `/docs/rtl_vip_integration.md` - Complete integration guide
- Created `/test_rtl_integration.sh` - Example test script

### Key Features
1. **Behavioral Model Testing**: Fast verification without RTL
2. **RTL Integration Testing**: Verify actual generated RTL
3. **Seamless Switching**: Easy mode selection from GUI
4. **Automated Flow**: One-click RTL generation and export
5. **Full UVM Support**: All VIP features work with both modes

### Usage
```bash
# Behavioral mode (default)
make run TEST=axi4_basic_test

# RTL integration mode
make run TEST=axi4_basic_test VIP_MODE=RTL RTL_PATH=output/rtl/axi4_interconnect.v
```

### Benefits
- Verify generated RTL with comprehensive UVM tests
- Find RTL-specific bugs early
- Measure actual RTL performance
- Leverage existing VIP test suite on custom RTL

---

## Previous Updates

### SystemVerilog/UVM VIP Implementation
- Complete AXI4 protocol support
- Master, slave, monitor agents
- Comprehensive test sequences
- Protocol compliance checking
- Multi-simulator support (VCS, Questa, Xcelium)

### GUI Improvements
- Masters on top, slaves on bottom layout
- No overlapping connection lines
- Drag and zoom functionality
- Flash animation on selection
- Dynamic interconnect text

### Configuration Management
- JSON-based configuration exchange
- Automated test script generation
- Organized output directory structure
- CLAUDE.md integration