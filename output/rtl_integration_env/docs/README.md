# RTL Integration Environment with tim_axi4_vip

This environment integrates the tim_axi4_vip (https://github.com/moonslide/tim_axi4_vip) with your RTL DUT.

## Directory Structure
- `tb/` - Testbench files
- `tb/tests/` - Test cases  
- `tim_axi4_vip/` - Symbolic link to tim_axi4_vip
- `rtl_wrapper/` - RTL wrapper with automated connections
- `scripts/` - Compilation and run scripts
- `configs/` - Configuration files

## Quick Start

1. **Add Your RTL DUT**
   - Copy your RTL files to the `rtl_wrapper/` directory
   - Edit `rtl_wrapper/dut_wrapper.sv`:
     - Replace 'your_axi_dut' with your module name
     - Adjust parameter names if needed
     - Remove unused signals (e.g., user signals)

2. **Update File List**
   - Edit `scripts/filelist.f`
   - Add your RTL files at the marked location

3. **Compile**
   ```bash
   cd scripts
   ./compile.sh
   ```

4. **Run Test**
   ```bash
   ./run_test.sh axi4_rtl_basic_test
   ```

## Available Tests
- `axi4_rtl_basic_test` - Basic read/write test
- All tests from tim_axi4_vip are available

## Configuration
- Bus Type: AXI4
- Data Width: 64 bits
- Address Width: 32 bits
- ID Width: 4 bits
- Masters: 2
- Slaves: 3

## Automated Features
- All AXI4 signals are pre-connected in the wrapper
- Standard parameter mappings are included
- Common port name variations are documented

## Troubleshooting
- If compilation fails, check that $VCS_HOME is set
- Ensure your DUT port names match the wrapper connections
- See tim_axi4_vip documentation for advanced features
