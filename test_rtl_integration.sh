#!/bin/bash
#==============================================================================
# Test script for RTL integration with VIP
# Demonstrates the full flow from GUI export to UVM simulation with RTL
#==============================================================================

set -e

# Colors for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

echo -e "${GREEN}=== AXI4 VIP RTL Integration Test ===${NC}"
echo ""

# Step 1: Generate RTL from GUI
echo -e "${YELLOW}Step 1: Generating RTL from GUI configuration...${NC}"
cd axi4_vip/gui
python -c "
from src.bus_config import BusConfig, Master, Slave
from src.axi_verilog_generator import AXIVerilogGenerator
import os

# Create sample configuration
config = BusConfig()
config.bus_type = 'AXI4'
config.addr_width = 32
config.data_width = 64

# Add masters
config.masters.append(Master('CPU', 0, 0))
config.masters.append(Master('DMA', 1, 0))

# Add slaves
config.slaves.append(Slave('Memory', 0x10000000, 256*1024))  # 256MB at 0x10000000
config.slaves.append(Slave('Peripheral1', 0x20000000, 1024))   # 1MB at 0x20000000
config.slaves.append(Slave('Peripheral2', 0x30000000, 1024))   # 1MB at 0x30000000

# Generate RTL
generator = AXIVerilogGenerator(config)
rtl_path = '../../axi4_vip_sim/output/rtl/axi4_interconnect_test.v'
os.makedirs(os.path.dirname(rtl_path), exist_ok=True)
if generator.generate_verilog(rtl_path):
    print(f'✅ RTL generated: {rtl_path}')
else:
    print('❌ RTL generation failed')
    exit(1)
"

# Step 2: Export UVM configuration with RTL mode
echo -e "${YELLOW}Step 2: Exporting UVM configuration with RTL mode...${NC}"
python -c "
from src.bus_config import BusConfig, Master, Slave
from src.uvm_config_exporter import export_gui_config_to_uvm
import os

# Create same configuration
config = BusConfig()
config.bus_type = 'AXI4'
config.addr_width = 32
config.data_width = 64

# Add masters
config.masters.append(Master('CPU', 0, 0))
config.masters.append(Master('DMA', 1, 0))

# Add slaves  
config.slaves.append(Slave('Memory', 0x10000000, 256*1024))
config.slaves.append(Slave('Peripheral1', 0x20000000, 1024))
config.slaves.append(Slave('Peripheral2', 0x30000000, 1024))

# Export with RTL mode
rtl_path = '../../axi4_vip_sim/output/rtl/axi4_interconnect_test.v'
export_paths = export_gui_config_to_uvm(config, 
                                       vip_mode='RTL', 
                                       rtl_path=rtl_path,
                                       output_dir='../../axi4_vip_sim/output')
print('✅ UVM configuration exported')
for name, path in export_paths.items():
    print(f'  • {name}: {path}')
"

# Step 3: Run UVM simulation with RTL
echo -e "${YELLOW}Step 3: Running UVM simulation with RTL integration...${NC}"
cd ../../axi4_vip_sim

# Run basic test with RTL mode
echo -e "${GREEN}Running basic test with RTL integration...${NC}"
make run TEST=axi4_basic_test \
         CONFIG_FILE=output/configs/axi4_config_*.json \
         VIP_MODE=RTL \
         RTL_PATH=output/rtl/axi4_interconnect_test.v

# Check results
echo ""
echo -e "${GREEN}=== Test Complete ===${NC}"
echo "Check logs in: axi4_vip_sim/output/logs/"
echo ""

# Show summary
if grep -q "TEST PASSED" output/logs/axi4_basic_test.log 2>/dev/null; then
    echo -e "${GREEN}✅ RTL integration test PASSED!${NC}"
else
    echo -e "${RED}❌ RTL integration test FAILED${NC}"
    echo "Check logs for details"
fi