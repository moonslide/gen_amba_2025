#!/bin/bash
# Generate the missing RTL files for 9x9 AXI interconnect

echo "============================================"
echo "Generating RTL for 9x9 AXI Interconnect"
echo "============================================"
echo ""

# Go to gen_amba_2025 directory
cd /home/timtim01/eda_test/project/gen_amba_2025

# Check if gen_amba_axi exists
if [ ! -f gen_amba_axi/gen_amba_axi ]; then
    echo "Building gen_amba_axi tool..."
    cd gen_amba_axi
    make clean
    make
    cd ..
fi

# Generate the 9x9 interconnect RTL
echo "Generating 9x9 AXI interconnect RTL..."
echo "Command: ./gen_amba_axi/gen_amba_axi --master=9 --slave=9 --output=9x9_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m9s9.v"

./gen_amba_axi/gen_amba_axi \
    --master=9 \
    --slave=9 \
    --output=9x9_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m9s9.v

if [ $? -eq 0 ]; then
    echo ""
    echo "✓ RTL generation successful!"
    echo ""
    echo "Generated files:"
    ls -la 9x9_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/*.v 2>/dev/null || echo "  (checking...)"
    
    # The gen_amba_axi tool generates all required files together
    echo ""
    echo "Now you can compile the VIP with:"
    echo "  cd 9x9_vip/axi4_vip_env_rtl_integration/sim"
    echo "  make compile"
else
    echo ""
    echo "✗ RTL generation failed!"
    echo "Please check if gen_amba_axi is built correctly."
fi