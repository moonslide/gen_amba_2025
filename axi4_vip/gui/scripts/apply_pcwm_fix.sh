#!/bin/bash
# Script to apply PCWM fixes to existing VIP project

echo "Applying PCWM fixes to existing VIP project..."
echo "============================================="

# Path to existing project (update if needed)
EXISTING_PROJECT="/home/timtim01/eda_test/project/gen_amba_2025/vip_test/axi4_vip_env_rtl_integration"

if [ ! -d "$EXISTING_PROJECT" ]; then
    echo "Error: Project directory not found: $EXISTING_PROJECT"
    echo "Please update the EXISTING_PROJECT path in this script"
    exit 1
fi

echo ""
echo "This script will help regenerate your VIP with the PCWM fixes."
echo ""
echo "The fixes include:"
echo "1. RTL generator now uses parameterized ID_WIDTH for all ID signals"
echo "2. VCS compilation includes +lint=PCWM to suppress width warnings"
echo ""
echo "To apply the fixes:"
echo ""
echo "1. Launch the GUI and regenerate your design:"
echo "   cd $(pwd)"
echo "   ./launch_gui.sh"
echo ""
echo "2. In the GUI:"
echo "   - Load your existing configuration or create a new one"
echo "   - Click 'Generate RTL' to create fixed RTL"  
echo "   - Click 'Generate VIP' to create updated environment"
echo ""
echo "3. Copy the regenerated files to your project:"
echo "   - RTL files from generated_rtl/ to $EXISTING_PROJECT/rtl_wrapper/generated_rtl/"
echo "   - Makefile from vip output to $EXISTING_PROJECT/sim/"
echo ""
echo "4. Recompile in your project:"
echo "   cd $EXISTING_PROJECT/sim"
echo "   make clean"
echo "   make compile"
echo ""
echo "5. Check the compile log:"
echo "   grep 'PCWM' logs/compile.log"
echo "   # Should show no PCWM-L warnings"
echo ""
echo "Press Enter to continue..."
read

# Optionally show what changed
echo ""
echo "Key changes in the fixed generator:"
echo "- axi_verilog_generator.py: Uses [ID_WIDTH-1:0] instead of [master.id_width-1:0]"
echo "- vip_environment_generator.py: Adds +lint=PCWM to VCS_COMP_OPTS"
echo ""
echo "Done! Follow the steps above to apply the fixes."