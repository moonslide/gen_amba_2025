#!/bin/bash
# AXI4 VIP GUI Launcher Script
# Enhanced gen_amba_2025 with Traffic Monitoring

echo "🚀 Launching AXI4 VIP Generator GUI..."
echo "✨ Enhanced gen_amba_2025 with Traffic Monitoring"
echo "📊 Features: Real-time Analytics, Zero UVM_ERRORs, 2x2-64x64 Support"
echo ""

# Get script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
GUI_DIR="$(dirname "$SCRIPT_DIR")/src"

# Check if Python3 is available
if ! command -v python3 &> /dev/null; then
    echo "❌ Error: python3 is required but not installed"
    exit 1
fi

# Check if GUI files exist
if [ ! -f "$GUI_DIR/vip_gui_integration.py" ]; then
    echo "❌ Error: vip_gui_integration.py not found in $GUI_DIR"
    exit 1
fi

# Launch GUI
echo "📁 GUI Directory: $GUI_DIR"
echo "🖥️ Starting GUI..."
echo ""

cd "$GUI_DIR"
python3 bus_matrix_gui.py

echo ""
echo "👋 GUI session ended"