#!/bin/bash

# Launch script for AXI4 RTL & VIP Generator - Streamlined GUI

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
GUI_DIR="$SCRIPT_DIR/src"

echo "=========================================="
echo "AMBA AXI4 Generator v3 - Streamlined GUI"
echo "=========================================="
echo ""
echo "Single-page interface with:"
echo "  ✓ Templates at top (Quick start buttons)"
echo "  ✓ Canvas in middle (Direct view, no tabs)"
echo "  ✓ CLI at bottom (Always visible)"
echo ""
echo "Starting streamlined GUI..."
echo ""

cd "$GUI_DIR"
python3 main_gui_v3_streamlined.py

if [ $? -ne 0 ]; then
    echo "Error: Failed to launch GUI"
    echo "Please ensure Python 3 and tkinter are installed"
    exit 1
fi