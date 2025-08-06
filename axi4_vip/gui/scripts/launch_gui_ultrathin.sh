#!/bin/bash
# AMBA Bus Matrix GUI Launch Script - UltraThin Version
# Fixes the 50% hanging issue by deferring heavy imports

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
GUI_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# Check if we can find the main GUI file
if [ ! -f "$GUI_DIR/src/bus_matrix_gui.py" ]; then
    echo "Error: Cannot find bus_matrix_gui.py in $GUI_DIR/src/"
    echo "Please ensure the script is in the correct location"
    exit 1
fi

# Change to GUI directory
cd "$GUI_DIR"

# Check Python dependencies
echo "Checking Python dependencies..."
python3 -c "import tkinter; print('✓ tkinter')" 2>/dev/null || (echo "✗ tkinter not installed" && exit 1)
python3 -c "import matplotlib; print('✓ matplotlib')" 2>/dev/null || (echo "✗ matplotlib not installed" && exit 1)
python3 -c "import numpy; print('✓ numpy')" 2>/dev/null || (echo "✗ numpy not installed" && exit 1)

echo "All dependencies installed, launching GUI..."

# FIXED VERSION: Use the working 7/29 approach (10-step RTL mode)
# This prevents the GUI from hanging at 50% during initialization
export VIP_DEFER_IMPORTS=true

echo ""
echo "✓ Using FIXED version with enhanced scalability"
echo "  - RTL mode: 10 steps (not 12)"
echo "  - VIP standalone: 6 steps"
echo "  - Fixed: Progress continues from step 6→7→8→9→10"
echo "  - Fixed: 11x11+ matrix support with timeout handling"
echo "  - Fixed: No more hanging at step 7/10 (70%)"
echo ""

# Set up signal handlers to ensure clean shutdown
cleanup() {
    echo "Cleaning up..."
    # Kill all child processes
    pkill -P $$
    exit 0
}

# Trap signals to ensure cleanup
trap cleanup EXIT INT TERM

# Launch GUI with exec to replace the shell process
# This ensures the Python process gets signals directly
exec python3 src/bus_matrix_gui.py "$@"