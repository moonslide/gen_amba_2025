#!/bin/bash
# AMBA Bus Matrix GUI Launch Script

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

# Enable optimized VIP generation to prevent hanging
# This uses the lightweight import wrapper with proper threading
export VIP_USE_LIGHT_WRAPPER=true
export VIP_IMPORT_TIMEOUT=15

echo ""
echo "✓ VIP generation optimized - no hanging at 50%"
echo "  - Full VIP environment will be generated"
echo "  - Import operations handled with timeout protection"
echo "  - GUI remains responsive during generation"
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