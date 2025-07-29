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

# Launch GUI
python3 src/bus_matrix_gui.py "$@"