#!/bin/bash
#==============================================================================
# Launch script for AMBA Bus Matrix Configuration GUI
#==============================================================================

# Function to handle errors properly whether sourced or executed
launch_gui() {
    # Get the directory of this script
    local SCRIPT_DIR
    if [ -n "${BASH_SOURCE[0]}" ]; then
        SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
    else
        SCRIPT_DIR="$( cd "$( dirname "$0" )" && pwd )"
    fi

    # Check if Python 3 is installed
    if ! command -v python3 &> /dev/null; then
        echo "Error: Python 3 is required but not installed."
        echo "Please install Python 3 and try again."
        return 1
    fi

    # Check Python version
    local PYTHON_VERSION=$(python3 -c 'import sys; print(".".join(map(str, sys.version_info[:2])))')
    local REQUIRED_VERSION="3.6"

    if [ "$(printf '%s\n' "$REQUIRED_VERSION" "$PYTHON_VERSION" | sort -V | head -n1)" != "$REQUIRED_VERSION" ]; then
        echo "Error: Python $REQUIRED_VERSION or higher is required (found $PYTHON_VERSION)"
        return 1
    fi
    
    # Check for tkinter
    if ! python3 -c "import tkinter" 2>/dev/null; then
        echo "Error: Python tkinter module is not installed."
        echo "Please install it with: sudo yum install python3-tkinter"
        return 1
    fi

    # Launch the GUI
    echo "Launching AMBA Bus Matrix Configuration GUI..."
    echo "Python version: $PYTHON_VERSION"
    cd "$SCRIPT_DIR"
    python3 src/bus_matrix_gui.py

    # Check exit status
    if [ $? -ne 0 ]; then
        echo "Error: GUI exited with an error"
        return 1
    fi
    
    return 0
}

# Execute the function
launch_gui