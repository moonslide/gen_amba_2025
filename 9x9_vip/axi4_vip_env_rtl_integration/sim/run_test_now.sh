#!/bin/bash
# Run the exact command the user requested with the fixed VIP

echo "============================================"
echo "Running Your Test with Fixed 9x9 VIP"
echo "============================================"
echo ""
echo "This script runs the exact command you requested:"
echo "  make run_fsdb TEST=axi4_basic_rw_test"
echo ""
echo "The VIP has been regenerated to fix compilation errors."
echo ""

# Create logs directory if needed
mkdir -p logs

# First ensure it's compiled
echo "Step 1: Ensuring VIP is compiled..."
echo "-----------------------------------"
if [ ! -f simv ]; then
    echo "No simv found, compiling first..."
    make compile
    if [ $? -ne 0 ]; then
        echo ""
        echo "✗ Compilation failed!"
        echo "This should not happen with the fixed code."
        echo "Please check logs/compile.log"
        exit 1
    fi
else
    echo "✓ simv already exists"
fi

echo ""
echo "Step 2: Running test with FSDB..."
echo "---------------------------------"
echo "Command: make run_fsdb TEST=axi4_basic_rw_test"
echo ""

# Run the actual command
make run_fsdb TEST=axi4_basic_rw_test

echo ""
echo "Test run complete!"
echo ""
echo "To view enhanced UVM_INFO logs:"
echo "  grep UVM_INFO logs/axi4_basic_rw_test.log"
echo ""
echo "To view FSDB waveform:"
echo "  verdi -ssf waves/axi4_basic_rw_test.fsdb &"