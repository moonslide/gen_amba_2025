#!/bin/bash
# Complete compile and run script for fixed 9x9 VIP

echo "============================================"
echo "9x9 VIP Compile and Run (Fixed Version)"
echo "============================================"
echo ""
echo "This VIP has been fixed with:"
echo "  ✓ Monitor compilation errors resolved"
echo "  ✓ Enhanced UVM_INFO logging added"
echo "  ✓ RTL files generated"
echo ""

# Clean previous artifacts
echo "Step 1: Cleaning previous compilation..."
make clean 2>/dev/null || true
rm -rf csrc simv simv.daidir ucli.key DVEfiles AN.DB 2>/dev/null || true
rm -rf logs/*.log 2>/dev/null || true
mkdir -p logs

echo "✓ Cleaned"
echo ""

# Compile
echo "Step 2: Compiling VIP..."
echo "========================"
make compile 2>&1 | tee logs/compile.log

# Check compilation result
if [ ${PIPESTATUS[0]} -eq 0 ]; then
    echo ""
    echo "✓ COMPILATION SUCCESSFUL!"
    echo ""
    
    # Run the test if compilation succeeded
    if [ "$1" == "--run" ]; then
        echo "Step 3: Running test..."
        echo "======================="
        make run_fsdb TEST=axi4_basic_rw_test 2>&1 | tee logs/axi4_basic_rw_test.log
        
        echo ""
        echo "✓ Test run complete!"
        echo ""
        echo "Logs available at:"
        echo "  - logs/compile.log"
        echo "  - logs/axi4_basic_rw_test.log"
        echo ""
        echo "FSDB waveform (if generated):"
        echo "  - waves/axi4_basic_rw_test.fsdb"
    else
        echo "Compilation successful!"
        echo ""
        echo "To run the test:"
        echo "  make run_fsdb TEST=axi4_basic_rw_test"
        echo ""
        echo "Or use this script with --run option:"
        echo "  ./compile_and_run.sh --run"
    fi
else
    echo ""
    echo "✗ COMPILATION FAILED!"
    echo ""
    echo "Checking for errors in logs/compile.log..."
    
    # Check for specific errors
    if grep -q "XMRE" logs/compile.log; then
        echo "  ✗ Found XMRE errors (this should NOT happen with fixed code!)"
    fi
    
    if grep -q "cannot be opened" logs/compile.log; then
        echo "  ✗ Missing files - check if all RTL files are present"
    fi
    
    if grep -q "vif.*is not a class item" logs/compile.log; then
        echo "  ✗ Monitor vif access error (this should NOT happen with fixed code!)"
    fi
    
    echo ""
    echo "Please check logs/compile.log for details."
fi