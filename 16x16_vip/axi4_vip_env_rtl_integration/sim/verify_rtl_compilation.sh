#!/bin/bash
#==============================================================================
# RTL Compilation Verification Script
# Verifies that the 16x16 AXI4 RTL can be compiled successfully
#==============================================================================

echo "======================================"
echo "16x16 AXI4 RTL Compilation Verification"
echo "======================================"

# Clean previous compilation
echo "🧹 Cleaning previous compilation..."
make clean > /dev/null 2>&1

# Run RTL compilation check
echo "🔍 Running RTL compilation check..."
if make compile_check > /dev/null 2>&1; then
    echo "✅ SUCCESS: 16x16 AXI4 RTL compilation passed!"
    
    # Check files were generated
    if [ -f "simv_rtl_check" ]; then
        echo "✅ Executable created: simv_rtl_check"
    fi
    
    if [ -d "simv_rtl_check.daidir" ]; then
        echo "✅ Simulation database created: simv_rtl_check.daidir"
    fi
    
    # Show compilation stats
    if [ -f "logs/compile.log" ]; then
        echo "📊 Compilation stats:"
        grep "CPU time" logs/compile.log | head -1
        echo "📊 Modules compiled:"
        grep "modules and" logs/compile.log | head -1
    fi
    
    echo ""
    echo "🎉 16x16 AXI4 RTL is ready for use!"
    echo "   - Use 'make help' to see available commands"
    echo "   - This is RTL-only mode (no UVM testbench for >10x10 matrices)"
    
else
    echo "❌ FAILED: RTL compilation failed"
    echo "Check logs/compile.log for details"
    exit 1
fi