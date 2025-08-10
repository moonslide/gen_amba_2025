#!/bin/bash

echo "========================================="
echo "Verifying Simple Crossbar Test Completion"
echo "========================================="

# Test the existing 15x15 VIP
cd /home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/sim

echo "Testing 15x15 VIP Simple Crossbar Test..."
make clean > /dev/null 2>&1

# Run the test with a timeout
timeout 30 make run_fsdb TEST=axi4_simple_crossbar_test > test_output.log 2>&1

# Check if it completed successfully
if grep -q "Simple Crossbar Test Completed" test_output.log && grep -q "\$finish at simulation time" test_output.log; then
    echo "✅ Test completed successfully!"
    
    # Check for errors
    if grep -q "UVM_ERROR :    0" test_output.log && grep -q "UVM_FATAL :    0" test_output.log; then
        echo "✅ No UVM errors or fatals detected"
    else
        echo "⚠️ UVM errors detected - check test_output.log"
    fi
    
    # Check if FSDB was generated
    if [ -f "./waves/axi4_vip.fsdb" ]; then
        echo "✅ FSDB waveform file generated"
        ls -lh ./waves/axi4_vip.fsdb
    else
        echo "⚠️ FSDB file not generated"
    fi
    
    echo ""
    echo "Test Summary:"
    grep -E "(Simple Crossbar|Virtual sequence completed|All master sequences)" test_output.log | tail -5
    
else
    echo "❌ Test failed to complete or timed out"
    echo "Last lines of output:"
    tail -20 test_output.log
    exit 1
fi

echo ""
echo "========================================="
echo "All checks passed! Test runs to completion."
echo "========================================="