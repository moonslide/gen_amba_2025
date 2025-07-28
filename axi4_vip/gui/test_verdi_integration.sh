#!/bin/bash
# Test script for Verdi integration features

echo "Testing Verdi Integration Features"
echo "=================================="

# Create test directory
TEST_DIR="test_verdi_output"
rm -rf $TEST_DIR
mkdir -p $TEST_DIR

# Generate a test VIP environment
echo "1. Generating test VIP environment..."
python3 src/test_vip_generation.py > /dev/null 2>&1

# Navigate to a generated sim directory (if exists)
if [ -d "vip_output/axi4_vip_env_rtl_integration/sim" ]; then
    cd vip_output/axi4_vip_env_rtl_integration/sim
    echo "   ✓ VIP environment generated"
    
    # Check Makefile for -lca -kdb
    echo ""
    echo "2. Checking VCS compilation flags..."
    if grep -q "\-lca \-kdb" Makefile; then
        echo "   ✓ -lca -kdb flags found in Makefile"
    else
        echo "   ✗ -lca -kdb flags NOT found in Makefile"
    fi
    
    # Check for enhanced verdi target
    echo ""
    echo "3. Checking enhanced 'make verdi' target..."
    if grep -q "Auto-loading last run in Verdi" Makefile; then
        echo "   ✓ Enhanced verdi target found"
        
        # Show the verdi target
        echo ""
        echo "   Verdi target content:"
        sed -n '/^verdi:/,/^[a-zA-Z]/p' Makefile | head -n -1 | sed 's/^/   /'
    else
        echo "   ✗ Enhanced verdi target NOT found"
    fi
    
    # Check for Verdi scripts
    echo ""
    echo "4. Checking Verdi scripts..."
    SCRIPTS=(
        "scripts/axi4_signals.rc"
        "scripts/axi4_session.ses"
        "scripts/verdi_auto_load.tcl"
        ".verdirc"
    )
    
    for script in "${SCRIPTS[@]}"; do
        if [ -f "$script" ]; then
            echo "   ✓ $script exists"
        else
            echo "   ✗ $script NOT found"
        fi
    done
    
    # Show usage example
    echo ""
    echo "5. Usage Example:"
    echo "   cd $(pwd)"
    echo "   make run_fsdb TEST=axi4_basic_rw_test  # Run with FSDB dumping"
    echo "   make verdi                              # Auto-load in Verdi"
    
    cd - > /dev/null
else
    echo "   ✗ VIP environment not generated"
fi

echo ""
echo "Test Complete!"
echo ""
echo "To use the features:"
echo "1. Generate VIP using the GUI"
echo "2. Navigate to <output>/sim directory"
echo "3. Run: make run_fsdb TEST=<test_name>"
echo "4. Run: make verdi"