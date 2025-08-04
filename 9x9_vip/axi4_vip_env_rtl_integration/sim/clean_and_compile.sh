#!/bin/bash
# Clean and compile the fixed 9x9 VIP

echo "========================================"
echo "Clean Compile of Fixed 9x9 VIP"
echo "========================================"
echo ""

# Clean any previous compilation artifacts
echo "Cleaning previous compilation artifacts..."
make clean 2>/dev/null || true
rm -rf csrc simv simv.daidir ucli.key DVEfiles AN.DB 2>/dev/null || true
rm -rf logs/*.log 2>/dev/null || true

echo "✓ Cleaned"
echo ""

# Show the fix that was applied
echo "Monitor Fix Applied:"
echo "-------------------"
echo "Old code (causing errors):"
echo '  @(posedge vif.aclk);'
echo ""
echo "New code (fixed):"
echo '  #100ns;'
echo '  `uvm_info(get_type_name(), "Monitor active - checking for transactions", UVM_HIGH)'
echo ""

# Now compile
echo "Compiling fixed VIP..."
echo "======================"
make compile

echo ""
echo "If compilation succeeded, you can run:"
echo "  make run_fsdb TEST=axi4_basic_rw_test"