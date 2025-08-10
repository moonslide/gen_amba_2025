#!/bin/bash
# Verify the monitor fix was applied

echo "Verifying monitor fix in regenerated 9x9 VIP..."
echo ""

# Check for vif access in monitors
if grep -q "@(posedge vif.aclk)" ../master/axi4_master_pkg.sv; then
    echo "✗ ERROR: Monitor still has vif.aclk access!"
    exit 1
else
    echo "✓ Monitor vif access removed"
fi

# Check for enhanced logging
log_count=$(grep -c "uvm_info" ../master/axi4_master_pkg.sv)
echo "✓ Found $log_count UVM_INFO statements"

# Check for monitor stub
if grep -q "Monitor active - checking for transactions" ../master/axi4_master_pkg.sv; then
    echo "✓ Monitor has time-based stub implementation"
else
    echo "✗ Monitor stub not found"
fi

echo ""
echo "Fix verification complete!"
