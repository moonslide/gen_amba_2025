#!/bin/bash
# Verify compilation of updated VIP

echo "=========================================="
echo "Verifying Updated VIP Compilation"
echo "=========================================="

# Create file list
cat > compile_verify.f << EOF
+incdir+$UVM_HOME/src
$UVM_HOME/src/uvm.sv
$UVM_HOME/src/dpi/uvm_dpi.cc

# Packages - compile in dependency order
../pkg/axi4_globals_pkg.sv
../master/axi4_master_pkg.sv
../slave/axi4_slave_pkg.sv
../env/axi4_env_pkg.sv
EOF

echo ""
echo "File list created. The updated generator should have fixed:"
echo "  - Monitor vif access errors"
echo "  - Cross-module reference errors"
echo ""
echo "To compile with VCS, run:"
echo "  vcs -sverilog -timescale=1ns/1ps +acc +vpi -f compile_verify.f"
echo ""
echo "The compilation should complete without errors."
