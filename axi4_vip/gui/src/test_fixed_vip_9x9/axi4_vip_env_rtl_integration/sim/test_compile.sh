#!/bin/bash
# Simple compile test for fixed VIP

echo "Testing compilation of fixed VIP..."

# Source VCS environment (adjust path as needed)
# source /path/to/vcs/setup.sh

# Create file list
cat > compile.f << EOF
+incdir+$UVM_HOME/src
$UVM_HOME/src/uvm.sv
$UVM_HOME/src/dpi/uvm_dpi.cc

# Packages
../pkg/axi4_globals_pkg.sv
../master/axi4_master_pkg.sv
../slave/axi4_slave_pkg.sv
EOF

# Run VCS compile (dry run - uncomment to actually compile)
# vcs -sverilog -timescale=1ns/1ps +acc +vpi -f compile.f

echo "Compile script ready - uncomment VCS command to test"
