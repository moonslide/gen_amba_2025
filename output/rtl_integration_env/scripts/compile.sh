#!/bin/bash
# VCS Compilation Script for rtl_integration

# Set environment
export VCS_HOME=$VCS_HOME

# Compile options
VCS_OPTS="-full64 -sverilog -debug_all +v2k -timescale=1ns/1ps -ntb_opts uvm"

# Compile design
vcs $VCS_OPTS \
    -f filelist.f \
    -o simv \
    +define+RTL_INTEGRATION \
    +incdir+$VCS_HOME/etc/uvm-1.2/src \
    $VCS_HOME/etc/uvm-1.2/src/uvm_pkg.sv

echo "Compilation complete!"
