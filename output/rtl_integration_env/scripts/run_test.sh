#!/bin/bash
# VCS Run Script

# Run simulation
./simv +UVM_TESTNAME=$1 -l sim.log

echo "Simulation complete! Check sim.log for results."
