#!/bin/bash
#==============================================================================
# Script to run AXI4 VIP simulation with waveform dumping
# Generated for easy waveform generation
#==============================================================================

# Default values
TEST=${1:-axi4_base_test}
SEED=${2:-1}
DUMP_TYPE=${3:-fsdb}  # fsdb or vcd

echo "======================================================================"
echo "Running AXI4 VIP Simulation with Waveform Dumping"
echo "======================================================================"
echo "Test: $TEST"
echo "Seed: $SEED"
echo "Dump Type: $DUMP_TYPE"
echo ""

# Clean previous waves
echo "Cleaning previous waveform files..."
rm -f waves/*.fsdb waves/*.vcd

# Run simulation based on dump type
if [ "$DUMP_TYPE" = "fsdb" ]; then
    echo "Running with FSDB dumping enabled..."
    make run_fsdb TEST=$TEST SEED=$SEED
    
    # Check if FSDB was generated
    if [ -f "waves/${TEST}_${SEED}.fsdb" ]; then
        echo ""
        echo "✅ FSDB waveform generated successfully!"
        echo "   File: waves/${TEST}_${SEED}.fsdb"
        echo ""
        echo "To view waveforms:"
        echo "   verdi -ssf waves/${TEST}_${SEED}.fsdb &"
    else
        echo ""
        echo "❌ FSDB file not generated. Check simulation log for errors."
        echo "   Log file: logs/${TEST}_${SEED}.log"
    fi
    
elif [ "$DUMP_TYPE" = "vcd" ]; then
    echo "Running with VCD dumping enabled..."
    make run_vcd TEST=$TEST SEED=$SEED
    
    # Check if VCD was generated
    if [ -f "waves/${TEST}_${SEED}.vcd" ]; then
        echo ""
        echo "✅ VCD waveform generated successfully!"
        echo "   File: waves/${TEST}_${SEED}.vcd"
        echo ""
        echo "To view waveforms:"
        echo "   gtkwave waves/${TEST}_${SEED}.vcd &"
    else
        echo ""
        echo "❌ VCD file not generated. Check simulation log for errors."
        echo "   Log file: logs/${TEST}_${SEED}.log"
    fi
    
else
    echo "❌ Invalid dump type. Use 'fsdb' or 'vcd'"
    exit 1
fi

echo ""
echo "======================================================================"