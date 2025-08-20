#!/bin/bash
#------------------------------------------------------------------------------
# gen_axi_with_tb.sh - Generate AXI interconnect with unified testbench
# Usage: ./gen_axi_with_tb.sh [gen_amba_axi options] --tb <tb_filename>
#------------------------------------------------------------------------------

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
GEN_AXI="$SCRIPT_DIR/gen_amba_axi"
TB_TEMPLATE="$SCRIPT_DIR/../test_rtl_02/rtl/tb_axi4_unified.v"

# Default values
TB_FILE=""
RTL_FILE=""
MASTER_COUNT=2
SLAVE_COUNT=2
PREFIX=""
WIDTH_AD=32
WIDTH_DA=64

# Parse arguments
GEN_ARGS=""
while [[ $# -gt 0 ]]; do
    case $1 in
        --tb)
            TB_FILE="$2"
            shift 2
            ;;
        --tb=*)
            TB_FILE="${1#*=}"
            shift
            ;;
        --master=*)
            MASTER_COUNT="${1#*=}"
            GEN_ARGS="$GEN_ARGS $1"
            shift
            ;;
        -M)
            MASTER_COUNT="$2"
            GEN_ARGS="$GEN_ARGS $1 $2"
            shift 2
            ;;
        --slave=*)
            SLAVE_COUNT="${1#*=}"
            GEN_ARGS="$GEN_ARGS $1"
            shift
            ;;
        -S)
            SLAVE_COUNT="$2"
            GEN_ARGS="$GEN_ARGS $1 $2"
            shift 2
            ;;
        --output=*)
            RTL_FILE="${1#*=}"
            GEN_ARGS="$GEN_ARGS $1"
            shift
            ;;
        -O)
            RTL_FILE="$2"
            GEN_ARGS="$GEN_ARGS $1 $2"
            shift 2
            ;;
        --prefix=*)
            PREFIX="${1#*=}"
            GEN_ARGS="$GEN_ARGS $1"
            shift
            ;;
        -P)
            PREFIX="$2"
            GEN_ARGS="$GEN_ARGS $1 $2"
            shift 2
            ;;
        --addr-width=*)
            WIDTH_AD="${1#*=}"
            GEN_ARGS="$GEN_ARGS $1"
            shift
            ;;
        -A)
            WIDTH_AD="$2"
            GEN_ARGS="$GEN_ARGS $1 $2"
            shift 2
            ;;
        --data-width=*)
            WIDTH_DA="${1#*=}"
            GEN_ARGS="$GEN_ARGS $1"
            shift
            ;;
        -W)
            WIDTH_DA="$2"
            GEN_ARGS="$GEN_ARGS $1 $2"
            shift 2
            ;;
        -h|--help)
            echo "Usage: $0 [gen_amba_axi options] --tb <testbench_file>"
            echo ""
            echo "This script generates both AXI RTL and unified testbench."
            echo ""
            echo "Additional options:"
            echo "  --tb <file>      Generate unified testbench to this file"
            echo ""
            echo "All other options are passed to gen_amba_axi:"
            $GEN_AXI --help
            exit 0
            ;;
        *)
            # Pass through to gen_amba_axi (for other options like -3, -q, etc.)
            GEN_ARGS="$GEN_ARGS $1"
            shift
            ;;
    esac
done

# Check if generator exists
if [[ ! -x "$GEN_AXI" ]]; then
    echo "ERROR: $GEN_AXI not found or not executable"
    echo "Please build the generator first: cd $SCRIPT_DIR && make"
    exit 1
fi

# Generate RTL first
echo "Generating AXI RTL..."
echo "DEBUG: Running: $GEN_AXI $GEN_ARGS"
$GEN_AXI $GEN_ARGS

if [[ $? -ne 0 ]]; then
    echo "ERROR: RTL generation failed"
    exit 1
fi

# Generate unified testbench if requested
if [[ -n "$TB_FILE" ]]; then
    echo "Generating unified testbench: $TB_FILE"
    
    # Check if template exists
    if [[ ! -f "$TB_TEMPLATE" ]]; then
        echo "ERROR: Template testbench not found: $TB_TEMPLATE"
        exit 1
    fi
    
    # Copy and modify template
    cp "$TB_TEMPLATE" "$TB_FILE"
    
    # Update module parameters based on command line
    sed -i "s/parameter NUM_MASTER = [0-9]*/parameter NUM_MASTER = $MASTER_COUNT/" "$TB_FILE"
    sed -i "s/parameter NUM_SLAVE  = [0-9]*/parameter NUM_SLAVE  = $SLAVE_COUNT/" "$TB_FILE"
    sed -i "s/parameter WIDTH_AD   = [0-9]*/parameter WIDTH_AD   = $WIDTH_AD/" "$TB_FILE"
    sed -i "s/parameter WIDTH_DA   = [0-9]*/parameter WIDTH_DA   = $WIDTH_DA/" "$TB_FILE"
    
    # Update module name if prefix is used
    if [[ -n "$PREFIX" ]]; then
        sed -i "s/amba_axi_m2s2/${PREFIX}_axi_m${MASTER_COUNT}s${SLAVE_COUNT}/" "$TB_FILE"
        sed -i "s/tb_axi4_unified/tb_${PREFIX}_axi4_unified/" "$TB_FILE"
    else
        sed -i "s/amba_axi_m2s2/amba_axi_m${MASTER_COUNT}s${SLAVE_COUNT}/" "$TB_FILE"
    fi
    
    # Update slave address parameters for different counts
    if [[ $SLAVE_COUNT -gt 2 ]]; then
        # First add comma after ADDR_LENGTH1(12)
        sed -i 's/ADDR_LENGTH1(12)/ADDR_LENGTH1(12),/' "$TB_FILE"
        
        # Add more slave parameters (simplified - assumes equal spacing)
        for ((i=2; i<$SLAVE_COUNT; i++)); do
            base_addr=$((0x2000 + i * 0x2000))
            echo "        .SLAVE_EN${i}(1)," >> temp_params
            echo "        .ADDR_BASE${i}(32'h$(printf "%08X" $base_addr))," >> temp_params
            if [[ $i -eq $((SLAVE_COUNT-1)) ]]; then
                # Last slave - no comma
                echo "        .ADDR_LENGTH${i}(12)" >> temp_params
            else
                echo "        .ADDR_LENGTH${i}(12)," >> temp_params
            fi
        done
        # Insert new parameters after ADDR_LENGTH1(12),
        sed -i '/ADDR_LENGTH1(12),/r temp_params' "$TB_FILE"
        rm -f temp_params
    fi
    
    echo "Generated unified testbench with:"
    echo "  Masters: $MASTER_COUNT"
    echo "  Slaves: $SLAVE_COUNT"
    echo "  Address width: $WIDTH_AD"
    echo "  Data width: $WIDTH_DA"
    echo "  Prefix: ${PREFIX:-none}"
fi

echo "Generation completed successfully!"
echo ""
echo "Usage examples:"
echo "  # Compile and run simple test"
echo "  vcs -full64 -sverilog $RTL_FILE $TB_FILE -o simv_test"
echo "  ./simv_test +TEST_MODE=SIMPLE"
echo ""
echo "  # Run all tests with FSDB"
echo "  vcs -full64 -sverilog +define+DUMP_FSDB $RTL_FILE $TB_FILE -o simv_test"
echo "  ./simv_test +TEST_MODE=ALL +fsdbfile+waves/test.fsdb"