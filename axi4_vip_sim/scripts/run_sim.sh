#!/bin/bash
#==============================================================================
# AXI4 VIP Simulation Runner Script
# Automated script for running AXI4 verification tests with VCS
#==============================================================================

set -e  # Exit on any error

# Script configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
OUTPUT_DIR="$PROJECT_DIR/output"
LOG_DIR="$OUTPUT_DIR/logs"
WORK_DIR="$OUTPUT_DIR/work"
WAVE_DIR="$OUTPUT_DIR/waves"
COV_DIR="$OUTPUT_DIR/coverage"
REPORT_DIR="$OUTPUT_DIR/reports"

# Default values
SIM="vcs"
TEST="axi4_basic_test"
VERBOSITY="UVM_MEDIUM"
GUI_MODE=0
COVERAGE=0
DUMP_WAVES=0
SEED=""
TIMEOUT="10ms"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored output
print_msg() {
    local color=$1
    local message=$2
    echo -e "${color}[AXI4_VIP] ${message}${NC}"
}

# Function to show usage
show_usage() {
    echo "AXI4 VIP Simulation Runner"
    echo "=========================="
    echo ""
    echo "Usage: $0 [options]"
    echo ""
    echo "Options:"
    echo "  -t, --test <name>        Test to run (default: axi4_basic_test)"
    echo "  -s, --sim <simulator>    Simulator (vcs, questa, xcelium)"
    echo "  -v, --verbosity <level>  UVM verbosity (UVM_LOW, UVM_MEDIUM, UVM_HIGH)"
    echo "  -g, --gui               Run with GUI"
    echo "  -c, --coverage          Enable coverage collection"
    echo "  -w, --waves             Dump waveforms"
    echo "  -r, --seed <number>     Random seed"
    echo "  --timeout <time>        Simulation timeout (default: 10ms)"
    echo "  --clean                 Clean before running"
    echo "  --regression            Run regression suite"
    echo "  -h, --help              Show this help"
    echo ""
    echo "Available Tests:"
    echo "  axi4_basic_test           Basic functionality test"
    echo "  axi4_comprehensive_test   Complete protocol test suite"
    echo ""
    echo "Examples:"
    echo "  $0 -t axi4_basic_test"
    echo "  $0 -t axi4_comprehensive_test -g -c"
    echo "  $0 --regression"
    echo "  $0 -t axi4_basic_test -w -v UVM_HIGH"
}

# Function to check if simulator is available
check_simulator() {
    local sim=$1
    case $sim in
        "vcs")
            if ! command -v vcs &> /dev/null; then
                print_msg $RED "VCS not found in PATH"
                exit 1
            fi
            ;;
        "questa")
            if ! command -v vsim &> /dev/null; then
                print_msg $RED "Questa not found in PATH"
                exit 1
            fi
            ;;
        "xcelium")
            if ! command -v xrun &> /dev/null; then
                print_msg $RED "Xcelium not found in PATH"
                exit 1
            fi
            ;;
        *)
            print_msg $RED "Unknown simulator: $sim"
            exit 1
            ;;
    esac
}

# Function to setup directories
setup_dirs() {
    mkdir -p "$OUTPUT_DIR"
    mkdir -p "$LOG_DIR"
    mkdir -p "$WORK_DIR"
    mkdir -p "$WAVE_DIR"
    mkdir -p "$COV_DIR"
    mkdir -p "$REPORT_DIR"
    print_msg $BLUE "Created output directories in: $OUTPUT_DIR"
}

# Function to compile the design
compile_design() {
    print_msg $YELLOW "Compiling AXI4 VIP design..."
    
    cd "$PROJECT_DIR"
    
    case $SIM in
        "vcs")
            local compile_cmd="vcs -sverilog -ntb_opts uvm-1.2 \
                +incdir+src +incdir+src/interfaces +incdir+src/sequences \
                +incdir+src/agents +incdir+src/testbench \
                -timescale=1ns/1ps \
                -debug_access+all -kdb +define+VCS \
                -o $WORK_DIR/simv"
            
            if [[ $COVERAGE -eq 1 ]]; then
                compile_cmd="$compile_cmd -cm line+cond+fsm+tgl+branch"
            fi
            
            compile_cmd="$compile_cmd \
                src/axi4_vip_pkg.sv \
                src/interfaces/axi4_if.sv \
                src/testbench/axi4_tb_top.sv"
            
            print_msg $BLUE "Running: $compile_cmd"
            eval $compile_cmd 2>&1 | tee "$LOG_DIR/compile.log"
            
            if [[ ${PIPESTATUS[0]} -ne 0 ]]; then
                print_msg $RED "Compilation failed! Check $LOG_DIR/compile.log"
                exit 1
            fi
            ;;
        "questa")
            make compile SIM=questa 2>&1 | tee "$LOG_DIR/compile.log"
            ;;
        "xcelium")
            make compile SIM=xcelium 2>&1 | tee "$LOG_DIR/compile.log"
            ;;
    esac
    
    print_msg $GREEN "Compilation successful"
}

# Function to run simulation
run_simulation() {
    print_msg $YELLOW "Running test: $TEST"
    
    cd "$PROJECT_DIR"
    
    local sim_args="+UVM_TESTNAME=$TEST +UVM_VERBOSITY=$VERBOSITY"
    
    if [[ -n "$SEED" ]]; then
        sim_args="$sim_args +ntb_random_seed=$SEED"
    fi
    
    if [[ $DUMP_WAVES -eq 1 ]]; then
        sim_args="$sim_args +DUMP_VCD"
    fi
    
    local log_file="$LOG_DIR/${TEST}_$(date +%Y%m%d_%H%M%S).log"
    
    case $SIM in
        "vcs")
            local run_cmd="$WORK_DIR/simv $sim_args -l $log_file"
            
            if [[ $COVERAGE -eq 1 ]]; then
                run_cmd="$run_cmd -cm line+cond+fsm+tgl+branch -cmdir $WORK_DIR/coverage.vdb"
            fi
            
            if [[ $GUI_MODE -eq 1 ]]; then
                run_cmd="$run_cmd -gui"
            fi
            
            print_msg $BLUE "Running: $run_cmd"
            timeout $TIMEOUT $run_cmd || handle_timeout $?
            ;;
        "questa")
            make run TEST=$TEST SIM=questa UVM_VERBOSITY=$VERBOSITY
            ;;
        "xcelium")
            make run TEST=$TEST SIM=xcelium UVM_VERBOSITY=$VERBOSITY
            ;;
    esac
    
    # Check results
    check_results "$log_file"
}

# Function to handle simulation timeout
handle_timeout() {
    local exit_code=$1
    if [[ $exit_code -eq 124 ]]; then
        print_msg $RED "Simulation timed out after $TIMEOUT"
        exit 1
    elif [[ $exit_code -ne 0 ]]; then
        print_msg $RED "Simulation failed with exit code: $exit_code"
        exit 1
    fi
}

# Function to check simulation results
check_results() {
    local log_file=$1
    
    if [[ -f "$log_file" ]]; then
        if grep -q "TEST.*PASSED" "$log_file"; then
            print_msg $GREEN "✓ Test PASSED: $TEST"
            return 0
        elif grep -q "TEST.*FAILED" "$log_file"; then
            print_msg $RED "✗ Test FAILED: $TEST"
            print_msg $YELLOW "Check log file: $log_file"
            return 1
        else
            print_msg $YELLOW "? Test result unclear for: $TEST"
            print_msg $YELLOW "Check log file: $log_file"
            return 1
        fi
    else
        print_msg $RED "Log file not found: $log_file"
        return 1
    fi
}

# Function to run regression tests
run_regression() {
    print_msg $YELLOW "Running AXI4 VIP Regression Suite"
    
    local tests=("axi4_basic_test" "axi4_comprehensive_test")
    local passed=0
    local failed=0
    local total=${#tests[@]}
    
    print_msg $BLUE "Regression tests to run: $total"
    
    for test in "${tests[@]}"; do
        print_msg $BLUE "Running regression test: $test"
        
        TEST=$test
        if run_simulation; then
            ((passed++))
            print_msg $GREEN "✓ $test PASSED"
        else
            ((failed++))
            print_msg $RED "✗ $test FAILED"
        fi
        
        print_msg $BLUE "Progress: $((passed + failed))/$total completed"
    done
    
    print_msg $YELLOW "=== REGRESSION SUMMARY ==="
    print_msg $GREEN "Passed: $passed/$total"
    print_msg $RED "Failed: $failed/$total"
    
    if [[ $failed -eq 0 ]]; then
        print_msg $GREEN "🎉 ALL REGRESSION TESTS PASSED!"
        return 0
    else
        print_msg $RED "❌ REGRESSION FAILED - $failed test(s) failed"
        return 1
    fi
}

# Function to generate coverage report
generate_coverage_report() {
    if [[ $COVERAGE -eq 1 ]]; then
        print_msg $YELLOW "Generating coverage report..."
        
        case $SIM in
            "vcs")
                if [[ -d "$WORK_DIR/simv.vdb" ]]; then
                    urg -dir "$WORK_DIR/simv.vdb" -report both -reportdir "$COV_DIR/vcs_coverage" \
                        2>&1 | tee "$LOG_DIR/coverage_gen.log"
                    
                    if [[ $? -eq 0 ]]; then
                        print_msg $GREEN "VCS coverage report generated in: $COV_DIR/vcs_coverage"
                    else
                        print_msg $RED "VCS coverage report generation failed"
                    fi
                else
                    print_msg $YELLOW "No VCS coverage database found"
                fi
                ;;
            "questa")
                if [[ -f "$WORK_DIR/coverage.ucdb" ]]; then
                    vcover report -html "$WORK_DIR/coverage.ucdb" -htmldir "$COV_DIR/questa_coverage" \
                        2>&1 | tee "$LOG_DIR/coverage_gen.log"
                    
                    if [[ $? -eq 0 ]]; then
                        print_msg $GREEN "Questa coverage report generated in: $COV_DIR/questa_coverage"
                    else
                        print_msg $RED "Questa coverage report generation failed"
                    fi
                else
                    print_msg $YELLOW "No Questa coverage database found"
                fi
                ;;
            *)
                print_msg $YELLOW "Coverage reporting not configured for $SIM"
                ;;
        esac
    fi
}

# Function to clean build artifacts
clean_build() {
    print_msg $YELLOW "Cleaning build artifacts..."
    
    cd "$PROJECT_DIR"
    rm -rf "$OUTPUT_DIR"
    rm -rf simv* csrc DVEfiles ucli.key vc_hdrs.h inter.vpd
    rm -rf transcript modelsim.ini .simvision/ INCA_libs/ xcelium.d/
    rm -rf *.log *.vcd *.fsdb *.shm
    
    print_msg $GREEN "Clean completed - removed $OUTPUT_DIR and temporary files"
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -t|--test)
            TEST="$2"
            shift 2
            ;;
        -s|--sim)
            SIM="$2"
            shift 2
            ;;
        -v|--verbosity)
            VERBOSITY="$2"
            shift 2
            ;;
        -g|--gui)
            GUI_MODE=1
            shift
            ;;
        -c|--coverage)
            COVERAGE=1
            shift
            ;;
        -w|--waves)
            DUMP_WAVES=1
            shift
            ;;
        -r|--seed)
            SEED="$2"
            shift 2
            ;;
        --timeout)
            TIMEOUT="$2"
            shift 2
            ;;
        --clean)
            clean_build
            exit 0
            ;;
        --regression)
            compile_design
            run_regression
            exit $?
            ;;
        -h|--help)
            show_usage
            exit 0
            ;;
        *)
            print_msg $RED "Unknown option: $1"
            show_usage
            exit 1
            ;;
    esac
done

# Main execution
main() {
    print_msg $BLUE "AXI4 VIP Simulation Started"
    print_msg $BLUE "Configuration:"
    print_msg $BLUE "  Simulator: $SIM"
    print_msg $BLUE "  Test: $TEST"
    print_msg $BLUE "  Verbosity: $VERBOSITY"
    print_msg $BLUE "  GUI Mode: $([[ $GUI_MODE -eq 1 ]] && echo "YES" || echo "NO")"
    print_msg $BLUE "  Coverage: $([[ $COVERAGE -eq 1 ]] && echo "YES" || echo "NO")"
    print_msg $BLUE "  Waves: $([[ $DUMP_WAVES -eq 1 ]] && echo "YES" || echo "NO")"
    if [[ -n "$SEED" ]]; then
        print_msg $BLUE "  Seed: $SEED"
    fi
    
    # Check prerequisites
    check_simulator "$SIM"
    setup_dirs
    
    # Compile and run
    compile_design
    run_simulation
    
    # Generate reports
    generate_coverage_report
    
    print_msg $GREEN "AXI4 VIP Simulation Completed Successfully"
}

# Run main function
main