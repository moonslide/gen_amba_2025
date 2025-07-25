#==============================================================================
# AXI4 VIP Simulation Makefile
# Supports multiple simulators: VCS, Questa, Xcelium
#==============================================================================

# Default simulator
SIM ?= vcs

# Test selection
TEST ?= axi4_basic_test
TESTNAME ?= $(TEST)

# Configuration file (optional)
CONFIG_FILE ?=

# VIP mode and RTL path
VIP_MODE ?= BEHAVIORAL
RTL_PATH ?= none

# Simulation directories
SRC_DIR = src
TB_DIR = $(SRC_DIR)/testbench
AGENTS_DIR = $(SRC_DIR)/agents
SEQ_DIR = $(SRC_DIR)/sequences
IF_DIR = $(SRC_DIR)/interfaces
OUTPUT_DIR = output
WORK_DIR = $(OUTPUT_DIR)/work
LOG_DIR = $(OUTPUT_DIR)/logs
WAVE_DIR = $(OUTPUT_DIR)/waves
COV_DIR = $(OUTPUT_DIR)/coverage
REPORT_DIR = $(OUTPUT_DIR)/reports

# Create directories
$(shell mkdir -p $(OUTPUT_DIR) $(WORK_DIR) $(LOG_DIR) $(WAVE_DIR) $(COV_DIR) $(REPORT_DIR))

# Source files
INTERFACE_FILES = $(IF_DIR)/axi4_if.sv

SEQUENCE_FILES = $(SEQ_DIR)/axi4_transaction.sv \
                $(SEQ_DIR)/axi4_sequences.sv

AGENT_FILES = $(AGENTS_DIR)/axi4_master_driver.sv \
              $(AGENTS_DIR)/axi4_slave_driver.sv \
              $(AGENTS_DIR)/axi4_monitor.sv \
              $(AGENTS_DIR)/axi4_master_agent.sv

TESTBENCH_FILES = $(TB_DIR)/axi4_scoreboard.sv \
                  $(TB_DIR)/axi4_test_env.sv \
                  $(TB_DIR)/axi4_rtl_wrapper.sv \
                  $(TB_DIR)/axi4_tb_top.sv

CONFIG_FILES = $(SRC_DIR)/config/axi4_config_reader.sv

PACKAGE_FILE = $(SRC_DIR)/axi4_vip_pkg.sv

ALL_FILES = $(PACKAGE_FILE) $(INTERFACE_FILES) $(CONFIG_FILES) $(SEQUENCE_FILES) $(AGENT_FILES) $(TESTBENCH_FILES)

# UVM Library
UVM_HOME ?= $(QUESTA_HOME)/verilog_src/uvm-1.2
UVM_VERBOSITY ?= UVM_MEDIUM

# Common compile arguments
COMMON_ARGS = +incdir+$(UVM_HOME)/src \
              +incdir+$(SRC_DIR) \
              +incdir+$(IF_DIR) \
              +incdir+$(SEQ_DIR) \
              +incdir+$(AGENTS_DIR) \
              +incdir+$(TB_DIR) \
              +incdir+$(SRC_DIR)/config \
              -timescale=1ns/1ps

# Runtime arguments
BASE_RUN_ARGS = +UVM_TESTNAME=$(TESTNAME) \
                +UVM_VERBOSITY=$(UVM_VERBOSITY)

# Add CONFIG_FILE if specified
ifneq ($(CONFIG_FILE),)
    CONFIG_ARGS = +CONFIG_FILE=$(CONFIG_FILE)
else
    CONFIG_ARGS =
endif

# Add VIP mode and RTL path
CONFIG_ARGS += +VIP_MODE=$(VIP_MODE)
ifneq ($(RTL_PATH),none)
    CONFIG_ARGS += +RTL_PATH=$(RTL_PATH)
endif

FULL_RUN_ARGS = $(BASE_RUN_ARGS) $(CONFIG_ARGS)

# Simulator specific settings
ifeq ($(SIM),questa)
    VLIB = vlib
    VMAP = vmap
    VLOG = vlog
    VSIM = vsim
    COMPILE_ARGS = $(COMMON_ARGS) -sv -work $(WORK_DIR) +define+QUESTA
    RUN_ARGS = -work $(WORK_DIR) -c -do "run -all; quit -f" \
               $(FULL_RUN_ARGS) \
               -l $(LOG_DIR)/$(TESTNAME).log \
               -wlf $(WAVE_DIR)/$(TESTNAME).wlf
    GUI_ARGS = -work $(WORK_DIR) -gui -do "add wave -r /*; run -all" \
               $(FULL_RUN_ARGS) \
               -l $(LOG_DIR)/$(TESTNAME)_gui.log \
               -wlf $(WAVE_DIR)/$(TESTNAME)_gui.wlf
endif

ifeq ($(SIM),vcs)
    VLOG = vcs
    COMPILE_ARGS = $(COMMON_ARGS) -sverilog -ntb_opts uvm-1.2 \
                   -debug_access+all -kdb +define+VCS \
                   -o $(WORK_DIR)/simv
    RUN_ARGS = $(FULL_RUN_ARGS) \
               -l $(LOG_DIR)/$(TESTNAME).log \
               +vcs+dumpvars+$(WAVE_DIR)/$(TESTNAME).vcd
    GUI_ARGS = -gui $(FULL_RUN_ARGS) \
               -l $(LOG_DIR)/$(TESTNAME)_gui.log \
               +vcs+dumpvars+$(WAVE_DIR)/$(TESTNAME)_gui.vcd
endif

ifeq ($(SIM),xcelium)
    VLOG = xrun
    COMPILE_ARGS = $(COMMON_ARGS) -sv -uvm -access +rwc +define+XCELIUM \
                   -xmlibdirpath $(WORK_DIR)
    RUN_ARGS = $(FULL_RUN_ARGS) \
               -l $(LOG_DIR)/$(TESTNAME).log \
               +xceliumncdumpvars+$(WAVE_DIR)/$(TESTNAME).shm
    GUI_ARGS = -gui $(FULL_RUN_ARGS) \
               -l $(LOG_DIR)/$(TESTNAME)_gui.log \
               +xceliumncdumpvars+$(WAVE_DIR)/$(TESTNAME)_gui.shm
endif

# Default target
all: compile

# Help target
help:
	@echo "AXI4 VIP Simulation Makefile"
	@echo "============================"
	@echo ""
	@echo "Usage: make [target] [options]"
	@echo ""
	@echo "Targets:"
	@echo "  help         Show this help message"
	@echo "  compile      Compile the design and testbench"
	@echo "  run          Run simulation with specified test"
	@echo "  gui          Run simulation with GUI"
	@echo "  regression   Run all tests in regression mode" 
	@echo "  clean        Clean build artifacts"
	@echo "  view_waves   View waveforms (Questa only)"
	@echo ""
	@echo "Options:"
	@echo "  SIM=<simulator>    Simulator choice (questa, vcs, xcelium)"
	@echo "  TEST=<testname>    Test to run (default: axi4_basic_test)"
	@echo "  UVM_VERBOSITY=<level>  UVM verbosity (UVM_LOW, UVM_MEDIUM, UVM_HIGH)"
	@echo "  CONFIG_FILE=<path>     Path to JSON configuration file"
	@echo "  VIP_MODE=<mode>        VIP mode (BEHAVIORAL or RTL)"
	@echo "  RTL_PATH=<path>        Path to generated RTL (when VIP_MODE=RTL)"
	@echo ""
	@echo "Available Tests:"
	@echo "  axi4_basic_test           Basic functionality test"
	@echo "  axi4_comprehensive_test   Complete protocol test suite"
	@echo ""
	@echo "Examples:"
	@echo "  make compile SIM=questa"
	@echo "  make run TEST=axi4_basic_test"
	@echo "  make gui TEST=axi4_comprehensive_test SIM=vcs"
	@echo "  make run TEST=axi4_basic_test CONFIG_FILE=output/configs/axi4_config.json"
	@echo "  make run TEST=axi4_basic_test VIP_MODE=RTL RTL_PATH=output/rtl/axi4_interconnect.v"
	@echo "  make regression"

# Compile target
compile: setup
ifeq ($(SIM),questa)
	$(VLIB) $(WORK_DIR)
	$(VLOG) $(COMPILE_ARGS) $(ALL_FILES)
else ifeq ($(SIM),vcs)
	$(VLOG) $(COMPILE_ARGS) -o $(WORK_DIR)/simv $(ALL_FILES)
else ifeq ($(SIM),xcelium)
	$(VLOG) $(COMPILE_ARGS) $(ALL_FILES) -elaborate
endif
	@echo "Compilation completed for $(SIM)"

# Run simulation
run: compile
	@echo "Running test: $(TESTNAME) on $(SIM)"
ifeq ($(SIM),questa)
	$(VSIM) $(RUN_ARGS) axi4_tb_top
else ifeq ($(SIM),vcs)
	$(WORK_DIR)/simv $(RUN_ARGS)
else ifeq ($(SIM),xcelium)
	$(VLOG) $(RUN_ARGS) $(TESTNAME)
endif
	@echo "Simulation completed. Check $(LOG_DIR)/$(TESTNAME).log for results"

# Run with GUI
gui: compile
	@echo "Running test: $(TESTNAME) with GUI on $(SIM)"
ifeq ($(SIM),questa)
	$(VSIM) $(GUI_ARGS) axi4_tb_top
else ifeq ($(SIM),vcs)
	$(WORK_DIR)/simv $(GUI_ARGS)
else ifeq ($(SIM),xcelium)
	$(VLOG) $(GUI_ARGS) $(TESTNAME)
endif

# Regression testing
regression: compile
	@echo "Running regression tests..."
	@$(MAKE) run TEST=axi4_basic_test
	@$(MAKE) run TEST=axi4_comprehensive_test
	@echo "Regression completed. Check logs in $(LOG_DIR)/"
	@grep -r "TEST.*PASSED\|TEST.*FAILED" $(LOG_DIR)/ || true

# Setup directories and environment
setup:
	@echo "Setting up AXI4 VIP simulation environment..."
	@echo "Simulator: $(SIM)"
	@echo "Test: $(TESTNAME)"
	@echo "UVM Verbosity: $(UVM_VERBOSITY)"
	@echo "Output Directory: $(OUTPUT_DIR)"
	@echo "Working Directory: $(WORK_DIR)"
	@mkdir -p $(OUTPUT_DIR) $(WORK_DIR) $(LOG_DIR) $(WAVE_DIR) $(COV_DIR) $(REPORT_DIR)

# View waveforms
view_waves:
	@echo "Opening waveform viewer..."
ifeq ($(SIM),questa)
	@WLFS=$$(find $(WAVE_DIR) -name "*.wlf" -type f 2>/dev/null | head -1); \
	if [ -n "$$WLFS" ]; then \
		echo "Opening $$WLFS"; \
		vsim -view "$$WLFS"; \
	else \
		echo "No Questa waveform files found in $(WAVE_DIR)/"; \
	fi
else ifeq ($(SIM),vcs)
	@VCDS=$$(find $(WAVE_DIR) -name "*.vcd" -type f 2>/dev/null | head -1); \
	if [ -n "$$VCDS" ]; then \
		echo "Opening $$VCDS with DVE"; \
		dve -vpd "$$VCDS" &; \
	else \
		echo "No VCS waveform files found in $(WAVE_DIR)/"; \
	fi
else ifeq ($(SIM),xcelium)
	@SHMS=$$(find $(WAVE_DIR) -name "*.shm" -type d 2>/dev/null | head -1); \
	if [ -n "$$SHMS" ]; then \
		echo "Opening $$SHMS with SimVision"; \
		simvision "$$SHMS" &; \
	else \
		echo "No Xcelium waveform files found in $(WAVE_DIR)/"; \
	fi
endif

# Coverage report
coverage:
	@echo "Generating coverage report..."
ifeq ($(SIM),questa)
	@if [ -f $(WORK_DIR)/coverage.ucdb ]; then \
		vcover report -html $(WORK_DIR)/coverage.ucdb -htmldir $(COV_DIR)/coverage_html; \
		echo "Coverage report generated in $(COV_DIR)/coverage_html/"; \
	else \
		echo "No coverage database found. Run with coverage enabled."; \
	fi
else ifeq ($(SIM),vcs)
	@if [ -d $(WORK_DIR)/simv.vdb ]; then \
		urg -dir $(WORK_DIR)/simv.vdb -report both -reportdir $(COV_DIR)/vcs_coverage; \
		echo "Coverage report generated in $(COV_DIR)/vcs_coverage/"; \
	else \
		echo "No VCS coverage database found. Run with coverage enabled."; \
	fi
else
	@echo "Coverage reporting available for Questa and VCS."
endif

# Lint checking
lint:
	@echo "Running lint checks..."
	@echo "Creating lint report..."
	@# This would typically run a linting tool like Spyglass or Lint
	@echo "Lint checking would be integrated here with tools like:"
	@echo "  - Synopsys Spyglass"
	@echo "  - Cadence Lint"
	@echo "  - Mentor Precision Synthesis"

# Debug target
debug: compile
	@echo "Starting debug session..."
ifeq ($(SIM),questa)
	$(VSIM) -work $(WORK_DIR) -gui -debugDB \
		+UVM_TESTNAME=$(TESTNAME) \
		+UVM_VERBOSITY=UVM_HIGH \
		-do "add wave -r /*; run 100us" \
		axi4_tb_top
endif

# Performance analysis
perf: compile
	@echo "Running performance analysis..."
	@$(MAKE) run TEST=axi4_stress_test UVM_VERBOSITY=UVM_LOW
	@echo "Performance analysis completed. Check logs for timing metrics."

# Clean build artifacts
clean:
	@echo "Cleaning build artifacts..."
	rm -rf $(OUTPUT_DIR)
	rm -rf transcript
	rm -rf modelsim.ini
	rm -rf ucli.key
	rm -rf vc_hdrs.h
	rm -rf simv*
	rm -rf csrc
	rm -rf DVEfiles
	rm -rf inter.vpd
	rm -rf *.log
	rm -rf *.vcd
	rm -rf *.fsdb
	rm -rf *.shm
	rm -rf xcelium.d
	rm -rf .simvision/
	rm -rf INCA_libs/
	@echo "Clean completed - removed $(OUTPUT_DIR) and temporary files"

# Install dependencies (example for common setups)
install_deps:
	@echo "Checking simulation tool dependencies..."
	@echo "Required tools:"
	@echo "  - SystemVerilog simulator (Questa/VCS/Xcelium)"
	@echo "  - UVM library (typically included with simulator)"
	@echo "  - Make utility"
	@echo ""
	@echo "Environment variables to set:"
	@echo "  QUESTA_HOME, VCS_HOME, or XCELIUM_HOME"
	@echo "  PATH should include simulator binaries"

# Quick test target
quick: 
	$(MAKE) run TEST=axi4_basic_test UVM_VERBOSITY=UVM_LOW

# Comprehensive test
full:
	$(MAKE) run TEST=axi4_comprehensive_test UVM_VERBOSITY=UVM_MEDIUM

# Print file list (useful for debugging makefile)
files:
	@echo "Source files to be compiled:"
	@echo "$(ALL_FILES)" | tr ' ' '\n'

# Simulator version check
version:
	@echo "Checking simulator versions..."
ifeq ($(SIM),questa)
	@vsim -version || echo "Questa not found"
endif
ifeq ($(SIM),vcs)
	@vcs -help | head -1 || echo "VCS not found"
endif
ifeq ($(SIM),xcelium)
	@xrun -version || echo "Xcelium not found"
endif

.PHONY: help compile run gui regression setup view_waves coverage lint debug perf clean install_deps quick full files version

# Default simulator check
check_sim:
	@echo "Using simulator: $(SIM)"
	@command -v $(VLOG) >/dev/null 2>&1 || { echo "$(SIM) not found in PATH"; exit 1; }