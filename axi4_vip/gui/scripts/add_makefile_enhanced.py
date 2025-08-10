#!/usr/bin/env python3
"""
Add Makefile.enhanced generation to match 16x16_vip reference
Creates the enhanced Makefile variant with additional debug features
"""

import os
import sys
from datetime import datetime

def add_makefile_enhanced_generation():
    """Add generation of Makefile.enhanced to match 16x16_vip"""
    
    script_dir = os.path.dirname(os.path.abspath(__file__))
    src_dir = os.path.join(script_dir, "..", "src")
    generator_file = os.path.join(src_dir, "vip_environment_generator.py")
    
    if not os.path.exists(generator_file):
        print(f"Error: Cannot find {generator_file}")
        return False
    
    # Read the file
    with open(generator_file, 'r') as f:
        lines = f.readlines()
    
    # Find where to add the Makefile.enhanced generation
    # Look for the _create_vip_rtl_makefile method
    for i, line in enumerate(lines):
        if 'def _create_vip_rtl_makefile(self, env_path, timestamp):' in line:
            # Find the end of this method where we write the makefile
            for j in range(i, min(i + 200, len(lines))):
                if 'with open(makefile_path, \'w\') as f:' in lines[j]:
                    # Find the line after writing the makefile
                    for k in range(j, min(j + 10, len(lines))):
                        if 'f.write(makefile_content)' in lines[k]:
                            # Insert code to also create Makefile.enhanced
                            indent = '        '  # 8 spaces
                            enhanced_code = f'''
{indent}
{indent}# Also create Makefile.enhanced with additional features
{indent}self._create_makefile_enhanced(sim_dir, timestamp)
'''
                            lines.insert(k + 1, enhanced_code)
                            break
                    break
            break
    
    # Add the method to create Makefile.enhanced at the end of the class
    enhanced_method = '''
    def _create_makefile_enhanced(self, sim_dir, timestamp):
        """Create enhanced Makefile matching 16x16_vip Makefile.enhanced"""
        makefile_enhanced_path = os.path.join(sim_dir, "Makefile.enhanced")
        
        makefile_enhanced_content = f"""#==============================================================================
# Enhanced Makefile for AXI4 VIP Simulation
# Extended version with additional debug and analysis features
# Date: {timestamp}
#==============================================================================

# Default simulator
SIM ?= vcs

# Test name
TEST ?= axi4_base_test

# Random seed
SEED ?= 1

# Verbosity level (UVM_NONE, UVM_LOW, UVM_MEDIUM, UVM_HIGH, UVM_FULL, UVM_DEBUG)
VERBOSITY ?= UVM_MEDIUM

# Directories
VIP_ROOT = ..
SIM_DIR = .
SCRIPT_DIR = $(SIM_DIR)/scripts
LOG_DIR = $(SIM_DIR)/logs
WAVE_DIR = $(SIM_DIR)/waves
COV_DIR = $(SIM_DIR)/coverage
REPORT_DIR = $(SIM_DIR)/reports

# Export VIP_ROOT for use in compile file
export VIP_ROOT

# Create directories
$(shell mkdir -p $(LOG_DIR) $(WAVE_DIR) $(COV_DIR) $(REPORT_DIR) $(SCRIPT_DIR))

# Common compile options
COMMON_OPTS = +define+UVM_NO_DEPRECATED +define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR

# Debug options
DEBUG_LEVEL ?= 0
ifeq ($(DEBUG_LEVEL), 1)
    COMMON_OPTS += +define+AXI4_DEBUG_BASIC
else ifeq ($(DEBUG_LEVEL), 2)
    COMMON_OPTS += +define+AXI4_DEBUG_BASIC +define+AXI4_DEBUG_TRANSACTION
else ifeq ($(DEBUG_LEVEL), 3)
    COMMON_OPTS += +define+AXI4_DEBUG_BASIC +define+AXI4_DEBUG_TRANSACTION +define+AXI4_DEBUG_PROTOCOL
else ifeq ($(DEBUG_LEVEL), 4)
    COMMON_OPTS += +define+AXI4_DEBUG_BASIC +define+AXI4_DEBUG_TRANSACTION +define+AXI4_DEBUG_PROTOCOL +define+AXI4_DEBUG_SCOREBOARD
endif

# Performance monitoring
PERF_MONITOR ?= 0
ifeq ($(PERF_MONITOR), 1)
    COMMON_OPTS += +define+AXI4_PERF_MONITOR
endif

# Coverage options
COVERAGE ?= 0
ifeq ($(COVERAGE), 1)
    COMMON_OPTS += +define+AXI4_ENABLE_COVERAGE
    VCS_COMP_OPTS += -cm line+cond+fsm+tgl+branch+assert
    VCS_RUN_OPTS += -cm line+cond+fsm+tgl+branch+assert -cm_name $(TEST)_$(SEED)
endif

# Waveform dump options
DUMP_FSDB ?= 0
DUMP_VCD ?= 0
FSDB_FILE ?= $(WAVE_DIR)/$(TEST)_$(SEED).fsdb
VCD_FILE ?= $(WAVE_DIR)/$(TEST)_$(SEED).vcd

# Add waveform defines
ifeq ($(DUMP_FSDB), 1)
    COMMON_OPTS += +define+DUMP_FSDB
    VERDI_HOME ?= /home/eda_tools/synopsys/verdi/W-2024.09-SP1
    VCS_COMP_OPTS += -P $(VERDI_HOME)/share/PLI/VCS/LINUX64/novas.tab $(VERDI_HOME)/share/PLI/VCS/LINUX64/pli.a
endif

ifeq ($(DUMP_VCD), 1)
    COMMON_OPTS += +define+DUMP_VCD
endif

# VCS options
VCS_COMP_OPTS = -full64 -sverilog -ntb_opts uvm-1.2 -timescale=1ns/1ps
VCS_COMP_OPTS += -debug_access+all +vcs+lic+wait -lca -kdb
VCS_COMP_OPTS += +lint=PCWM +lint=TFIPC-L
VCS_COMP_OPTS += $(COMMON_OPTS)

# Enhanced runtime options
VCS_RUN_OPTS = +UVM_TESTNAME=$(TEST) +UVM_VERBOSITY=$(VERBOSITY)
VCS_RUN_OPTS += +ntb_random_seed=$(SEED)

# UVM specific debug options
UVM_DEBUG ?= 0
ifeq ($(UVM_DEBUG), 1)
    VCS_RUN_OPTS += +UVM_CONFIG_DB_TRACE +UVM_OBJECTION_TRACE
    VCS_RUN_OPTS += +UVM_PHASE_TRACE +UVM_RESOURCE_DB_TRACE
endif

# Transaction recording
TRANS_RECORD ?= 0
ifeq ($(TRANS_RECORD), 1)
    VCS_RUN_OPTS += +UVM_TR_RECORD +UVM_LOG_RECORD
endif

# Timeout settings
TIMEOUT ?= 1000000
VCS_RUN_OPTS += +UVM_TIMEOUT=$(TIMEOUT),NO

# Maximum error count
MAX_ERRORS ?= 10
VCS_RUN_OPTS += +UVM_MAX_QUIT_COUNT=$(MAX_ERRORS),NO

# Add FSDB runtime options
ifeq ($(DUMP_FSDB), 1)
    VCS_RUN_OPTS += +fsdb_file=$(FSDB_FILE)
endif

# Targets
.PHONY: all compile run clean help debug_info

all: run

compile:
\\t@echo "======================================"
\\t@echo "Enhanced Compilation Mode"
\\t@echo "======================================"
\\t@echo "Debug Level: $(DEBUG_LEVEL)"
\\t@echo "Coverage: $(COVERAGE)"
\\t@echo "Performance Monitor: $(PERF_MONITOR)"
\\tVIP_ROOT=$(VIP_ROOT) vcs $(VCS_COMP_OPTS) -f $(VIP_ROOT)/sim/axi4_compile.f -l $(LOG_DIR)/compile.log
\\t@echo "✅ Compilation successful!"

run: compile
\\t@echo "======================================"
\\t@echo "Running Enhanced Test Mode"
\\t@echo "======================================"
\\t@echo "Test: $(TEST)"
\\t@echo "Seed: $(SEED)"
\\t@echo "Verbosity: $(VERBOSITY)"
\\t@echo "UVM Debug: $(UVM_DEBUG)"
\\t@echo "Transaction Recording: $(TRANS_RECORD)"
\\t@echo "Timeout: $(TIMEOUT)"
\\t./simv $(VCS_RUN_OPTS) -l $(LOG_DIR)/$(TEST)_$(SEED).log | tee $(LOG_DIR)/$(TEST)_$(SEED)_console.log
\\t@echo "✅ Simulation completed!"
\\t@echo "Log file: $(LOG_DIR)/$(TEST)_$(SEED).log"

# Debug runs with different levels
debug_basic:
\\t$(MAKE) run DEBUG_LEVEL=1 VERBOSITY=UVM_HIGH

debug_trans:
\\t$(MAKE) run DEBUG_LEVEL=2 VERBOSITY=UVM_HIGH TRANS_RECORD=1

debug_protocol:
\\t$(MAKE) run DEBUG_LEVEL=3 VERBOSITY=UVM_HIGH UVM_DEBUG=1

debug_full:
\\t$(MAKE) run DEBUG_LEVEL=4 VERBOSITY=UVM_FULL UVM_DEBUG=1 TRANS_RECORD=1

# Run with performance monitoring
run_perf:
\\t$(MAKE) run PERF_MONITOR=1
\\t@echo "Performance metrics logged in simulation output"

# Run with coverage
run_cov:
\\t$(MAKE) run COVERAGE=1
\\t@echo "Coverage database: simv.vdb"

# Run with FSDB dumping
run_fsdb: 
\\t$(MAKE) run DUMP_FSDB=1
\\t@echo "✅ FSDB file generated: $(FSDB_FILE)"

# Run with VCD dumping
run_vcd:
\\t$(MAKE) run DUMP_VCD=1
\\t@echo "✅ VCD file generated: $(VCD_FILE)"

# Run all tests
run_all:
\\t@for test in axi4_basic_rw_test axi4_burst_test axi4_stress_test axi4_random_test; do \\\\
\\t\\techo "Running $$test..."; \\\\
\\t\\t$(MAKE) run TEST=$$test; \\\\
\\tdone

# Generate coverage report
cov_report:
\\turg -dir simv.vdb -format html -report $(REPORT_DIR)/coverage.html

# Open Verdi for waveform viewing
verdi:
\\tverdi -ssf $(FSDB_FILE) -f $(VIP_ROOT)/sim/axi4_compile.f &

# Clean all generated files
clean:
\\trm -rf simv* csrc *.log *.key DVEfiles
\\trm -rf $(LOG_DIR)/* $(WAVE_DIR)/* $(COV_DIR)/* $(REPORT_DIR)/*
\\trm -rf ucli.key vc_hdrs.h .inter.vpd.uvm verdiLog novas*
\\trm -rf work.lib++ *.daidir

# Display help
help:
\\t@echo "Enhanced Makefile for AXI4 VIP Simulation"
\\t@echo "========================================="
\\t@echo ""
\\t@echo "Basic targets:"
\\t@echo "  compile          - Compile the design"
\\t@echo "  run              - Run simulation"
\\t@echo "  clean            - Clean generated files"
\\t@echo ""
\\t@echo "Debug targets:"
\\t@echo "  debug_basic      - Run with basic debug (level 1)"
\\t@echo "  debug_trans      - Run with transaction debug (level 2)"
\\t@echo "  debug_protocol   - Run with protocol debug (level 3)"
\\t@echo "  debug_full       - Run with full debug (level 4)"
\\t@echo ""
\\t@echo "Analysis targets:"
\\t@echo "  run_perf         - Run with performance monitoring"
\\t@echo "  run_cov          - Run with coverage collection"
\\t@echo "  cov_report       - Generate coverage report"
\\t@echo ""
\\t@echo "Waveform targets:"
\\t@echo "  run_fsdb         - Run with FSDB dumping"
\\t@echo "  run_vcd          - Run with VCD dumping"
\\t@echo "  verdi            - Open Verdi viewer"
\\t@echo ""
\\t@echo "Options:"
\\t@echo "  TEST=<name>      - Test to run (default: axi4_base_test)"
\\t@echo "  SEED=<value>     - Random seed (default: 1)"
\\t@echo "  VERBOSITY=<level>- UVM verbosity level"
\\t@echo "  DEBUG_LEVEL=<n>  - Debug level (0-4)"
\\t@echo "  COVERAGE=1       - Enable coverage"
\\t@echo "  PERF_MONITOR=1   - Enable performance monitoring"
\\t@echo "  UVM_DEBUG=1      - Enable UVM debug features"
\\t@echo "  TRANS_RECORD=1   - Enable transaction recording"
\\t@echo "  TIMEOUT=<value>  - Simulation timeout"
\\t@echo "  MAX_ERRORS=<n>   - Maximum error count"

# Display current configuration
debug_info:
\\t@echo "Current Configuration:"
\\t@echo "  TEST = $(TEST)"
\\t@echo "  SEED = $(SEED)"
\\t@echo "  VERBOSITY = $(VERBOSITY)"
\\t@echo "  DEBUG_LEVEL = $(DEBUG_LEVEL)"
\\t@echo "  COVERAGE = $(COVERAGE)"
\\t@echo "  PERF_MONITOR = $(PERF_MONITOR)"
\\t@echo "  UVM_DEBUG = $(UVM_DEBUG)"
\\t@echo "  TRANS_RECORD = $(TRANS_RECORD)"
\\t@echo "  DUMP_FSDB = $(DUMP_FSDB)"
\\t@echo "  DUMP_VCD = $(DUMP_VCD)"
"""
        
        with open(makefile_enhanced_path, 'w') as f:
            f.write(makefile_enhanced_content)
        
        print(f"Created Makefile.enhanced at {makefile_enhanced_path}")
'''
    
    # Find the end of the class to add the method
    class_end = -1
    for i in range(len(lines) - 1, 0, -1):
        if lines[i].startswith('class VIPEnvironmentGenerator'):
            # Find the end of this class
            indent_level = 0
            for j in range(i + 1, len(lines)):
                if lines[j].startswith('class ') and not lines[j].startswith('    '):
                    class_end = j
                    break
            break
    
    if class_end > 0:
        lines.insert(class_end, enhanced_method + '\n')
        print("✓ Added _create_makefile_enhanced method")
    
    # Write back the modified content
    with open(generator_file, 'w') as f:
        f.writelines(lines)
    
    print("✅ Successfully added Makefile.enhanced generation")
    return True

if __name__ == "__main__":
    print("=== Add Makefile.enhanced Generation ===")
    print("This adds generation of Makefile.enhanced to match 16x16_vip\n")
    
    if add_makefile_enhanced_generation():
        print("\n✅ Makefile.enhanced generation added successfully!")
        print("The VIP generator will now create both Makefile and Makefile.enhanced")
    else:
        print("\n❌ Failed to add Makefile.enhanced generation")
        sys.exit(1)