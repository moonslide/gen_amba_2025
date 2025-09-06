# AXI4 VIP Simulation Makefile
# Auto-generated

# Simulator
SIM = vcs

# UVM-1.2 home
UVM_HOME = ${VCS_HOME}/etc/uvm-1.2

# Compile options
COMP_OPTS = -sverilog +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm.sv
COMP_OPTS += +define+UVM_NO_DPI -ntb_opts uvm-1.2

# Simulation options
SIM_OPTS = +UVM_TESTNAME=axi4_base_test +UVM_VERBOSITY=UVM_MEDIUM

# Targets
compile:
	$(SIM) $(COMP_OPTS) -f filelist.f

run:
	./simv $(SIM_OPTS)

clean:
	rm -rf csrc simv* *.log *.vpd ucli.key

.PHONY: compile run clean
