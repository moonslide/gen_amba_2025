#!/usr/bin/env python3
"""
RTL and VIP Generator Backend
Generates Verilog RTL and UVM VIP based on bus configuration
"""

import os
import subprocess
from pathlib import Path
from typing import Tuple, List
from bus_config import Project

class Generator:
    """Backend generator for RTL and VIP"""
    
    def __init__(self, project: Project):
        self.project = project
        self.output_dir = "output"
        
        # Get project root directory (gen_amba_2025) - use absolute path
        self.project_root = Path(__file__).resolve().parent.parent.parent.parent
        
    def generate_rtl(self, output_file: str = None) -> Tuple[bool, str]:
        """
        Generate RTL Verilog using gen_amba_axi
        Returns (success, message)
        """
        try:
            # Default output file
            if not output_file:
                os.makedirs(self.output_dir, exist_ok=True)
                num_masters = len(self.project.masters)
                num_slaves = len(self.project.slaves)
                output_file = f"{self.output_dir}/axi_m{num_masters}s{num_slaves}.v"
            
            # Build command
            cmd = [
                str(self.project_root / "gen_amba_axi" / "gen_amba_axi"),
                f"--master={len(self.project.masters)}",
                f"--slave={len(self.project.slaves)}",
                f"--output={output_file}"
            ]
            
            # Add bus configuration
            if self.project.bus.addr_width != 32:
                cmd.append(f"--addr-width={self.project.bus.addr_width}")
            
            if self.project.bus.data_width != 64:
                cmd.append(f"--data-width={self.project.bus.data_width}")
            
            if self.project.bus.id_width != 4:
                cmd.append(f"--id-width={self.project.bus.id_width}")
            
            # Add QoS if enabled
            if self.project.bus.qos:
                cmd.append("--qos")
            
            # Run generator (compatible with older Python)
            # Note: gen_amba_axi creates files relative to cwd
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, 
                                  universal_newlines=True, cwd=str(self.project_root))
            
            if result.returncode == 0:
                # Success - file is created relative to project_root
                full_output_path = self.project_root / output_file
                if full_output_path.exists():
                    size_kb = full_output_path.stat().st_size // 1024
                else:
                    # Try in current directory as fallback
                    size_kb = os.path.getsize(output_file) // 1024 if os.path.exists(output_file) else 0
                message = f"RTL generated successfully!\n"
                message += f"File: {output_file}\n"
                message += f"Size: {size_kb} KB\n"
                message += f"Configuration: {len(self.project.masters)}M × {len(self.project.slaves)}S\n"
                message += f"Width: {self.project.bus.data_width}-bit data, {self.project.bus.addr_width}-bit address"
                
                if self.project.bus.qos:
                    message += "\nQoS: Enabled"
                if self.project.bus.arbitration == "fixed":
                    message += "\nArbitration: Fixed Priority"
                elif self.project.bus.arbitration == "rr":
                    message += "\nArbitration: Round Robin"
                elif self.project.bus.arbitration == "qos":
                    message += "\nArbitration: QoS-based"
                
                return True, message
            else:
                # Error
                error_msg = f"RTL generation failed!\n"
                error_msg += f"Command: {' '.join(cmd)}\n"
                error_msg += f"Error: {result.stderr}"
                
                # Parse specific error codes
                if "E-QOS-RANGE" in result.stderr:
                    error_msg = "Error: QoS value out of range (must be 0-15)"
                elif "E-WSTRB-MISMATCH" in result.stderr:
                    error_msg = f"Error: WSTRB width mismatch. Expected {self.project.bus.data_width // 8} bytes"
                elif "E-FIXED-PRIO-MISS" in result.stderr:
                    error_msg = "Error: Fixed priority configuration incomplete"
                elif "E-AHB-AXI-FEATURE" in result.stderr:
                    error_msg = "Error: AXI feature not supported in AHB mode"
                
                return False, error_msg
                
        except FileNotFoundError as e:
            # Check if it's actually the generator that's missing
            gen_exe = self.project_root / "gen_amba_axi" / "gen_amba_axi"
            if not gen_exe.exists():
                error_msg = "Error: gen_amba_axi not found!\n"
                error_msg += "Please build the generator first:\n"
                error_msg += "  cd gen_amba_axi && make"
                return False, error_msg
            else:
                # FileNotFoundError for something else - re-raise
                raise
            
        except Exception as e:
            return False, f"Unexpected error: {str(e)}"
    
    def generate_vip(self, output_dir: str = None) -> Tuple[bool, str]:
        """
        Generate UVM VIP environment
        Returns (success, message)
        """
        try:
            # Default output directory
            if not output_dir:
                num_masters = len(self.project.masters)
                num_slaves = len(self.project.slaves)
                output_dir = f"{self.output_dir}/vip_m{num_masters}s{num_slaves}"
            
            os.makedirs(output_dir, exist_ok=True)
            
            # Generate VIP structure
            self._generate_vip_structure(output_dir)
            
            message = f"VIP generated successfully!\n"
            message += f"Directory: {output_dir}\n"
            message += f"Configuration: {len(self.project.masters)}M × {len(self.project.slaves)}S\n"
            
            # List generated files
            files_generated = []
            for root, dirs, files in os.walk(output_dir):
                files_generated.extend(files)
            
            message += f"Files generated: {len(files_generated)}\n"
            message += "\nTo run simulation:\n"
            message += f"  cd {output_dir}/sim\n"
            message += "  make compile\n"
            message += "  make run TEST=axi4_base_test"
            
            return True, message
            
        except Exception as e:
            return False, f"VIP generation error: {str(e)}"
    
    def _generate_vip_structure(self, output_dir: str):
        """Generate VIP directory structure and files"""
        # Create directories
        dirs = [
            "agent",
            "agent/master_agent",
            "agent/slave_agent",
            "seq",
            "test",
            "env",
            "sim",
            "rtl"
        ]
        
        for d in dirs:
            os.makedirs(f"{output_dir}/{d}", exist_ok=True)
        
        # Generate package file
        self._generate_vip_package(f"{output_dir}/axi4_vip_pkg.sv")
        
        # Generate agent files
        self._generate_master_agent(f"{output_dir}/agent/master_agent")
        self._generate_slave_agent(f"{output_dir}/agent/slave_agent")
        
        # Generate environment
        self._generate_environment(f"{output_dir}/env/axi4_env.sv")
        
        # Generate base test
        self._generate_base_test(f"{output_dir}/test/axi4_base_test.sv")
        
        # Generate Makefile
        self._generate_makefile(f"{output_dir}/sim/Makefile")
    
    def _generate_vip_package(self, filename: str):
        """Generate VIP package file"""
        content = f"""// AXI4 VIP Package
// Auto-generated from bus configuration

package axi4_vip_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Parameters
    parameter ADDR_WIDTH = {self.project.bus.addr_width};
    parameter DATA_WIDTH = {self.project.bus.data_width};
    parameter ID_WIDTH = {self.project.bus.id_width};
    parameter USER_WIDTH = {self.project.bus.user_width};
    parameter NUM_MASTERS = {len(self.project.masters)};
    parameter NUM_SLAVES = {len(self.project.slaves)};
    
    // QoS configuration
    parameter QOS_ENABLE = {1 if self.project.bus.qos else 0};
    parameter DEFAULT_AWQOS = {self.project.bus.qos_default.aw};
    parameter DEFAULT_ARQOS = {self.project.bus.qos_default.ar};
    
    // Include all VIP components
    `include "axi4_transaction.sv"
    `include "axi4_master_driver.sv"
    `include "axi4_master_monitor.sv"
    `include "axi4_master_agent.sv"
    `include "axi4_slave_driver.sv"
    `include "axi4_slave_monitor.sv"
    `include "axi4_slave_agent.sv"
    `include "axi4_env.sv"
    
endpackage
"""
        with open(filename, 'w') as f:
            f.write(content)
    
    def _generate_master_agent(self, dir_path: str):
        """Generate master agent files"""
        # Generate master driver
        driver_content = f"""// AXI4 Master Driver
class axi4_master_driver extends uvm_driver #(axi4_transaction);
    `uvm_component_utils(axi4_master_driver)
    
    virtual axi4_if vif;
    int master_id;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
    endfunction
    
    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            drive_transaction(req);
            seq_item_port.item_done();
        end
    endtask
    
    task drive_transaction(axi4_transaction tr);
        // Drive AW channel
        @(posedge vif.aclk);
        vif.awvalid <= 1'b1;
        vif.awaddr <= tr.addr;
        vif.awlen <= tr.len;
        vif.awsize <= tr.size;
        vif.awburst <= tr.burst;
"""
        
        if self.project.bus.qos:
            driver_content += f"""        vif.awqos <= tr.qos_aw;
"""
        
        driver_content += """        wait(vif.awready);
        vif.awvalid <= 1'b0;
        
        // Drive W channel
        for(int i = 0; i <= tr.len; i++) begin
            @(posedge vif.aclk);
            vif.wvalid <= 1'b1;
            vif.wdata <= tr.data[i];
            vif.wstrb <= tr.strb[i];
            vif.wlast <= (i == tr.len);
            wait(vif.wready);
        end
        vif.wvalid <= 1'b0;
        
        // Wait for B response
        wait(vif.bvalid);
        tr.resp = vif.bresp;
        @(posedge vif.aclk);
        vif.bready <= 1'b1;
        @(posedge vif.aclk);
        vif.bready <= 1'b0;
    endtask
endclass
"""
        with open(f"{dir_path}/axi4_master_driver.sv", 'w') as f:
            f.write(driver_content)
    
    def _generate_slave_agent(self, dir_path: str):
        """Generate slave agent files"""
        # Generate slave driver
        driver_content = f"""// AXI4 Slave Driver
class axi4_slave_driver extends uvm_driver #(axi4_transaction);
    `uvm_component_utils(axi4_slave_driver)
    
    virtual axi4_if vif;
    int slave_id;
    bit [7:0] memory[int];
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
    endfunction
    
    task run_phase(uvm_phase phase);
        fork
            handle_write_address();
            handle_write_data();
            handle_write_response();
            handle_read_address();
            handle_read_data();
        join
    endtask
    
    task handle_write_address();
        forever begin
            @(posedge vif.aclk);
            if(vif.awvalid) begin
                vif.awready <= 1'b1;
                @(posedge vif.aclk);
                vif.awready <= 1'b0;
            end
        end
    endtask
    
    task handle_write_data();
        forever begin
            @(posedge vif.aclk);
            if(vif.wvalid) begin
                vif.wready <= 1'b1;
                @(posedge vif.aclk);
                vif.wready <= 1'b0;
            end
        end
    endtask
    
    task handle_write_response();
        forever begin
            // Simple response after each write
            @(posedge vif.aclk);
            vif.bvalid <= 1'b1;
            vif.bresp <= 2'b00; // OKAY
            wait(vif.bready);
            @(posedge vif.aclk);
            vif.bvalid <= 1'b0;
        end
    endtask
    
    task handle_read_address();
        forever begin
            @(posedge vif.aclk);
            if(vif.arvalid) begin
                vif.arready <= 1'b1;
                @(posedge vif.aclk);
                vif.arready <= 1'b0;
            end
        end
    endtask
    
    task handle_read_data();
        // Simplified read data handling
        forever begin
            @(posedge vif.aclk);
            vif.rvalid <= 1'b1;
            vif.rdata <= $random;
            vif.rresp <= 2'b00;
            vif.rlast <= 1'b1;
            wait(vif.rready);
            @(posedge vif.aclk);
            vif.rvalid <= 1'b0;
        end
    endtask
endclass
"""
        with open(f"{dir_path}/axi4_slave_driver.sv", 'w') as f:
            f.write(driver_content)
    
    def _generate_environment(self, filename: str):
        """Generate environment file"""
        content = f"""// AXI4 Environment
class axi4_env extends uvm_env;
    `uvm_component_utils(axi4_env)
    
    axi4_master_agent master_agents[NUM_MASTERS];
    axi4_slave_agent slave_agents[NUM_SLAVES];
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create master agents
        for(int i = 0; i < NUM_MASTERS; i++) begin
            master_agents[i] = axi4_master_agent::type_id::create($sformatf("master_agent_%0d", i), this);
            master_agents[i].master_id = i;
        end
        
        // Create slave agents
        for(int i = 0; i < NUM_SLAVES; i++) begin
            slave_agents[i] = axi4_slave_agent::type_id::create($sformatf("slave_agent_%0d", i), this);
            slave_agents[i].slave_id = i;
        end
    endfunction
endclass
"""
        with open(filename, 'w') as f:
            f.write(content)
    
    def _generate_base_test(self, filename: str):
        """Generate base test file"""
        content = f"""// AXI4 Base Test
class axi4_base_test extends uvm_test;
    `uvm_component_utils(axi4_base_test)
    
    axi4_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = axi4_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting AXI4 base test", UVM_LOW)
        
        // Run test sequences
        #1000ns;
        
        `uvm_info(get_type_name(), "Test completed", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
endclass
"""
        with open(filename, 'w') as f:
            f.write(content)
    
    def _generate_makefile(self, filename: str):
        """Generate simulation Makefile"""
        content = f"""# AXI4 VIP Simulation Makefile
# Auto-generated

# Simulator
SIM = vcs

# UVM home
UVM_HOME = ${{VCS_HOME}}/etc/uvm

# Compile options
COMP_OPTS = -sverilog +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm.sv
COMP_OPTS += +define+UVM_NO_DPI

# Simulation options
SIM_OPTS = +UVM_TESTNAME=axi4_base_test +UVM_VERBOSITY=UVM_MEDIUM

# Targets
compile:
\t$(SIM) $(COMP_OPTS) -f filelist.f

run:
\t./simv $(SIM_OPTS)

clean:
\trm -rf csrc simv* *.log *.vpd ucli.key

.PHONY: compile run clean
"""
        with open(filename, 'w') as f:
            f.write(content)
    
    def validate_configuration(self) -> Tuple[bool, List[str]]:
        """
        Validate the current configuration
        Returns (is_valid, list_of_errors)
        """
        errors = []
        
        # Check minimum requirements
        if len(self.project.masters) < 1:
            errors.append("At least 1 master required")
        
        if len(self.project.slaves) < 1:
            errors.append("At least 1 slave required")
        
        # Check data width
        valid_data_widths = [8, 16, 32, 64, 128, 256, 512, 1024]
        if self.project.bus.data_width not in valid_data_widths:
            errors.append(f"Invalid data width: {self.project.bus.data_width}")
        
        # Check address width
        if not (8 <= self.project.bus.addr_width <= 64):
            errors.append(f"Address width must be 8-64 bits, got {self.project.bus.addr_width}")
        
        # Check QoS values
        if self.project.bus.qos:
            for master in self.project.masters:
                if master.qos_default:
                    if not (0 <= master.qos_default.aw <= 15):
                        errors.append(f"Master {master.name}: AWQoS must be 0-15")
                    if not (0 <= master.qos_default.ar <= 15):
                        errors.append(f"Master {master.name}: ARQoS must be 0-15")
        
        # Check address overlaps
        for i, slave1 in enumerate(self.project.slaves):
            for j, slave2 in enumerate(self.project.slaves[i+1:], i+1):
                if self._check_overlap(slave1, slave2):
                    errors.append(f"Address overlap: {slave1.name} and {slave2.name}")
        
        # Check 4KB boundary
        for slave in self.project.slaves:
            if slave.size > 0x1000:  # > 4KB
                if slave.base % 0x1000 != 0:
                    errors.append(f"{slave.name}: Base address must be 4KB aligned for size > 4KB")
        
        # Check fixed priority completeness
        if self.project.bus.arbitration == "fixed":
            for slave in self.project.slaves:
                if not slave.priority or "order" not in slave.priority:
                    errors.append(f"{slave.name}: Fixed priority order not configured")
        
        return len(errors) == 0, errors
    
    def _check_overlap(self, slave1: 'SlaveNode', slave2: 'SlaveNode') -> bool:
        """Check if two slaves have overlapping address ranges"""
        end1 = slave1.base + slave1.size - 1
        end2 = slave2.base + slave2.size - 1
        
        return not (slave1.base > end2 or slave2.base > end1)