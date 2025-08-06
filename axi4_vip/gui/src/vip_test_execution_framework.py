#!/usr/bin/env python3

"""
AXI4 VIP Automated Test Execution Framework
Comprehensive framework for automated test execution, monitoring, and result collection.
References tim_axi4_vip architecture for scalable test automation.
"""

import os
import sys
import subprocess
import threading
import queue
import time
import json
import shutil
import signal
import psutil
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional, Tuple, Callable
from pathlib import Path
from dataclasses import dataclass, asdict
from enum import Enum
import concurrent.futures
import tempfile
import logging
from vip_storage_manager import get_storage_manager, StoragePolicy

class TestStatus(Enum):
    """Test execution status enumeration"""
    PENDING = "PENDING"
    QUEUED = "QUEUED"
    RUNNING = "RUNNING"
    COMPLETED = "COMPLETED"
    FAILED = "FAILED"
    TIMEOUT = "TIMEOUT"
    ABORTED = "ABORTED"
    ERROR = "ERROR"

@dataclass
class TestExecution:
    """Test execution configuration and state"""
    execution_id: int
    test_name: str
    test_id: int
    config_id: int
    simulator: str
    compile_args: str
    simulation_args: str
    seed: int
    timeout_seconds: int
    work_dir: str
    log_file: str
    status: TestStatus = TestStatus.PENDING
    start_time: Optional[datetime] = None
    end_time: Optional[datetime] = None
    exit_code: int = 0
    process: Optional[subprocess.Popen] = None
    error_message: str = ""
    warnings_count: int = 0
    errors_count: int = 0
    coverage_percentage: float = 0.0
    performance_metrics: Dict[str, Any] = None

    def __post_init__(self):
        if self.performance_metrics is None:
            self.performance_metrics = {}

class VIPTestExecutionFramework:
    """Automated test execution framework for AXI4 VIP testing"""
    
    def __init__(self, base_work_dir: str = "/tmp/vip_test_runs", 
                 max_concurrent_tests: int = 4, storage_policy: StoragePolicy = None):
        self.base_work_dir = Path(base_work_dir)
        self.max_concurrent_tests = max_concurrent_tests
        self.running_tests: Dict[int, TestExecution] = {}
        self.test_queue = queue.Queue()
        self.result_callbacks: List[Callable] = []
        self.executor = concurrent.futures.ThreadPoolExecutor(max_workers=max_concurrent_tests)
        self.shutdown_event = threading.Event()
        
        # Initialize storage manager
        self.storage_manager = get_storage_manager(str(base_work_dir), storage_policy)
        
        # Setup logging
        self.logger = self._setup_logging()
        
        # Initialize work directory
        self.base_work_dir.mkdir(parents=True, exist_ok=True)
        
        # Start execution manager thread
        self.execution_thread = threading.Thread(target=self._execution_manager, daemon=True)
        self.execution_thread.start()
        
    def _setup_logging(self) -> logging.Logger:
        """Setup logging for the test framework"""
        logger = logging.getLogger('VIPTestFramework')
        logger.setLevel(logging.INFO)
        
        if not logger.handlers:
            # Console handler
            console_handler = logging.StreamHandler()
            console_handler.setLevel(logging.INFO)
            console_formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            console_handler.setFormatter(console_formatter)
            logger.addHandler(console_handler)
            
            # File handler
            log_file = self.base_work_dir / "framework.log"
            file_handler = logging.FileHandler(log_file)
            file_handler.setLevel(logging.DEBUG)
            file_formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(funcName)s:%(lineno)d - %(message)s'
            )
            file_handler.setFormatter(file_formatter)
            logger.addHandler(file_handler)
            
        return logger
        
    def add_result_callback(self, callback: Callable[[TestExecution], None]):
        """Add callback function to be called when test completes"""
        self.result_callbacks.append(callback)
        
    def submit_test(self, test_execution: TestExecution) -> int:
        """Submit a test for execution"""
        test_execution.status = TestStatus.QUEUED
        self.test_queue.put(test_execution)
        self.logger.info(f"Queued test: {test_execution.test_name} (ID: {test_execution.execution_id})")
        return test_execution.execution_id
        
    def _execution_manager(self):
        """Main execution manager thread"""
        self.logger.info("Test execution manager started")
        
        while not self.shutdown_event.is_set():
            try:
                # Check if we can start new tests
                if len(self.running_tests) < self.max_concurrent_tests:
                    try:
                        test_execution = self.test_queue.get(timeout=1.0)
                        self._start_test_execution(test_execution)
                    except queue.Empty:
                        continue
                        
                # Check running tests for completion
                self._check_running_tests()
                
                time.sleep(0.5)  # Brief pause to prevent busy waiting
                
            except Exception as e:
                self.logger.error(f"Error in execution manager: {e}")
                
        self.logger.info("Test execution manager stopped")
        
    def _start_test_execution(self, test_execution: TestExecution):
        """Start executing a test"""
        try:
            # Setup test work directory
            test_work_dir = self._setup_test_workspace(test_execution)
            test_execution.work_dir = str(test_work_dir)
            
            # Generate test files
            self._generate_test_files(test_execution, test_work_dir)
            
            # Start test execution
            future = self.executor.submit(self._execute_test, test_execution)
            test_execution.status = TestStatus.RUNNING
            test_execution.start_time = datetime.now()
            
            self.running_tests[test_execution.execution_id] = test_execution
            
            self.logger.info(f"Started test: {test_execution.test_name} in {test_work_dir}")
            
        except Exception as e:
            test_execution.status = TestStatus.ERROR
            test_execution.error_message = str(e)
            test_execution.end_time = datetime.now()
            self.logger.error(f"Failed to start test {test_execution.test_name}: {e}")
            self._notify_completion(test_execution)
            
    def _setup_test_workspace(self, test_execution: TestExecution) -> Path:
        """Setup isolated workspace for test execution"""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        test_dir_name = f"test_{test_execution.execution_id}_{timestamp}"
        test_work_dir = self.base_work_dir / test_dir_name
        
        # Create directory structure
        test_work_dir.mkdir(parents=True, exist_ok=True)
        (test_work_dir / "src").mkdir(exist_ok=True)
        (test_work_dir / "sim").mkdir(exist_ok=True)
        (test_work_dir / "logs").mkdir(exist_ok=True)
        (test_work_dir / "coverage").mkdir(exist_ok=True)
        (test_work_dir / "waves").mkdir(exist_ok=True)
        
        # Setup log file
        test_execution.log_file = str(test_work_dir / "logs" / "test.log")
        
        return test_work_dir
        
    def _generate_test_files(self, test_execution: TestExecution, work_dir: Path):
        """Generate test files and scripts"""
        
        # Generate testbench
        self._generate_testbench(test_execution, work_dir)
        
        # Generate compilation script
        self._generate_compile_script(test_execution, work_dir)
        
        # Generate simulation script
        self._generate_simulation_script(test_execution, work_dir)
        
        # Generate makefile
        self._generate_makefile(test_execution, work_dir)
        
    def _generate_testbench(self, test_execution: TestExecution, work_dir: Path):
        """Generate testbench for the test"""
        tb_content = f'''`timescale 1ns/1ps

module tb_axi4_vip_test;

    // Test parameters
    parameter NUM_MASTERS = 4;
    parameter NUM_SLAVES = 4;
    parameter DATA_WIDTH = 64;
    parameter ADDR_WIDTH = 32;
    parameter ID_WIDTH = 8;
    parameter USER_WIDTH = 8;
    parameter TEST_SEED = {test_execution.seed};
    
    // Clock and reset
    reg clk;
    reg resetn;
    
    // Test control
    reg test_start;
    reg test_done;
    integer test_errors;
    integer test_warnings;
    
    // AXI4 Interface signals
    // Master interfaces
    wire [NUM_MASTERS*ID_WIDTH-1:0]     m_axi_awid;
    wire [NUM_MASTERS*ADDR_WIDTH-1:0]   m_axi_awaddr;
    wire [NUM_MASTERS*8-1:0]            m_axi_awlen;
    wire [NUM_MASTERS*3-1:0]            m_axi_awsize;
    wire [NUM_MASTERS*2-1:0]            m_axi_awburst;
    wire [NUM_MASTERS*1-1:0]            m_axi_awlock;
    wire [NUM_MASTERS*4-1:0]            m_axi_awcache;
    wire [NUM_MASTERS*3-1:0]            m_axi_awprot;
    wire [NUM_MASTERS*4-1:0]            m_axi_awqos;
    wire [NUM_MASTERS*4-1:0]            m_axi_awregion;
    wire [NUM_MASTERS*USER_WIDTH-1:0]   m_axi_awuser;
    wire [NUM_MASTERS-1:0]              m_axi_awvalid;
    wire [NUM_MASTERS-1:0]              m_axi_awready;
    
    wire [NUM_MASTERS*DATA_WIDTH-1:0]   m_axi_wdata;
    wire [NUM_MASTERS*DATA_WIDTH/8-1:0] m_axi_wstrb;
    wire [NUM_MASTERS-1:0]              m_axi_wlast;
    wire [NUM_MASTERS*USER_WIDTH-1:0]   m_axi_wuser;
    wire [NUM_MASTERS-1:0]              m_axi_wvalid;
    wire [NUM_MASTERS-1:0]              m_axi_wready;
    
    wire [NUM_MASTERS*ID_WIDTH-1:0]     m_axi_bid;
    wire [NUM_MASTERS*2-1:0]            m_axi_bresp;
    wire [NUM_MASTERS*USER_WIDTH-1:0]   m_axi_buser;
    wire [NUM_MASTERS-1:0]              m_axi_bvalid;
    wire [NUM_MASTERS-1:0]              m_axi_bready;
    
    wire [NUM_MASTERS*ID_WIDTH-1:0]     m_axi_arid;
    wire [NUM_MASTERS*ADDR_WIDTH-1:0]   m_axi_araddr;
    wire [NUM_MASTERS*8-1:0]            m_axi_arlen;
    wire [NUM_MASTERS*3-1:0]            m_axi_arsize;
    wire [NUM_MASTERS*2-1:0]            m_axi_arburst;
    wire [NUM_MASTERS*1-1:0]            m_axi_arlock;
    wire [NUM_MASTERS*4-1:0]            m_axi_arcache;
    wire [NUM_MASTERS*3-1:0]            m_axi_arprot;
    wire [NUM_MASTERS*4-1:0]            m_axi_arqos;
    wire [NUM_MASTERS*4-1:0]            m_axi_arregion;
    wire [NUM_MASTERS*USER_WIDTH-1:0]   m_axi_aruser;
    wire [NUM_MASTERS-1:0]              m_axi_arvalid;
    wire [NUM_MASTERS-1:0]              m_axi_arready;
    
    wire [NUM_MASTERS*ID_WIDTH-1:0]     m_axi_rid;
    wire [NUM_MASTERS*DATA_WIDTH-1:0]   m_axi_rdata;
    wire [NUM_MASTERS*2-1:0]            m_axi_rresp;
    wire [NUM_MASTERS-1:0]              m_axi_rlast;
    wire [NUM_MASTERS*USER_WIDTH-1:0]   m_axi_ruser;
    wire [NUM_MASTERS-1:0]              m_axi_rvalid;
    wire [NUM_MASTERS-1:0]              m_axi_rready;
    
    // Slave interfaces (similar structure)
    // ... (slave interface signals would be defined here)
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100MHz clock
    end
    
    // Reset generation
    initial begin
        resetn = 0;
        repeat(10) @(posedge clk);
        resetn = 1;
    end
    
    // Test sequence
    initial begin
        // Initialize
        test_start = 0;
        test_done = 0;
        test_errors = 0;
        test_warnings = 0;
        
        // Set random seed
        $srandom(TEST_SEED);
        
        // Wait for reset deassertion
        wait(resetn);
        repeat(5) @(posedge clk);
        
        $display("Starting AXI4 VIP Test: {test_execution.test_name}");
        $display("Test ID: {test_execution.test_id}");
        $display("Execution ID: {test_execution.execution_id}");
        $display("Seed: %0d", TEST_SEED);
        
        test_start = 1;
        
        // Call test sequence based on test type
        case ("{test_execution.test_name}")
            "Basic Read/Write Test": run_basic_read_write_test();
            "Burst Transaction Test": run_burst_transaction_test();
            "Exclusive Access Test": run_exclusive_access_test();
            "QoS Arbitration Test": run_qos_arbitration_test();
            "Performance Benchmark": run_performance_benchmark();
            default: begin
                $display("ERROR: Unknown test type");
                test_errors++;
            end
        endcase
        
        test_done = 1;
        
        // Final report
        $display("\\n=== Test Summary ===");
        $display("Test: {test_execution.test_name}");
        $display("Errors: %0d", test_errors);
        $display("Warnings: %0d", test_warnings);
        $display("Status: %s", (test_errors == 0) ? "PASS" : "FAIL");
        
        if (test_errors == 0) begin
            $display("TEST PASSED");
            $finish(0);
        end else begin
            $display("TEST FAILED");
            $finish(1);
        end
    end
    
    // Test timeout
    initial begin
        #{test_execution.timeout_seconds * 1000000000}; // Convert to ns
        $display("ERROR: Test timeout after {test_execution.timeout_seconds} seconds");
        $finish(2);
    end
    
    // Test procedures
    task run_basic_read_write_test();
        begin
            $display("Running Basic Read/Write Test...");
            // Implement basic read/write test sequence
            repeat(100) begin
                @(posedge clk);
                // Add test logic here
            end
        end
    endtask
    
    task run_burst_transaction_test();
        begin
            $display("Running Burst Transaction Test...");
            // Implement burst transaction test sequence
            repeat(200) begin
                @(posedge clk);
                // Add burst test logic here
            end
        end
    endtask
    
    task run_exclusive_access_test();
        begin
            $display("Running Exclusive Access Test...");
            // Implement exclusive access test sequence
            repeat(300) begin
                @(posedge clk);
                // Add exclusive access test logic here
            end
        end
    endtask
    
    task run_qos_arbitration_test();
        begin
            $display("Running QoS Arbitration Test...");
            // Implement QoS arbitration test sequence
            repeat(400) begin
                @(posedge clk);
                // Add QoS test logic here
            end
        end
    endtask
    
    task run_performance_benchmark();
        begin
            $display("Running Performance Benchmark...");
            // Implement performance benchmark sequence
            repeat(1000) begin
                @(posedge clk);
                // Add performance test logic here
            end
        end
    endtask
    
    // Instantiate DUT (Device Under Test)
    // This would instantiate the generated AXI4 interconnect
    // amba_axi_m4s4 dut (
    //     .clk(clk),
    //     .resetn(resetn),
    //     // Connect all AXI interfaces
    //     ...
    // );
    
    // Waveform dumping
    initial begin
        if ($test$plusargs("WAVES")) begin
            $dumpfile("waves/test.vcd");
            $dumpvars(0, tb_axi4_vip_test);
        end
    end
    
    // Coverage collection
    initial begin
        if ($test$plusargs("COVERAGE")) begin
            // Enable coverage collection
        end
    end

endmodule
'''
        
        with open(work_dir / "src" / "tb_axi4_vip_test.sv", 'w') as f:
            f.write(tb_content)
            
    def _generate_compile_script(self, test_execution: TestExecution, work_dir: Path):
        """Generate compilation script for the simulator"""
        
        if test_execution.simulator == "questa":
            script_content = f'''#!/bin/bash
# Questa compilation script for {test_execution.test_name}

set -e

# Create work library
vlib work

# Compile design files
vlog -sv +incdir+../src \\
     {test_execution.compile_args} \\
     ../src/tb_axi4_vip_test.sv

echo "Compilation completed successfully"
'''
        elif test_execution.simulator == "vcs":
            script_content = f'''#!/bin/bash
# VCS compilation script for {test_execution.test_name}

set -e

# Compile with VCS
vcs -sverilog +incdir+../src \\
    {test_execution.compile_args} \\
    -o simv \\
    ../src/tb_axi4_vip_test.sv

echo "Compilation completed successfully"
'''
        elif test_execution.simulator == "xcelium":
            script_content = f'''#!/bin/bash
# Xcelium compilation script for {test_execution.test_name}

set -e

# Compile with Xcelium
xrun -compile \\
     -sv +incdir+../src \\
     {test_execution.compile_args} \\
     ../src/tb_axi4_vip_test.sv

echo "Compilation completed successfully"
'''
        else:
            # Generic script
            script_content = f'''#!/bin/bash
# Generic compilation script for {test_execution.test_name}

echo "Compilation not implemented for simulator: {test_execution.simulator}"
exit 1
'''
        
        script_path = work_dir / "sim" / "compile.sh"
        with open(script_path, 'w') as f:
            f.write(script_content)
        script_path.chmod(0o755)
        
    def _generate_simulation_script(self, test_execution: TestExecution, work_dir: Path):
        """Generate simulation script"""
        
        if test_execution.simulator == "questa":
            script_content = f'''#!/bin/bash
# Questa simulation script for {test_execution.test_name}

set -e

# Run simulation
vsim -batch -do "run -all; quit" \\
     {test_execution.simulation_args} \\
     +SEED={test_execution.seed} \\
     +WAVES +COVERAGE \\
     tb_axi4_vip_test

echo "Simulation completed"
'''
        elif test_execution.simulator == "vcs":
            script_content = f'''#!/bin/bash
# VCS simulation script for {test_execution.test_name}

set -e

# Run simulation
./simv {test_execution.simulation_args} \\
       +SEED={test_execution.seed} \\
       +WAVES +COVERAGE

echo "Simulation completed"
'''
        elif test_execution.simulator == "xcelium":
            script_content = f'''#!/bin/bash
# Xcelium simulation script for {test_execution.test_name}

set -e

# Run simulation
xrun -R \\
     {test_execution.simulation_args} \\
     +SEED={test_execution.seed} \\
     +WAVES +COVERAGE \\
     tb_axi4_vip_test

echo "Simulation completed"
'''
        else:
            # Generic script
            script_content = f'''#!/bin/bash
# Generic simulation script for {test_execution.test_name}

echo "Simulation not implemented for simulator: {test_execution.simulator}"
exit 1
'''
        
        script_path = work_dir / "sim" / "simulate.sh"
        with open(script_path, 'w') as f:
            f.write(script_content)
        script_path.chmod(0o755)
        
    def _generate_makefile(self, test_execution: TestExecution, work_dir: Path):
        """Generate Makefile for test execution"""
        makefile_content = f'''# Makefile for {test_execution.test_name}

.PHONY: all compile simulate clean

all: compile simulate

compile:
\t@echo "Compiling test..."
\tcd sim && ./compile.sh 2>&1 | tee ../logs/compile.log

simulate: compile
\t@echo "Running simulation..."
\tcd sim && ./simulate.sh 2>&1 | tee ../logs/simulate.log

clean:
\t@echo "Cleaning up..."
\trm -rf sim/work sim/simv* sim/csrc sim/DVEfiles
\trm -f logs/*.log waves/*.vcd coverage/*.ucdb

help:
\t@echo "Available targets:"
\t@echo "  compile  - Compile the testbench"
\t@echo "  simulate - Run the simulation"
\t@echo "  clean    - Clean up generated files"
\t@echo "  help     - Show this help"
'''
        
        with open(work_dir / "Makefile", 'w') as f:
            f.write(makefile_content)
            
    def _execute_test(self, test_execution: TestExecution) -> TestExecution:
        """Execute a single test"""
        try:
            work_dir = Path(test_execution.work_dir)
            
            # Change to work directory
            original_cwd = os.getcwd()
            os.chdir(work_dir)
            
            try:
                # Run compilation
                compile_result = self._run_command(
                    ["make", "compile"], 
                    test_execution.timeout_seconds // 4,  # 1/4 of total timeout for compile
                    test_execution.log_file
                )
                
                if compile_result.returncode != 0:
                    test_execution.status = TestStatus.FAILED
                    test_execution.error_message = "Compilation failed"
                    test_execution.exit_code = compile_result.returncode
                    return test_execution
                    
                # Run simulation
                sim_result = self._run_command(
                    ["make", "simulate"],
                    test_execution.timeout_seconds * 3 // 4,  # 3/4 of total timeout for simulation
                    test_execution.log_file
                )
                
                test_execution.exit_code = sim_result.returncode
                
                if sim_result.returncode == 0:
                    test_execution.status = TestStatus.COMPLETED
                elif sim_result.returncode == 2:  # Timeout code from testbench
                    test_execution.status = TestStatus.TIMEOUT
                    test_execution.error_message = "Test timeout"
                else:
                    test_execution.status = TestStatus.FAILED
                    test_execution.error_message = "Simulation failed"
                    
                # Parse results
                self._parse_test_results(test_execution)
                
            finally:
                os.chdir(original_cwd)
                
        except Exception as e:
            test_execution.status = TestStatus.ERROR
            test_execution.error_message = str(e)
            self.logger.error(f"Test execution error: {e}")
            
        finally:
            test_execution.end_time = datetime.now()
            
        return test_execution
        
    def _run_command(self, cmd: List[str], timeout: int, log_file: str) -> subprocess.CompletedResult:
        """Run a command with timeout and logging"""
        with open(log_file, 'a') as log:
            log.write(f"\\n=== Running command: {' '.join(cmd)} ===\\n")
            log.flush()
            
            try:
                result = subprocess.run(
                    cmd,
                    timeout=timeout,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    text=True
                )
                return result
                
            except subprocess.TimeoutExpired:
                log.write(f"\\nCommand timed out after {timeout} seconds\\n")
                return subprocess.CompletedResult(cmd, 124)  # Timeout exit code
                
    def _parse_test_results(self, test_execution: TestExecution):
        """Parse test results from log files"""
        try:
            log_file = test_execution.log_file
            if not os.path.exists(log_file):
                return
                
            with open(log_file, 'r') as f:
                log_content = f.read()
                
            # Parse errors and warnings
            test_execution.errors_count = log_content.count("ERROR:")
            test_execution.warnings_count = log_content.count("WARNING:")
            
            # Parse coverage if available
            coverage_match = re.search(r"Coverage:\s*(\d+\.?\d*)%", log_content)
            if coverage_match:
                test_execution.coverage_percentage = float(coverage_match.group(1))
                
            # Parse performance metrics
            perf_metrics = {}
            
            # Look for throughput metrics
            throughput_match = re.search(r"Throughput:\s*(\d+\.?\d*)\s*MB/s", log_content)
            if throughput_match:
                perf_metrics['throughput_mbps'] = float(throughput_match.group(1))
                
            # Look for latency metrics
            latency_match = re.search(r"Average Latency:\s*(\d+\.?\d*)\s*cycles", log_content)
            if latency_match:
                perf_metrics['avg_latency_cycles'] = float(latency_match.group(1))
                
            test_execution.performance_metrics = perf_metrics
            
        except Exception as e:
            self.logger.warning(f"Failed to parse test results: {e}")
            
    def _check_running_tests(self):
        """Check status of running tests"""
        completed_tests = []
        
        for execution_id, test_execution in self.running_tests.items():
            if test_execution.status in [TestStatus.COMPLETED, TestStatus.FAILED, 
                                       TestStatus.TIMEOUT, TestStatus.ERROR, TestStatus.ABORTED]:
                completed_tests.append(execution_id)
                
        # Remove completed tests and notify
        for execution_id in completed_tests:
            test_execution = self.running_tests.pop(execution_id)
            self._notify_completion(test_execution)
            
    def _notify_completion(self, test_execution: TestExecution):
        """Notify callbacks about test completion"""
        self.logger.info(f"Test completed: {test_execution.test_name} - {test_execution.status.value}")
        
        # Limit log file size after completion
        if test_execution.log_file and os.path.exists(test_execution.log_file):
            self.storage_manager.limit_log_file_size(test_execution.log_file)
        
        # Schedule workspace cleanup after a delay (keep for debugging)
        cleanup_delay_hours = 2  # Keep workspace for 2 hours after completion
        cleanup_timer = threading.Timer(cleanup_delay_hours * 3600, 
                                      self._cleanup_test_workspace_delayed, 
                                      args=[test_execution.execution_id])
        cleanup_timer.daemon = True
        cleanup_timer.start()
        
        for callback in self.result_callbacks:
            try:
                callback(test_execution)
            except Exception as e:
                self.logger.error(f"Error in result callback: {e}")
                
    def _cleanup_test_workspace_delayed(self, execution_id: int):
        """Cleanup test workspace after delay"""
        try:
            self.cleanup_test_workspace(execution_id, keep_logs=True)
        except Exception as e:
            self.logger.warning(f"Failed delayed cleanup of test {execution_id}: {e}")
                
    def abort_test(self, execution_id: int) -> bool:
        """Abort a running test"""
        if execution_id in self.running_tests:
            test_execution = self.running_tests[execution_id]
            if test_execution.process:
                try:
                    # Terminate process tree
                    parent = psutil.Process(test_execution.process.pid)
                    for child in parent.children(recursive=True):
                        child.terminate()
                    parent.terminate()
                    
                    test_execution.status = TestStatus.ABORTED
                    test_execution.end_time = datetime.now()
                    return True
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    pass
                    
        return False
        
    def get_test_status(self, execution_id: int) -> Optional[TestExecution]:
        """Get current status of a test"""
        return self.running_tests.get(execution_id)
        
    def get_all_running_tests(self) -> List[TestExecution]:
        """Get list of all currently running tests"""
        return list(self.running_tests.values())
        
    def get_queue_size(self) -> int:
        """Get number of tests in queue"""
        return self.test_queue.qsize()
        
    def cleanup_test_workspace(self, execution_id: int, keep_logs: bool = True):
        """Clean up test workspace after completion"""
        try:
            # Find test directory
            for test_dir in self.base_work_dir.iterdir():
                if test_dir.is_dir() and f"test_{execution_id}_" in test_dir.name:
                    if keep_logs:
                        # Keep only logs and coverage
                        for item in test_dir.iterdir():
                            if item.name not in ['logs', 'coverage']:
                                if item.is_dir():
                                    shutil.rmtree(item)
                                else:
                                    item.unlink()
                    else:
                        # Remove entire directory
                        shutil.rmtree(test_dir)
                    break
                    
        except Exception as e:
            self.logger.warning(f"Failed to cleanup workspace for test {execution_id}: {e}")
            
    def shutdown(self, timeout: int = 30):
        """Shutdown the test execution framework"""
        self.logger.info("Shutting down test execution framework...")
        
        # Signal shutdown
        self.shutdown_event.set()
        
        # Abort all running tests
        for execution_id in list(self.running_tests.keys()):
            self.abort_test(execution_id)
            
        # Wait for execution thread to finish
        self.execution_thread.join(timeout=timeout)
        
        # Shutdown executor
        self.executor.shutdown(wait=True, timeout=timeout)
        
        self.logger.info("Test execution framework shutdown complete")

# Example usage and integration
def example_test_execution():
    """Example of using the test execution framework"""
    
    # Initialize framework
    framework = VIPTestExecutionFramework(max_concurrent_tests=2)
    
    # Add result callback
    def result_callback(test_execution: TestExecution):
        print(f"Test {test_execution.test_name} completed with status {test_execution.status.value}")
        if test_execution.status == TestStatus.COMPLETED:
            print(f"  Coverage: {test_execution.coverage_percentage}%")
            print(f"  Performance: {test_execution.performance_metrics}")
        elif test_execution.error_message:
            print(f"  Error: {test_execution.error_message}")
            
    framework.add_result_callback(result_callback)
    
    # Create test executions
    test_configs = [
        {
            'execution_id': 1,
            'test_name': 'Basic Read/Write Test',
            'test_id': 101,
            'config_id': 1,
            'simulator': 'questa',
            'compile_args': '-O2',
            'simulation_args': '+UVM_TESTNAME=basic_test',
            'seed': 1234,
            'timeout_seconds': 300
        },
        {
            'execution_id': 2,
            'test_name': 'Burst Transaction Test',
            'test_id': 102,
            'config_id': 1,
            'simulator': 'questa',
            'compile_args': '-O2',
            'simulation_args': '+UVM_TESTNAME=burst_test',
            'seed': 5678,
            'timeout_seconds': 600
        }
    ]
    
    # Submit tests
    for config in test_configs:
        test_execution = TestExecution(**config)
        framework.submit_test(test_execution)
        
    # Monitor execution
    try:
        while framework.get_queue_size() > 0 or len(framework.get_all_running_tests()) > 0:
            time.sleep(1)
            running_tests = framework.get_all_running_tests()
            if running_tests:
                print(f"Running tests: {[t.test_name for t in running_tests]}")
                
    except KeyboardInterrupt:
        print("Interrupted - shutting down...")
        
    finally:
        framework.shutdown()

if __name__ == "__main__":
    import re  # Add missing import
    example_test_execution()