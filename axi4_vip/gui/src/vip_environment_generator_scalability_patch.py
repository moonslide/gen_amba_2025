#!/usr/bin/env python3
"""
Scalability patch for VIP Environment Generator
Fixes hang issue with 11x11+ bus matrices during generation
"""

import os
import json
import subprocess
import threading
import time
from datetime import datetime
from dataclasses import asdict

class ScalableVIPEnvironmentGenerator:
    """Enhanced VIP Environment Generator with scalability fixes for large bus matrices"""
    
    def __init__(self, gui_config, mode, simulator="vcs"):
        self.config = gui_config
        self.mode = mode
        self.simulator = simulator
        self.timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        self.warnings = []
        self.progress_callback = None  # Add progress callback support
        self.cancel_event = threading.Event()  # For cancellation support
        
    def set_progress_callback(self, callback):
        """Set a callback function for progress updates"""
        self.progress_callback = callback
        
    def _update_progress(self, message, step=None):
        """Update progress with optional callback"""
        if self.progress_callback:
            self.progress_callback(message, step)
        print(f"[VIP Gen] {message}")
        
    def _check_large_matrix_warning(self):
        """Check if matrix size might cause performance issues"""
        num_masters = len(self.config.masters)
        num_slaves = len(self.config.slaves)
        
        if num_masters * num_slaves > 49:  # 7x7 = 49
            self.warnings.append(f"PERFORMANCE WARNING: {num_masters}x{num_slaves} matrix is very large")
            self.warnings.append(f"Generation may take several minutes. Consider reducing matrix size.")
            return True
        elif num_masters * num_slaves > 100:  # 10x10 = 100
            self.warnings.append(f"CRITICAL WARNING: {num_masters}x{num_slaves} matrix exceeds recommended size")
            self.warnings.append(f"Generation may fail or take excessive time. Maximum recommended: 10x10")
            return True
        return False
        
    def generate_environment(self, output_dir):
        """Generate VIP environment with progress tracking and timeout handling"""
        # Check for large matrix
        self._check_large_matrix_warning()
        
        # Validate configuration
        self._validate_configuration()
        
        # Print warnings
        if self.warnings:
            print("\n⚠️  Configuration Warnings:")
            for warning in self.warnings:
                print(f"   {warning}")
            print()
        
        env_name = f"axi4_vip_env_{self.mode}"
        env_path = os.path.join(output_dir, env_name)
        
        try:
            # Create directory structure
            self._update_progress("Creating directory structure...", 7)
            self._create_directory_structure(env_path)
            
            # Check for cancellation
            if self.cancel_event.is_set():
                return None
                
            # Generate package files
            self._update_progress("Generating package files...", 8)
            self._generate_package_files(env_path)
            
            # For large matrices, generate files in chunks with progress updates
            num_masters = len(self.config.masters)
            num_slaves = len(self.config.slaves)
            
            if num_masters * num_slaves > 64:
                # Large matrix - show detailed progress
                self._generate_files_with_progress(env_path)
            else:
                # Normal generation
                self._generate_all_files(env_path)
                
            return env_path
            
        except Exception as e:
            self._update_progress(f"Error during generation: {str(e)}")
            raise
    
    def _generate_files_with_progress(self, env_path):
        """Generate files with detailed progress for large matrices"""
        steps = [
            ("Generating interface files", self._generate_interface_files),
            ("Generating agent files", self._generate_agent_files),
            ("Generating sequence files", self._generate_sequence_files),
            ("Generating environment files", self._generate_environment_files),
            ("Generating test files", self._generate_test_files),
            ("Generating top files", self._generate_top_files),
            ("Generating simulation files", self._generate_simulation_files),
            ("Generating documentation", self._generate_documentation),
        ]
        
        if self.mode == "rtl_integration":
            steps.append(("Generating RTL wrapper", lambda p: self._generate_rtl_wrapper(p)))
        
        for i, (desc, func) in enumerate(steps):
            if self.cancel_event.is_set():
                return
            
            # Calculate sub-step within step 8
            sub_progress = 8.0 + (i / len(steps)) * 2.0  # Steps 8-10
            self._update_progress(desc, int(sub_progress))
            
            func(env_path)
    
    def _generate_interconnect_rtl_with_timeout(self, rtl_dir):
        """Generate interconnect RTL with timeout and progress tracking"""
        num_masters = len(self.config.masters)
        num_slaves = len(self.config.slaves)
        
        # Find gen_amba_axi tool
        gen_amba_path = self._find_gen_amba_tool()
        if not gen_amba_path:
            self.warnings.append("gen_amba_axi tool not found")
            self._create_dummy_rtl_files(rtl_dir, num_masters, num_slaves)
            return
        
        # Calculate timeout based on matrix size
        base_timeout = 120  # 120 seconds for small matrices
        matrix_size = num_masters * num_slaves
        if matrix_size > 100:  # 10x10 or larger
            timeout = base_timeout * (matrix_size / 16)  # Scale timeout
            timeout = min(timeout, 1200)  # Max 20 minutes
        elif matrix_size > 64:  # 8x8 or larger
            timeout = base_timeout * (matrix_size / 16)  # Scale timeout
            timeout = min(timeout, 600)  # Max 10 minutes
        else:
            timeout = base_timeout
        
        self._update_progress(f"Generating {num_masters}x{num_slaves} interconnect RTL (timeout: {int(timeout)}s)...")
        
        interconnect_file = os.path.join(rtl_dir, f"amba_axi_m{num_masters}s{num_slaves}.v")
        cmd = [gen_amba_path, 
               f"--master={num_masters}",
               f"--slave={num_slaves}",
               f"--output={interconnect_file}"]
        
        try:
            # Run with timeout
            process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, 
                                     universal_newlines=True)
            
            # Monitor progress in separate thread
            def monitor_progress():
                start_time = time.time()
                while process.poll() is None:
                    elapsed = time.time() - start_time
                    if elapsed > timeout:
                        process.terminate()
                        break
                    if self.cancel_event.is_set():
                        process.terminate()
                        break
                    time.sleep(1)
            
            monitor_thread = threading.Thread(target=monitor_progress)
            monitor_thread.start()
            
            # Wait for completion
            stdout, stderr = process.communicate()
            monitor_thread.join()
            
            if process.returncode == 0:
                print(f"✓ Generated AXI interconnect: {interconnect_file}")
                self._create_support_rtl_files(rtl_dir, num_masters, num_slaves)
            else:
                raise subprocess.CalledProcessError(process.returncode, cmd, stdout, stderr)
                
        except subprocess.TimeoutExpired:
            self.warnings.append(f"Interconnect generation timed out after {timeout}s")
            self.warnings.append(f"Matrix size {num_masters}x{num_slaves} may be too large")
            self._create_dummy_rtl_files(rtl_dir, num_masters, num_slaves)
        except subprocess.CalledProcessError as e:
            self.warnings.append(f"Failed to generate interconnect: {e.stderr}")
            self._create_dummy_rtl_files(rtl_dir, num_masters, num_slaves)
    
    def _find_gen_amba_tool(self):
        """Find gen_amba_axi tool with multiple search paths"""
        search_paths = [
            os.path.join(os.path.dirname(__file__), "../../../../gen_amba_axi/gen_amba_axi"),
            os.path.join(os.path.dirname(__file__), "../../../gen_amba_axi/gen_amba_axi"),
            os.path.join(os.path.dirname(__file__), "../../gen_amba_axi/gen_amba_axi"),
            "/usr/local/bin/gen_amba_axi",
            "gen_amba_axi"  # Try PATH
        ]
        
        for path in search_paths:
            abs_path = os.path.abspath(path) if not path.startswith('/') else path
            if os.path.exists(abs_path) and os.access(abs_path, os.X_OK):
                return abs_path
        
        return None
    
    def _create_optimized_dummy_rtl(self, rtl_dir, num_masters, num_slaves):
        """Create optimized dummy RTL for large matrices"""
        with open(os.path.join(rtl_dir, f"amba_axi_m{num_masters}s{num_slaves}.v"), "w") as f:
            f.write(f"""// Placeholder RTL for {num_masters}x{num_slaves} AXI interconnect
// WARNING: This is a dummy file for large matrix ({num_masters}x{num_slaves})
// 
// For matrices larger than 10x10, consider:
// 1. Using hierarchical interconnect design
// 2. Implementing partial crossbar with shared slaves
// 3. Using NoC (Network-on-Chip) approach
//
// To generate actual RTL, run manually with extended timeout:
// ./gen_amba_axi --master={num_masters} --slave={num_slaves} --output=amba_axi_m{num_masters}s{num_slaves}.v

module amba_axi_m{num_masters}s{num_slaves} #(
    parameter NUM_MASTER = {num_masters},
    parameter NUM_SLAVE = {num_slaves},
    parameter WIDTH_ID = 4,
    parameter WIDTH_AD = 32,
    parameter WIDTH_DA = 32
) (
    input ARESETn,
    input ACLK,
    // Master ports
""")
            
            # Add master port comments
            for i in range(min(num_masters, 3)):
                f.write(f"    // Master {i} ports - TODO: Add all signals\n")
            if num_masters > 3:
                f.write(f"    // ... Masters 3-{num_masters-1} ...\n")
                
            # Add slave port comments  
            for i in range(min(num_slaves, 3)):
                f.write(f"    // Slave {i} ports - TODO: Add all signals\n")
            if num_slaves > 3:
                f.write(f"    // ... Slaves 3-{num_slaves-1} ...\n")
                
            f.write(""");

    // Large matrix interconnect implementation
    // TODO: Implement hierarchical or NoC-based design for efficiency

endmodule
""")

# Monkey patch the original class to add these improvements
def apply_scalability_patch():
    """Apply scalability improvements to VIPEnvironmentGenerator"""
    import sys
    sys.path.insert(0, os.path.dirname(__file__))
    
    try:
        from vip_environment_generator import VIPEnvironmentGenerator
        
        # Save original methods
        VIPEnvironmentGenerator._original_generate_environment = VIPEnvironmentGenerator.generate_environment
        VIPEnvironmentGenerator._original_generate_interconnect_rtl = VIPEnvironmentGenerator._generate_interconnect_rtl
        
        # Apply patches
        VIPEnvironmentGenerator.set_progress_callback = ScalableVIPEnvironmentGenerator.set_progress_callback
        VIPEnvironmentGenerator._update_progress = ScalableVIPEnvironmentGenerator._update_progress
        VIPEnvironmentGenerator._check_large_matrix_warning = ScalableVIPEnvironmentGenerator._check_large_matrix_warning
        VIPEnvironmentGenerator._generate_files_with_progress = ScalableVIPEnvironmentGenerator._generate_files_with_progress
        VIPEnvironmentGenerator._generate_interconnect_rtl_with_timeout = ScalableVIPEnvironmentGenerator._generate_interconnect_rtl_with_timeout
        VIPEnvironmentGenerator._find_gen_amba_tool = ScalableVIPEnvironmentGenerator._find_gen_amba_tool
        VIPEnvironmentGenerator._create_optimized_dummy_rtl = ScalableVIPEnvironmentGenerator._create_optimized_dummy_rtl
        
        # Replace generate_interconnect_rtl with timeout version
        VIPEnvironmentGenerator._generate_interconnect_rtl = VIPEnvironmentGenerator._generate_interconnect_rtl_with_timeout
        
        # Initialize new attributes
        if not hasattr(VIPEnvironmentGenerator, 'progress_callback'):
            VIPEnvironmentGenerator.progress_callback = None
        if not hasattr(VIPEnvironmentGenerator, 'cancel_event'):
            VIPEnvironmentGenerator.cancel_event = threading.Event()
        
        print("✅ Scalability patch applied successfully!")
        return True
        
    except Exception as e:
        print(f"❌ Failed to apply scalability patch: {e}")
        return False

if __name__ == "__main__":
    apply_scalability_patch()