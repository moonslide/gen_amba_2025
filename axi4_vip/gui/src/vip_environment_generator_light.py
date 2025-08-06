#!/usr/bin/env python3
"""
Lightweight VIP Environment Generator Wrapper
This module provides a more efficient way to generate VIP environments
by deferring the import of the large vip_environment_generator module
"""

import os
import sys
import time
import threading
import importlib.util

class VIPEnvironmentGeneratorLight:
    """Lightweight wrapper that defers heavy imports"""
    
    def __init__(self, gui_config, mode, simulator="vcs", progress_callback=None):
        self.gui_config = gui_config
        self.mode = mode
        self.simulator = simulator
        self.progress_callback = progress_callback
        self._generator = None
        self._import_error = None
        
    def _import_generator_module(self):
        """Import the generator module in a separate thread with timeout"""
        try:
            print("[INFO] Starting import of VIP environment generator module...")
            start_time = time.time()
            
            # Import the module
            from vip_environment_generator import VIPEnvironmentGenerator
            
            # Create the generator instance
            self._generator = VIPEnvironmentGenerator(self.gui_config, self.mode, self.simulator)
            
            elapsed = time.time() - start_time
            print(f"[INFO] VIP environment generator loaded in {elapsed:.2f} seconds")
            
        except Exception as e:
            self._import_error = e
            print(f"[ERROR] Failed to import VIP environment generator: {e}")
            
    def get_generator(self):
        """Get the generator instance, importing if necessary"""
        if self._generator is None and self._import_error is None:
            # Try importing with a timeout
            import_thread = threading.Thread(target=self._import_generator_module)
            import_thread.daemon = True
            import_thread.start()
            
            # Wait for import with timeout
            import_thread.join(timeout=30.0)  # 30 second timeout
            
            if import_thread.is_alive():
                raise TimeoutError("VIP environment generator import timed out after 30 seconds")
                
            if self._import_error:
                raise self._import_error
                
        return self._generator
        
    def generate_environment(self, output_dir):
        """Generate the environment"""
        # Update progress
        if self.progress_callback:
            self.progress_callback("Initializing VIP generator...")
            
        # Get the generator (will import if needed)
        generator = self.get_generator()
        
        if generator is None:
            raise RuntimeError("Failed to initialize VIP environment generator")
            
        # Call the original generate method
        return generator.generate_environment(output_dir)


def create_minimal_vip_environment(gui_config, output_dir, mode="rtl_integration"):
    """Create a minimal VIP environment without importing the full generator"""
    env_name = f"axi4_vip_env_{mode}"
    env_path = os.path.join(output_dir, env_name)
    
    # Create basic directory structure
    dirs = [
        "agent", "env", "seq", "test", "top", "pkg", "include", "intf", "sim"
    ]
    
    for dir_name in dirs:
        os.makedirs(os.path.join(env_path, dir_name), exist_ok=True)
        
    # Create a minimal package file
    pkg_file = os.path.join(env_path, "pkg", "axi4_globals_pkg.sv")
    with open(pkg_file, 'w') as f:
        f.write(f"""// Minimal AXI4 globals package
package axi4_globals_pkg;
    parameter int ADDRESS_WIDTH = {gui_config.addr_width};
    parameter int DATA_WIDTH = {gui_config.data_width};
    parameter int NO_OF_MASTERS = {len(gui_config.masters)};
    parameter int NO_OF_SLAVES = {len(gui_config.slaves)};
endpackage
""")
    
    print(f"[INFO] Created minimal VIP environment at: {env_path}")
    return env_path