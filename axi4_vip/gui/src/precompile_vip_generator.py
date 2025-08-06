#!/usr/bin/env python3
"""Precompile VIP environment generator to speed up imports"""

import py_compile
import os
import sys
import time

def precompile_module():
    """Precompile the VIP environment generator module"""
    module_path = os.path.join(os.path.dirname(__file__), "vip_environment_generator.py")
    
    if not os.path.exists(module_path):
        print(f"Error: Module not found at {module_path}")
        return False
        
    print(f"Precompiling {module_path}...")
    start_time = time.time()
    
    try:
        # Compile to bytecode
        py_compile.compile(module_path, doraise=True, optimize=2)
        
        elapsed = time.time() - start_time
        print(f"Successfully precompiled in {elapsed:.2f} seconds")
        
        # Check if __pycache__ was created
        pycache_dir = os.path.join(os.path.dirname(module_path), "__pycache__")
        if os.path.exists(pycache_dir):
            pyc_files = [f for f in os.listdir(pycache_dir) if f.startswith("vip_environment_generator")]
            if pyc_files:
                print(f"Bytecode files created: {', '.join(pyc_files)}")
            else:
                print("Warning: No bytecode files found")
        
        return True
        
    except py_compile.PyCompileError as e:
        print(f"Compilation error: {e}")
        return False
    except Exception as e:
        print(f"Unexpected error: {e}")
        return False

if __name__ == "__main__":
    success = precompile_module()
    sys.exit(0 if success else 1)