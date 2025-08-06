#!/usr/bin/env python3
"""
Debug script to test wrapper execution
"""

import os
import sys
import time

# Set up ultrathin environment
os.environ['VIP_DEFER_IMPORTS'] = 'true'
os.environ['VIP_USE_FINAL'] = 'true'
os.environ['VIP_FAST_GEN'] = 'true'

sys.path.insert(0, '/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src')

print("=== DEBUGGING WRAPPER EXECUTION ===")

class MockConfig:
    def __init__(self):
        self.masters = [1, 2, 3, 4, 5, 6, 7, 8]  # 8 masters
        self.slaves = [1, 2, 3, 4, 5, 6, 7, 8]   # 8 slaves  
        self.data_width = 128
        self.addr_width = 40

def mock_progress_callback(step_name, step_num=None):
    print(f"[MOCK PROGRESS] Step {step_num}: {step_name}")

try:
    print("\n1. Testing wrapper import...")
    from vip_environment_generator_wrapper_final import VIPEnvironmentGeneratorWrapperFinal
    print("✅ Wrapper imported successfully")
    
    print("\n2. Creating wrapper instance...")
    mock_config = MockConfig()
    wrapper = VIPEnvironmentGeneratorWrapperFinal(
        gui_config=mock_config,
        mode="rtl_integration", 
        simulator="vcs",
        start_step=1,
        total_steps=12
    )
    print("✅ Wrapper instance created")
    
    print("\n3. Setting progress callback...")
    wrapper._progress_callback = mock_progress_callback
    print("✅ Progress callback set")
    
    print("\n4. Testing wrapper execution...")
    output_dir = "/tmp/debug_vip_test"
    os.makedirs(output_dir, exist_ok=True)
    
    print("🚀 Starting wrapper.generate_environment()...")
    start_time = time.time()
    
    env_path = wrapper.generate_environment(output_dir)
    
    end_time = time.time()
    print(f"⏱️  Execution time: {end_time - start_time:.2f} seconds")
    
    if env_path:
        print(f"✅ Wrapper completed successfully!")
        print(f"📁 Environment path: {env_path}")
        
        # Check if all step files were created
        print("\n5. Checking generated files...")
        for step in range(1, 13):
            step_file = os.path.join(env_path, f"rtl_generation_step_{step}.txt")
            if os.path.exists(step_file):
                print(f"✅ Step {step} file exists")
            else:
                print(f"❌ Step {step} file missing")
                
        # Check final completion file
        completion_file = os.path.join(env_path, "generation_complete.txt")
        if os.path.exists(completion_file):
            print("✅ Generation completion file exists")
            with open(completion_file, 'r') as f:
                print(f"📄 Content: {f.read().strip()}")
        else:
            print("❌ Generation completion file missing")
            
    else:
        print("❌ Wrapper returned None - execution failed")
        
except Exception as e:
    print(f"❌ Test failed: {e}")
    import traceback
    traceback.print_exc()

print("\n" + "="*50)