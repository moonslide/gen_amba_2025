#!/usr/bin/env python3
"""
Verify ultrathin setup and identify why GUI stops at step 7
"""

import os
import sys

print("🔍 VERIFYING ULTRATHIN SETUP")
print("="*50)

# Check environment variables
print("\n1. Environment Variables:")
env_vars = ['VIP_DEFER_IMPORTS', 'VIP_USE_FINAL', 'VIP_FAST_GEN', 'VIP_LAZY_LOAD', 'VIP_SKIP_COMPONENT_INIT']
for var in env_vars:
    value = os.environ.get(var, 'not set')
    print(f"   {var}: {value}")

# Check launch script
print("\n2. Launch Script Configuration:")
launch_script = '/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/scripts/launch_gui_ultrathin.sh'
if os.path.exists(launch_script):
    print(f"   ✅ {launch_script} exists")
    with open(launch_script, 'r') as f:
        content = f.read()
        if 'VIP_USE_FINAL=true' in content:
            print("   ✅ VIP_USE_FINAL=true is set")
        else:
            print("   ❌ VIP_USE_FINAL=true is NOT set")
else:
    print(f"   ❌ {launch_script} not found")

# Check imports
print("\n3. Import Chain:")
sys.path.insert(0, '/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src')

# Simulate ultrathin environment
os.environ['VIP_DEFER_IMPORTS'] = 'true'
os.environ['VIP_USE_FINAL'] = 'true'

try:
    # Check bus_matrix_gui import logic
    print("   Checking bus_matrix_gui.py import logic...")
    with open('/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/bus_matrix_gui.py', 'r') as f:
        lines = f.readlines()
        
    in_vip_section = False
    for i, line in enumerate(lines[1190:1220], 1190):
        if 'VIP_DEFER_IMPORTS' in line:
            in_vip_section = True
        if in_vip_section and 'import' in line:
            print(f"   Line {i}: {line.strip()}")
            
    # Try importing
    print("\n   Testing import...")
    from vip_gui_integration_ultrathin_final import (
        VIPControlPanelUltraThin,
        VIPGenerationThreadUltraThin,
        patched_update_progress
    )
    print("   ✅ Successfully imported ultrathin final version")
    
    # Check if patch is applied
    from vip_gui_integration import VIPGenerationThread
    if VIPGenerationThread.update_progress.__name__ == 'patched_update_progress':
        print("   ✅ update_progress is patched")
    else:
        print("   ❌ update_progress is NOT patched")
        
    # Check wrapper
    from vip_environment_generator_wrapper_final import VIPEnvironmentGeneratorWrapperFinal
    print("   ✅ Wrapper final imported successfully")
    
except Exception as e:
    print(f"   ❌ Import failed: {e}")
    import traceback
    traceback.print_exc()

print("\n4. Potential Issues:")
print("   If generation stops at step 7/12:")
print("   - The GUI thread might be terminating early")
print("   - The wrapper progress callback might not be connected properly")
print("   - There might be an exception in the wrapper that's being silently caught")
print("   - The parent VIPGenerationThread might be interfering")

print("\n5. Debug Commands:")
print("   To see full debug output when running GUI:")
print("   $ cd /home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/scripts")
print("   $ ./launch_gui_ultrathin.sh 2>&1 | tee debug_output.log")
print("   Then search for:")
print("   - 'ULTRATHIN FINAL'")
print("   - 'WRAPPER FINAL'") 
print("   - 'Skipping premature'")
print("   - 'ERROR'")

print("\n" + "="*50)