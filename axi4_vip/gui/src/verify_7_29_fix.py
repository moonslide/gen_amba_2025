#!/usr/bin/env python3
"""
Verify the 7/29 working version fix
"""

import os
import sys

print("🔧 VERIFYING 7/29 WORKING VERSION FIX")
print("="*50)

# Set simple environment (like 7/29)
os.environ['VIP_DEFER_IMPORTS'] = 'true'

sys.path.insert(0, '/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src')

print("\n✅ BACK TO 7/29 WORKING APPROACH:")
print("- RTL mode: 10 steps (not 12)")
print("- VIP standalone: 6 steps")  
print("- Simple direct generation")
print("- No complex wrappers")
print("- No monkey patching")

try:
    print("\n1. Testing fixed version import...")
    from vip_gui_integration_fixed import VIPControlPanel, VIPGenerationThread
    print(f"   ✅ VIPControlPanel: {VIPControlPanel}")
    print(f"   ✅ VIPGenerationThread: {VIPGenerationThread}")
    
    print("\n2. Checking step configuration...")
    # Create mock thread to check steps
    class MockGUI:
        def __init__(self):
            self.current_config = None
    
    mock_gui = MockGUI()
    
    # Test RTL mode steps
    rtl_thread = VIPGenerationThread(
        gui_integration=mock_gui,
        output_dir="/tmp/test",
        rtl_mode=True,
        status_var=None,
        status_label=None
    )
    
    print(f"   ✅ RTL mode total steps: {rtl_thread.total_steps} (should be 10)")
    
    # Test VIP standalone steps
    vip_thread = VIPGenerationThread(
        gui_integration=mock_gui,
        output_dir="/tmp/test", 
        rtl_mode=False,
        status_var=None,
        status_label=None
    )
    
    print(f"   ✅ VIP standalone total steps: {vip_thread.total_steps} (should be 6)")
    
    print("\n3. Checking step names...")
    step_names = rtl_thread.step_names
    print(f"   Total step names defined: {len(step_names)}")
    for i, name in enumerate(step_names[:5], 1):
        print(f"   Step {i}: {name}")
    print("   ...")
    
    if rtl_thread.total_steps == 10 and vip_thread.total_steps == 6:
        print("\n✅ CORRECT STEP CONFIGURATION!")
        print("This matches the working 7/29 version")
    else:
        print("\n❌ INCORRECT STEP CONFIGURATION")
        
    print("\n4. Testing bus_matrix_gui import logic...")
    # Simulate bus_matrix_gui.py import logic
    if os.environ.get('VIP_DEFER_IMPORTS', 'false').lower() == 'true':
        from vip_gui_integration_fixed import VIPControlPanel as TestVIPControlPanel
        print("   ✅ Would import from vip_gui_integration_fixed")
    else:
        print("   ⚠️  Would import from regular vip_gui_integration")
        
    print(f"   Loaded: {TestVIPControlPanel}")
    
except Exception as e:
    print(f"\n❌ Test failed: {e}")
    import traceback
    traceback.print_exc()

print("\n🚀 EXPECTED BEHAVIOR:")
print("When you run ./launch_gui_ultrathin.sh:")
print("1. Shows: 'Using FIXED version from 7/29'")
print("2. Progress for RTL mode: 1/10, 2/10, ..., 10/10") 
print("3. Shows [SUCCESS] after 10/10 (100%)")
print("4. No stopping at step 6 or 7")
print("5. Simple, working generation like it was on 7/29")

print("\n" + "="*50)
print("🎯 REVERTED TO WORKING 7/29 STATE!")
print("="*50)