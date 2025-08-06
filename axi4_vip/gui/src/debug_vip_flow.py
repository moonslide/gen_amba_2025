#!/usr/bin/env python3
"""Debug script to trace VIP generation flow"""

import os
import sys

# Add debug environment variables
os.environ['VIP_DEFER_IMPORTS'] = 'true'
os.environ['VIP_USE_FINAL'] = 'true'
os.environ['VIP_FAST_GEN'] = 'true'

print("=== VIP Generation Flow Debug ===")
print(f"VIP_DEFER_IMPORTS: {os.environ.get('VIP_DEFER_IMPORTS')}")
print(f"VIP_USE_FINAL: {os.environ.get('VIP_USE_FINAL')}")
print(f"VIP_FAST_GEN: {os.environ.get('VIP_FAST_GEN')}")

# Test which module gets imported
try:
    if os.environ.get('VIP_DEFER_IMPORTS', 'false').lower() == 'true':
        if os.environ.get('VIP_USE_FINAL', 'true').lower() == 'true':
            print("\n[INFO] Importing vip_gui_integration_ultrathin_final")
            from vip_gui_integration_ultrathin_final import VIPControlPanelUltraThin as VIPControlPanel
            from vip_gui_integration_ultrathin_final import VIPGenerationThreadUltraThin
            print("[SUCCESS] Imported final ultrathin version")
            print(f"VIPControlPanel module: {VIPControlPanel.__module__}")
            print(f"VIPGenerationThread module: {VIPGenerationThreadUltraThin.__module__}")
        else:
            print("\n[INFO] Importing vip_gui_integration_ultrathin")
            from vip_gui_integration_ultrathin import VIPControlPanelUltraThin as VIPControlPanel
    else:
        print("\n[INFO] Importing vip_gui_integration")
        from vip_gui_integration import VIPControlPanel
        
except Exception as e:
    print(f"\n[ERROR] Import failed: {e}")
    import traceback
    traceback.print_exc()

# Test wrapper import
try:
    print("\n[INFO] Testing wrapper import")
    from vip_environment_generator_wrapper_final import VIPEnvironmentGeneratorWrapperFinal
    print("[SUCCESS] Wrapper imported successfully")
    
    # Test instantiation
    class DummyConfig:
        addr_width = 32
        data_width = 64
        masters = [1, 2]
        slaves = [1, 2, 3]
    
    wrapper = VIPEnvironmentGeneratorWrapperFinal(
        gui_config=DummyConfig(),
        mode="rtl_integration",
        simulator="vcs",
        start_step=7,
        total_steps=12
    )
    print(f"[SUCCESS] Wrapper instantiated: start_step={wrapper.start_step}")
    
except Exception as e:
    print(f"\n[ERROR] Wrapper test failed: {e}")
    import traceback
    traceback.print_exc()

print("\n=== Debug Complete ===")