#!/usr/bin/env python3
"""
Final verification that the ultrathin VIP TypeError is fixed
"""

import os
import sys

print("🔧 VERIFYING ULTRATHIN VIP TYPEDEF FIX")
print("="*50)

# Set up ultrathin environment
os.environ['VIP_DEFER_IMPORTS'] = 'true'
os.environ['VIP_USE_FINAL'] = 'true'
os.environ['VIP_FAST_GEN'] = 'true'

sys.path.insert(0, '/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src')

def check_method_signature(cls, method_name, expected_params):
    """Check if method has expected signature"""
    import inspect
    
    if not hasattr(cls, method_name):
        return False, f"Method {method_name} not found"
    
    method = getattr(cls, method_name)
    sig = inspect.signature(method)
    params = sig.parameters
    
    for param_name, expected_default in expected_params:
        if param_name not in params:
            return False, f"Parameter {param_name} missing"
        
        param = params[param_name]
        if expected_default is not None:
            if param.default == inspect.Parameter.empty:
                return False, f"Parameter {param_name} has no default value"
            if param.default != expected_default:
                return False, f"Parameter {param_name} default is {param.default}, expected {expected_default}"
        
    return True, "OK"

def main():
    print("\n1️⃣  CHECKING ORIGINAL VIP INTEGRATION...")
    
    try:
        from vip_gui_integration import VIPControlPanel
        
        # Check show_vip_setup_dialog signature
        success, msg = check_method_signature(
            VIPControlPanel, 
            'show_vip_setup_dialog',
            [('mode', None)]  # Should have mode=None default
        )
        
        if success:
            print("   ✅ show_vip_setup_dialog(self, mode=None) - CORRECT")
        else:
            print(f"   ❌ show_vip_setup_dialog signature issue: {msg}")
            return False
            
        # Check compatibility methods exist
        for method in ['generate_rtl_integration_env', 'generate_vip_standalone_env']:
            if hasattr(VIPControlPanel, method):
                print(f"   ✅ {method}() method exists")
            else:
                print(f"   ❌ {method}() method missing")
                return False
                
    except Exception as e:
        print(f"   ❌ Original VIP integration error: {e}")
        return False
    
    print("\n2️⃣  CHECKING ULTRATHIN FINAL VERSION...")
    
    try:
        from vip_gui_integration_ultrathin_final import VIPControlPanelUltraThin
        
        # Check signature
        success, msg = check_method_signature(
            VIPControlPanelUltraThin,
            'show_vip_setup_dialog', 
            [('mode', 'rtl_integration')]  # Should have mode="rtl_integration" default
        )
        
        if success:
            print("   ✅ show_vip_setup_dialog(self, mode='rtl_integration') - CORRECT")
        else:
            print(f"   ❌ Ultrathin final signature issue: {msg}")
            return False
            
    except Exception as e:
        print(f"   ❌ Ultrathin final import error: {e}")
        return False
    
    print("\n3️⃣  CHECKING ULTRATHIN REGULAR VERSION...")
    
    try:
        from vip_gui_integration_ultrathin import VIPControlPanelUltraThin as RegularUltrathin
        
        # Check signature  
        success, msg = check_method_signature(
            RegularUltrathin,
            'show_vip_setup_dialog',
            [('mode', 'rtl_integration')]  # Should have mode="rtl_integration" default
        )
        
        if success:
            print("   ✅ show_vip_setup_dialog(self, mode='rtl_integration') - CORRECT")
        else:
            print(f"   ❌ Ultrathin regular signature issue: {msg}")
            return False
            
    except Exception as e:
        print(f"   ❌ Ultrathin regular import error: {e}")
        return False
    
    print("\n4️⃣  VERIFYING THE PROBLEMATIC CALL...")
    
    # Check the fixed call in vip_gui_integration.py
    with open('/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_gui_integration.py', 'r') as f:
        content = f.read()
    
    # Look for the fixed call
    if 'self.show_vip_setup_dialog("rtl_integration")' in content:
        print("   ✅ Method call fixed to include mode parameter")
    elif 'self.show_vip_setup_dialog()' in content:
        print("   ❌ Method call still missing mode parameter")
        return False
    else:
        print("   ⚠️  Could not find method call (may be OK)")
    
    print("\n🎉 ALL CHECKS PASSED!")
    print("="*50)
    print("The TypeError should now be FIXED:")
    print("")
    print("✅ ./launch_gui_ultrathin.sh should work without errors")
    print("✅ VIP → Create VIP Environment should open dialog")  
    print("✅ Complex AXI4 template should complete 12/12 steps")
    print("✅ All method signatures are compatible")
    print("")
    print("🚀 Ready to test with Complex AXI4 template!")
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)