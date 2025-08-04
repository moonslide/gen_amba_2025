#!/usr/bin/env python3
"""
Simple patch to enable enhanced VIP generation in existing GUI
"""

def apply_enhanced_vip_patch():
    """Apply patch to use enhanced VIP generator"""
    
    # Import both generators
    try:
        from vip_environment_generator import VIPEnvironmentGenerator
        from vip_environment_generator_enhanced import VIPEnvironmentGeneratorEnhanced
    except ImportError as e:
        print(f"Error importing generators: {e}")
        return False
    
    # Monkey patch all GUI modules
    import sys
    
    # List of modules that might use VIPEnvironmentGenerator
    gui_modules = [
        'bus_matrix_gui',
        'bus_matrix_gui_modern', 
        'vip_gui_integration',
        'vip_gui_integration_modern'
    ]
    
    patched_count = 0
    
    for module_name in gui_modules:
        if module_name in sys.modules:
            module = sys.modules[module_name]
            if hasattr(module, 'VIPEnvironmentGenerator'):
                # Replace the class
                module.VIPEnvironmentGenerator = VIPEnvironmentGeneratorEnhanced
                patched_count += 1
                print(f"Patched {module_name}")
            
            # Also check for any instances
            for attr_name in dir(module):
                attr = getattr(module, attr_name)
                if isinstance(attr, type) and issubclass(attr, VIPEnvironmentGenerator):
                    setattr(module, attr_name, VIPEnvironmentGeneratorEnhanced)
                    patched_count += 1
                    print(f"Patched {module_name}.{attr_name}")
    
    # Global replacement
    import builtins
    if hasattr(builtins, 'VIPEnvironmentGenerator'):
        builtins.VIPEnvironmentGenerator = VIPEnvironmentGeneratorEnhanced
        patched_count += 1
        print("Patched global VIPEnvironmentGenerator")
    
    print(f"Enhanced VIP patch applied successfully ({patched_count} replacements)")
    return True

# Auto-apply when imported
if __name__ != "__main__":
    apply_enhanced_vip_patch()
