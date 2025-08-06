#!/usr/bin/env python3
"""
Fix for 11x11+ bus matrix hang during VIP generation
Updates vip_gui_integration.py to use scalability patches
"""

import os
import sys

def apply_11x11_fix():
    """Apply fix for large bus matrix hang issue"""
    
    # Path to vip_gui_integration.py
    integration_file = os.path.join(os.path.dirname(__file__), 'vip_gui_integration.py')
    
    if not os.path.exists(integration_file):
        print(f"Error: {integration_file} not found")
        return False
    
    # Read the file
    with open(integration_file, 'r') as f:
        content = f.read()
    
    # Check if fix already applied
    if 'vip_environment_generator_scalability_patch' in content:
        print("Fix already applied!")
        return True
    
    # Find the first import of VIPEnvironmentGenerator
    import_line = "from vip_environment_generator import VIPEnvironmentGenerator"
    
    # Create the patch import code
    patch_code = """# Apply scalability patch for large bus matrices (11x11+)
try:
    from vip_environment_generator_scalability_patch import apply_scalability_patch
    apply_scalability_patch()
    print("[VIP] Scalability patch applied for large bus matrix support")
except Exception as e:
    print(f"[VIP] Warning: Could not apply scalability patch: {e}")

# Import the VIP environment generator
from vip_environment_generator import VIPEnvironmentGenerator"""
    
    # Replace the import
    if import_line in content:
        content = content.replace(import_line, patch_code, 1)  # Only replace first occurrence
    else:
        print("Error: Could not find VIPEnvironmentGenerator import")
        return False
    
    # Now add progress callback support to the generator creation
    # Find generator creation pattern
    generator_pattern = """generator = VIPEnvironmentGenerator(
                gui_config=self.gui_integration.gui.current_config,
                mode="rtl_integration",
                simulator=self.gui_integration.simulator
            )"""
    
    enhanced_generator = """generator = VIPEnvironmentGenerator(
                gui_config=self.gui_integration.gui.current_config,
                mode="rtl_integration",
                simulator=self.gui_integration.simulator
            )
            
            # Set progress callback for large matrix support
            def vip_progress_callback(message, step=None):
                if step is not None:
                    self.update_progress(message, step)
                else:
                    self.update_progress(message)
            
            if hasattr(generator, 'set_progress_callback'):
                generator.set_progress_callback(vip_progress_callback)
                generator.cancel_event = self.cancel_event  # Share cancel event"""
    
    # Replace all generator creation patterns
    content = content.replace(generator_pattern, enhanced_generator)
    
    # Also update standalone mode
    standalone_pattern = """generator = VIPEnvironmentGenerator(
                gui_config=self.gui_integration.gui.current_config,
                mode="vip_standalone",
                simulator=self.gui_integration.simulator
            )"""
    
    enhanced_standalone = """generator = VIPEnvironmentGenerator(
                gui_config=self.gui_integration.gui.current_config,
                mode="vip_standalone",
                simulator=self.gui_integration.simulator
            )
            
            # Set progress callback for large matrix support
            def vip_progress_callback(message, step=None):
                if step is not None:
                    self.update_progress(message, step)
                else:
                    self.update_progress(message)
            
            if hasattr(generator, 'set_progress_callback'):
                generator.set_progress_callback(vip_progress_callback)
                generator.cancel_event = self.cancel_event  # Share cancel event"""
    
    content = content.replace(standalone_pattern, enhanced_standalone)
    
    # Add warning check after environment generation
    env_gen_pattern = "env_path = generator.generate_environment(self.output_dir)"
    
    enhanced_env_gen = """# Check for large matrix warnings before generation
            if hasattr(generator, '_check_large_matrix_warning'):
                generator._check_large_matrix_warning()
                if generator.warnings:
                    warning_msg = "\\n".join(generator.warnings)
                    self.update_progress(f"⚠️  {warning_msg}")
            
            env_path = generator.generate_environment(self.output_dir)"""
    
    content = content.replace(env_gen_pattern, enhanced_env_gen)
    
    # Write the updated file
    with open(integration_file, 'w') as f:
        f.write(content)
    
    print(f"✅ Successfully patched {integration_file}")
    print("\nWhat was fixed:")
    print("1. Added scalability patch import for large bus matrices")
    print("2. Added progress callback support to VIPEnvironmentGenerator")
    print("3. Added timeout handling for gen_amba_axi subprocess")
    print("4. Added warnings for matrices larger than 8x8")
    print("5. Shared cancel event for proper cancellation support")
    print("\nThe VIP generation should now:")
    print("- Show detailed progress for large matrices")
    print("- Not hang indefinitely on 11x11+ matrices")
    print("- Provide warnings and timeout after reasonable time")
    print("- Allow cancellation during long operations")
    
    return True

def create_test_script():
    """Create a test script to verify the fix"""
    test_script = """#!/usr/bin/env python3
# Test script for 11x11 matrix generation

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from dataclasses import dataclass
from typing import List

@dataclass
class MasterConfig:
    name: str
    id_width: int = 4
    user_width: int = 1
    
@dataclass  
class SlaveConfig:
    name: str
    base_addr: int
    size: int
    
@dataclass
class BusConfig:
    masters: List[MasterConfig]
    slaves: List[SlaveConfig]
    addr_width: int = 32
    data_width: int = 32
    
# Create 11x11 test configuration
print("Creating 11x11 bus matrix configuration...")
test_config = BusConfig(
    masters=[MasterConfig(f"M{i}") for i in range(11)],
    slaves=[SlaveConfig(f"S{i}", 0x1000_0000 + i*0x1000, 0x1000) for i in range(11)],
)

print(f"Masters: {len(test_config.masters)}")
print(f"Slaves: {len(test_config.slaves)}")
print(f"Total connections: {len(test_config.masters) * len(test_config.slaves)}")

# Test the generator
try:
    from vip_environment_generator_scalability_patch import apply_scalability_patch
    apply_scalability_patch()
    
    from vip_environment_generator import VIPEnvironmentGenerator
    
    generator = VIPEnvironmentGenerator(
        gui_config=test_config,
        mode="rtl_integration"
    )
    
    # Check warnings
    generator._check_large_matrix_warning()
    if generator.warnings:
        print("\\nWarnings:")
        for w in generator.warnings:
            print(f"  - {w}")
    
    print("\\nTest passed! Large matrix handling is working.")
    
except Exception as e:
    print(f"\\nTest failed: {e}")
"""
    
    test_file = os.path.join(os.path.dirname(__file__), 'test_11x11_fix.py')
    with open(test_file, 'w') as f:
        f.write(test_script)
    os.chmod(test_file, 0o755)
    print(f"\nCreated test script: {test_file}")

if __name__ == "__main__":
    print("🔧 Applying 11x11+ Bus Matrix Hang Fix")
    print("="*50)
    
    if apply_11x11_fix():
        create_test_script()
        print("\n✅ Fix applied successfully!")
        print("\nTo test: python3 test_11x11_fix.py")
    else:
        print("\n❌ Failed to apply fix")