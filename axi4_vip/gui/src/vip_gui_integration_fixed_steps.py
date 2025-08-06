#!/usr/bin/env python3
"""
Fixed VIP GUI Integration - Properly handles steps 7-10
"""

import os
import time

def apply_step_fix():
    """Apply fix to make VIP generation continue from step 6 to 7-10"""
    
    print("🔧 APPLYING STEP 6→7 AUTO-PROGRESSION FIX")
    print("="*50)
    
    # Read the current vip_gui_integration.py
    file_path = '/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_gui_integration.py'
    
    with open(file_path, 'r') as f:
        content = f.read()
    
    # Find and replace the problematic section
    old_code = """            # Generate the environment
            env_path = generator.generate_environment(self.output_dir)
            
            # Handle RTL integration"""
    
    new_code = """            # Generate the environment with progress tracking for steps 7-10
            # Step 6 is already done, now continue to 7
            if not self.update_progress("Starting environment generation", 7):
                return None
            
            # Run the generator (does the actual work)
            env_path = generator.generate_environment(self.output_dir)
            
            # Update progress for remaining steps since generator doesn't report progress
            if env_path:
                # Simulate progress for steps 8-10
                time.sleep(0.2)  # Brief pause for visual feedback
                if not self.update_progress("Generating test and verification files", 8):
                    return None
                    
                time.sleep(0.2)
                if not self.update_progress("Generating simulation infrastructure", 9):
                    return None
                    
                time.sleep(0.2)
                if not self.update_progress("Finalizing VIP environment", 10):
                    return None
            
            # Handle RTL integration"""
    
    if old_code in content:
        content = content.replace(old_code, new_code)
        
        # Add import for time if not present
        if "import time" not in content:
            # Add after other imports
            import_pos = content.find("import threading")
            if import_pos != -1:
                content = content[:import_pos] + "import time\n" + content[import_pos:]
        
        # Write back
        with open(file_path, 'w') as f:
            f.write(content)
            
        print("✅ Applied fix to vip_gui_integration.py")
        print("\nChanges made:")
        print("1. Added progress update for step 7 after step 6")
        print("2. Added manual progress updates for steps 8-10")
        print("3. Added brief delays for visual feedback")
        print("\nNow the progress will go: 6/10 → 7/10 → 8/10 → 9/10 → 10/10")
        
    else:
        print("❌ Could not find the target code to replace")
        print("The file may have already been modified")
        
    print("\n" + "="*50)

if __name__ == "__main__":
    apply_step_fix()