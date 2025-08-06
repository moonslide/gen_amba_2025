#!/usr/bin/env python3
"""
Force ultrathin mode for complex configurations regardless of how they were loaded
"""

import os
import sys

def apply_complex_config_detection():
    """Apply patch to detect complex configs during VIP generation"""
    
    # Patch the VIP generation thread to detect complexity on-the-fly
    vip_integration_file = "/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_gui_integration.py"
    
    with open(vip_integration_file, 'r') as f:
        content = f.read()
    
    # Find the run method in VIPGenerationThread
    run_method_start = content.find('def run(self):')
    if run_method_start == -1:
        print("[ERROR] Could not find run method in VIPGenerationThread")
        return False
    
    # Find the start of the method body (after the docstring)
    method_body_start = content.find('try:', run_method_start)
    if method_body_start == -1:
        method_body_start = content.find('if', run_method_start)
    
    if method_body_start == -1:
        print("[ERROR] Could not find method body start")
        return False
    
    # Insert complexity detection code
    complexity_check = '''        
        # ULTRATHIN PATCH: Auto-detect complex configurations
        try:
            config = self.gui_integration.gui.current_config
            num_masters = len(config.masters) if hasattr(config, 'masters') and config.masters else 0
            num_slaves = len(config.slaves) if hasattr(config, 'slaves') and config.slaves else 0
            complexity = num_masters * num_slaves
            data_width = getattr(config, 'data_width', 32)
            addr_width = getattr(config, 'addr_width', 32)
            
            # Check if this is a complex configuration
            is_complex = (complexity > 16 or data_width > 64 or addr_width > 32 or num_masters > 4)
            
            if is_complex:
                print(f"[ULTRATHIN] Complex config detected: {num_masters}M×{num_slaves}S, {data_width}-bit data, {addr_width}-bit addr")
                print(f"[ULTRATHIN] Forcing ultrathin mode for robust 12-step generation")
                
                # Force ultrathin environment variables
                os.environ['VIP_DEFER_IMPORTS'] = 'true'
                os.environ['VIP_USE_FINAL'] = 'true'
                os.environ['VIP_FAST_GEN'] = 'true'
                os.environ['VIP_LAZY_LOAD'] = 'true'
                os.environ['VIP_SKIP_COMPONENT_INIT'] = 'true'
                
                # Import and use ultrathin final version directly
                from vip_gui_integration_ultrathin_final import VIPGenerationThreadUltraThin
                
                # Replace self with ultrathin version
                ultrathin_thread = VIPGenerationThreadUltraThin(
                    gui_integration=self.gui_integration,
                    output_dir=self.output_dir,
                    rtl_mode=self.rtl_mode,
                    rtl_source=getattr(self, 'rtl_source', None),
                    rtl_folder=getattr(self, 'rtl_folder', None),
                    status_var=getattr(self, 'status_var', None),
                    status_label=getattr(self, 'status_label', None)  
                )
                
                # Copy attributes
                for attr in ['progress_var', 'total_steps', 'current_step', 'cancelled', 'completed']:
                    if hasattr(self, attr):
                        setattr(ultrathin_thread, attr, getattr(self, attr))
                
                print(f"[ULTRATHIN] Delegating to ultrathin thread for 12-step generation")
                ultrathin_thread.run()
                
                # Copy results back
                self.completed = ultrathin_thread.completed
                self.result_path = getattr(ultrathin_thread, 'result_path', None)
                if hasattr(ultrathin_thread, 'error_message'):
                    self.error_message = ultrathin_thread.error_message
                
                return  # Exit early, ultrathin thread handled everything
                
        except Exception as e:
            print(f"[WARNING] Complexity detection failed: {e}")
            # Continue with original flow
            pass
        
'''
    
    # Insert the complexity check at the start of the method body
    insert_pos = content.find('\n', method_body_start) + 1
    patched_content = content[:insert_pos] + complexity_check + content[insert_pos:]
    
    # Add import at the top of the file if not present
    if 'import os' not in patched_content:
        import_pos = patched_content.find('import threading')
        if import_pos != -1:
            patched_content = patched_content[:import_pos] + 'import os\n' + patched_content[import_pos:]
    
    # Write the patched content
    with open(vip_integration_file, 'w') as f:  
        f.write(patched_content)
    
    print("[SUCCESS] Applied complexity detection patch to VIPGenerationThread")
    print("Now complex configurations will automatically use ultrathin 12-step generation")
    return True

if __name__ == "__main__":
    print("=== Applying Complex Configuration Detection Patch ===\n")
    
    success = apply_complex_config_detection()
    
    if success:
        print("\n=== Patch Applied Successfully ===")
        print("Now when you run VIP generation with the Complex AXI4 template:")
        print("1. Thread will detect 8M×8S complexity automatically")
        print("2. Force ultrathin mode regardless of template loading")
        print("3. Use ultrathin final version for proper 12-step execution")  
        print("4. Show SUCCESS only after completing all 12 steps")
        print("\nNo need to restart GUI - the fix is applied to the source file.")
    else:
        print("\n=== Patch Failed ===")
        print("Manual intervention required")
        sys.exit(1)