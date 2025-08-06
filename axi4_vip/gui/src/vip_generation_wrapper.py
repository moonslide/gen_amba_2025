#!/usr/bin/env python3
"""
VIP Environment Wrapper - Automatically handles large matrices
"""

import os
import sys
sys.path.insert(0, os.path.dirname(__file__))

# Import the original module
from vip_gui_integration import VIPGenerationThread as OriginalThread

class VIPGenerationThreadWrapper(OriginalThread):
    """Wrapper that automatically detects and handles large matrices"""
    
    def run(self):
        """Override run to check matrix size first"""
        try:
            # Get configuration
            config = self.gui_integration.gui.current_config
            num_masters = len(config.masters) if hasattr(config, 'masters') and config.masters else 0
            num_slaves = len(config.slaves) if hasattr(config, 'slaves') and config.slaves else 0
            matrix_size = num_masters * num_slaves
            
            print(f"[VIP Wrapper] Detected {num_masters}x{num_slaves} matrix (size: {matrix_size})")
            
            # For large matrices, set environment variables to use ultrathin mode
            if matrix_size > 49:  # 7x7 or larger
                print(f"[VIP Wrapper] Large matrix detected! Enabling ultrathin mode...")
                os.environ['VIP_DEFER_IMPORTS'] = 'true'
                os.environ['VIP_USE_FINAL'] = 'true'
                os.environ['VIP_FAST_GEN'] = 'true'
                os.environ['VIP_LAZY_LOAD'] = 'true'
                os.environ['VIP_SKIP_COMPONENT_INIT'] = 'true'
                
                # Import and use ultrathin version
                from vip_gui_integration_ultrathin_final import VIPGenerationThreadUltraThin
                
                # Create ultrathin thread
                ultrathin_thread = VIPGenerationThreadUltraThin(
                    gui_integration=self.gui_integration,
                    output_dir=self.output_dir,
                    rtl_mode=self.rtl_mode,
                    rtl_source=getattr(self, 'rtl_source', None),
                    rtl_folder=getattr(self, 'rtl_folder', None),
                    status_var=getattr(self, 'status_var', None),
                    status_label=getattr(self, 'status_label', None),
                    progress_callback=getattr(self, 'progress_callback', None)
                )
                
                # Copy state
                for attr in ['progress_var', 'total_steps', 'current_step', 'cancelled', 'completed']:
                    if hasattr(self, attr):
                        setattr(ultrathin_thread, attr, getattr(self, attr))
                
                # Run ultrathin version
                ultrathin_thread.run()
                
                # Copy results back
                self.completed = ultrathin_thread.completed
                self.result_path = getattr(ultrathin_thread, 'result_path', None)
                self.error_message = getattr(ultrathin_thread, 'error_message', None)
                
            else:
                # Normal execution for smaller matrices
                super().run()
                
        except Exception as e:
            print(f"[VIP Wrapper] Error: {e}")
            import traceback
            traceback.print_exc()
            # Fall back to original
            super().run()

# Replace the original class
VIPGenerationThread = VIPGenerationThreadWrapper
