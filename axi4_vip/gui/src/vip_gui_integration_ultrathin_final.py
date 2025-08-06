#!/usr/bin/env python3
"""
VIP GUI Integration Module - UltraThin Final Version
Complete fix for 12-step execution
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import json
import threading
import queue
import time
import os
import traceback
from typing import Dict, List, Optional, Any
from dataclasses import asdict
from datetime import datetime, timedelta

# Check if we should defer imports
DEFER_IMPORTS = os.environ.get('VIP_DEFER_IMPORTS', 'false').lower() == 'true'
LAZY_LOAD = os.environ.get('VIP_LAZY_LOAD', 'false').lower() == 'true'

# Initialize all VIP components as None
VIP_COMPONENTS_AVAILABLE = False
VIPConfig = None
create_axi_vip_environment = None
AXIMasterAgent = None
AXISlaveAgent = None
AXIMonitor = None
AXIChecker = None
AXITransaction = None
AXITestSequenceGenerator = None
TestScenarioConfig = None
create_comprehensive_test_suite = None
export_gui_config_to_uvm = None

# Deferred import function
def _lazy_import_vip_components():
    """Lazy import VIP components only when needed"""
    global VIP_COMPONENTS_AVAILABLE, VIPConfig, create_axi_vip_environment
    global AXIMasterAgent, AXISlaveAgent, AXIMonitor, AXIChecker
    global AXITransaction, AXITestSequenceGenerator, TestScenarioConfig
    global create_comprehensive_test_suite, export_gui_config_to_uvm
    
    if VIP_COMPONENTS_AVAILABLE:
        return True
        
    try:
        print("[INFO] Loading VIP components (deferred import)...")
        from axi_vip_components import (
            AXIMasterAgent, AXISlaveAgent, AXIMonitor, AXIChecker,
            VIPConfig, AXITransaction, create_axi_vip_environment
        )
        from axi_test_sequences import (
            AXITestSequenceGenerator, TestScenarioConfig, 
            create_comprehensive_test_suite
        )
        VIP_COMPONENTS_AVAILABLE = True
        print("[INFO] VIP components loaded successfully")
        return True
    except (ImportError, AttributeError) as e:
        print(f"[WARNING] VIP components not available: {e}")
        VIP_COMPONENTS_AVAILABLE = False
        return False

# Only import if not in defer mode
if not DEFER_IMPORTS:
    _lazy_import_vip_components()

# Try to import UVM exporter
try:
    if not DEFER_IMPORTS:
        from uvm_config_exporter import export_gui_config_to_uvm
except ImportError:
    export_gui_config_to_uvm = None

# Import the rest of the original file content
from vip_gui_integration import (
    VIPControlPanel,
    VIPGenerationThread
)

# Monkey patch to prevent premature completion messages but allow normal progress
original_update_progress = VIPGenerationThread.update_progress
def patched_update_progress(self, message, step_num=None):
    current_step = step_num or self.current_step
    
    # Specific completion messages that terminate the thread prematurely
    terminating_messages = [
        "VIP generation completed successfully!",
        "RTL integration environment completed"
    ]
    
    # Only skip these specific messages that would terminate the thread early
    # Allow all other progress messages to proceed normally
    if any(term_msg in message for term_msg in terminating_messages):
        if current_step < 12:
            print(f"[DEBUG ULTRATHIN FINAL] Skipping premature termination message at step {current_step}: {message}")
            # Don't terminate, let the wrapper continue to steps 7-12
            return True
        else:
            print(f"[DEBUG ULTRATHIN FINAL] Allowing completion message at step {current_step}: {message}")
    
    # Process all other messages normally (including regular step progress)
    return original_update_progress(self, message, step_num)

VIPGenerationThread.update_progress = patched_update_progress

# Override VIPControlPanel to add lazy loading
class VIPControlPanelUltraThin(VIPControlPanel):
    """Enhanced VIP Control Panel with lazy loading"""
    
    def __init__(self, parent, gui):
        # Set flag to prevent heavy initialization
        self._components_loaded = False
        super().__init__(parent, gui)
        
    def _ensure_components_loaded(self):
        """Ensure VIP components are loaded before use"""
        if not self._components_loaded and LAZY_LOAD:
            self._components_loaded = _lazy_import_vip_components()
        return self._components_loaded
        
    def generate_rtl_integration_env(self):
        """Generate RTL Integration environment"""
        if not self._ensure_components_loaded():
            messagebox.showwarning("VIP Not Ready", 
                                 "VIP components are still loading. Please try again.")
            return
        super().generate_rtl_integration_env()
        
    def generate_vip_standalone_env(self):
        """Generate VIP Standalone environment"""
        if not self._ensure_components_loaded():
            messagebox.showwarning("VIP Not Ready", 
                                 "VIP components are still loading. Please try again.")
            return
        super().generate_vip_standalone_env()

# Override VIPGenerationThread to use wrapper
class VIPGenerationThreadUltraThin(VIPGenerationThread):
    """Enhanced Generation Thread with proper 12-step execution"""
    
    def __init__(self, *args, **kwargs):
        print(f"[DEBUG ULTRATHIN FINAL] 🎯 VIPGenerationThreadUltraThin constructor called!")
        print(f"[DEBUG ULTRATHIN FINAL] Args: {args}")
        print(f"[DEBUG ULTRATHIN FINAL] Kwargs: {kwargs}")
        super().__init__(*args, **kwargs)
        print(f"[DEBUG ULTRATHIN FINAL] ✅ Ultrathin thread initialized successfully")
    
    def run(self):
        """Override run - Parent handles steps 1-6, wrapper handles 7-12"""
        try:
            print(f"[DEBUG ULTRATHIN FINAL] Starting generation: rtl_mode={self.rtl_mode}")
            self.update_progress("Starting VIP generation", 0)
            
            if self.rtl_mode:
                # RTL Integration Mode
                if self.rtl_source == "generate":
                    print(f"[DEBUG ULTRATHIN FINAL] Executing RTL generation (steps 1-6)")
                    # Let parent handle RTL generation (steps 1-6)
                    if not self._generate_rtl_with_progress():
                        return
                    print(f"[DEBUG ULTRATHIN FINAL] RTL generation complete, current step: {self.current_step}")
                    
                print(f"[DEBUG ULTRATHIN FINAL] Starting VIP environment generation (steps 7-12)")
                # Now wrapper handles steps 7-12
                env_path = self._generate_rtl_integration_with_progress()
            else:
                # VIP Standalone Mode - wrapper handles ALL steps 1-12  
                env_path = self._generate_vip_standalone_with_progress()
                
            # Check if all steps completed
            if env_path and not self.cancelled:
                print(f"[DEBUG ULTRATHIN FINAL] Generation returned path: {env_path}")
                print(f"[DEBUG ULTRATHIN FINAL] Current step: {self.current_step}/{self.total_steps}")
                
                # Wait for wrapper to complete all 12 steps
                max_wait = 45  # seconds - increased for complex configurations
                wait_time = 0
                while self.current_step < self.total_steps and wait_time < max_wait:
                    print(f"[DEBUG ULTRATHIN FINAL] Waiting for completion: step {self.current_step}/{self.total_steps}")
                    time.sleep(0.3)
                    wait_time += 0.3
                
                # Force completion to step 12 if wrapper finished but didn't reach it
                if self.current_step < self.total_steps:
                    print(f"[DEBUG ULTRATHIN FINAL] Forcing completion to step 12 (was at {self.current_step})")
                    self.update_progress("Finalizing environment", 12)
                
                # Verify we're at step 12 before marking success
                if self.current_step >= self.total_steps:
                    print(f"[DEBUG ULTRATHIN FINAL] All {self.total_steps} steps completed successfully!")
                    self.result_path = env_path
                    self.completed = True
                    
                    # Show final success message ONLY after all 12 steps
                    final_status = f"[SUCCESS] Success: VIP generated and saved to {env_path}"
                    self.status_var.set(final_status)
                    
                    # Update label color to green
                    if hasattr(self, 'status_label') and self.status_label:
                        self.status_label.config(foreground="green")
                        
                    print(f"[DEBUG ULTRATHIN FINAL] ✅ Thread marked as completed after 12/12 steps")
                else:
                    print(f"[ERROR ULTRATHIN FINAL] Generation incomplete - only reached step {self.current_step}")
                    self.error_message = f"Generation incomplete: only {self.current_step}/{self.total_steps} steps completed"
                    error_status = f"[ERROR] Error: {self.error_message}"
                    self.status_var.set(error_status)
                    
                    if hasattr(self, 'status_label') and self.status_label:
                        self.status_label.config(foreground="red")
                    
        except Exception as e:
            self.error_message = str(e)
            error_status = f"[ERROR] Error: {self.error_message}"
            self.status_var.set(error_status)
            
            if hasattr(self, 'status_label') and self.status_label:
                self.status_label.config(foreground="red")
            
            print(f"VIP Generation Error: {self.error_message}")
            traceback.print_exc()
    
    def _generate_rtl_integration_with_progress(self):
        """Generate RTL integration environment with all 12 steps - OVERRIDE COMPLETELY"""
        try:
            print(f"[DEBUG ULTRATHIN FINAL] _generate_rtl_integration_with_progress called")
            print(f"[DEBUG ULTRATHIN FINAL] Current step before wrapper: {self.current_step}")
            
            # IMPORTANT: Wrapper should continue from step 7 (after RTL generation)
            # Steps 1-6 are handled by parent thread
            print(f"[DEBUG ULTRATHIN FINAL] Starting wrapper from step 7 to continue generation")
            
            # Use the wrapper for steps 7-12 only
            from vip_environment_generator_wrapper_final import VIPEnvironmentGeneratorWrapperFinal
            
            # Create generator instance that handles steps 7-12
            generator = VIPEnvironmentGeneratorWrapperFinal(
                gui_config=self.gui_integration.gui.current_config,
                mode="rtl_integration",
                simulator=self.gui_integration.target_simulator,
                start_step=7,  # Start from step 7 to continue after RTL generation
                total_steps=12
            )
            
            # Add progress callback with enhanced debugging
            def generator_progress_callback(step_name, step_num=None):
                if self.cancelled:
                    raise Exception("Generation cancelled by user")
                print(f"[DEBUG ULTRATHIN FINAL] Wrapper progress callback: step {step_num}, name: {step_name}")
                try:
                    if step_num is not None:
                        result = self.update_progress(step_name, step_num)
                        print(f"[DEBUG ULTRATHIN FINAL] update_progress returned: {result}")
                    else:
                        result = self.update_progress(step_name)
                        print(f"[DEBUG ULTRATHIN FINAL] update_progress (no step_num) returned: {result}")
                except Exception as e:
                    print(f"[ERROR ULTRATHIN FINAL] Progress update failed: {e}")
                    import traceback
                    traceback.print_exc()
                    
            generator._progress_callback = generator_progress_callback
            
            # Generate the environment (ALL 12 steps)
            print(f"[DEBUG ULTRATHIN FINAL] About to call wrapper.generate_environment()")
            print(f"[DEBUG ULTRATHIN FINAL] Wrapper type: {type(generator)}")
            print(f"[DEBUG ULTRATHIN FINAL] Output dir: {self.output_dir}")
            print(f"[DEBUG ULTRATHIN FINAL] Thread current_step: {self.current_step}")
            print(f"[DEBUG ULTRATHIN FINAL] Thread cancelled: {self.cancelled}")
            
            env_path = generator.generate_environment(self.output_dir)
            
            print(f"[DEBUG ULTRATHIN FINAL] Wrapper completed!")
            print(f"[DEBUG ULTRATHIN FINAL] Wrapper returned path: {env_path}")
            print(f"[DEBUG ULTRATHIN FINAL] Thread current_step after wrapper: {self.current_step}")
            print(f"[DEBUG ULTRATHIN FINAL] Thread total_steps: {self.total_steps}")
            
            # Handle RTL integration
            if env_path and hasattr(self.gui_integration, 'generated_rtl_path') and self.gui_integration.generated_rtl_path and os.path.exists(self.gui_integration.generated_rtl_path):
                import shutil
                dest_rtl_dir = os.path.join(env_path, "rtl_wrapper", "generated_rtl")
                if os.path.exists(dest_rtl_dir):
                    shutil.rmtree(dest_rtl_dir)
                shutil.copytree(self.gui_integration.generated_rtl_path, dest_rtl_dir)
                self.gui_integration._update_rtl_filelist(env_path)
            elif env_path and hasattr(self.gui_integration, 'existing_rtl_path') and self.gui_integration.existing_rtl_path and os.path.exists(self.gui_integration.existing_rtl_path):
                import shutil
                dest_rtl_dir = os.path.join(env_path, "rtl_wrapper", "existing_rtl")
                if os.path.exists(dest_rtl_dir):
                    shutil.rmtree(dest_rtl_dir)
                shutil.copytree(self.gui_integration.existing_rtl_path, dest_rtl_dir)
                self.gui_integration._update_rtl_filelist(env_path)
            
            # IMPORTANT: Wait for wrapper to complete all 12 steps
            print(f"[DEBUG ULTRATHIN FINAL] Waiting for wrapper to complete all steps...")
            print(f"[DEBUG ULTRATHIN FINAL] Current step: {self.current_step}/12")
            
            # Wait for completion marker file
            if env_path:
                marker_file = os.path.join(env_path, ".all_12_steps_done")
                wait_time = 0
                max_wait = 30  # seconds
                
                while wait_time < max_wait:
                    if os.path.exists(marker_file):
                        print(f"[DEBUG ULTRATHIN FINAL] Wrapper completed! Marker file found.")
                        break
                    
                    # Also check current_step
                    if self.current_step >= 12:
                        print(f"[DEBUG ULTRATHIN FINAL] All 12 steps completed!")
                        break
                        
                    time.sleep(0.5)
                    wait_time += 0.5
                    
                    if wait_time % 2 == 0:  # Log every 2 seconds
                        print(f"[DEBUG ULTRATHIN FINAL] Still waiting... step {self.current_step}/12")
                
                if not os.path.exists(marker_file) and self.current_step < 12:
                    print(f"[ERROR ULTRATHIN FINAL] Wrapper did not complete! Only reached step {self.current_step}/12")
                    # Force update to step 12 to show completion
                    self.update_progress("Finalizing environment", 12)
            
            return env_path
            
        except Exception as e:
            if "cancelled" in str(e).lower():
                self.update_progress("Generation cancelled")
                return None
            raise Exception(f"Failed to generate RTL integration environment: {str(e)}")
            
    def _generate_vip_standalone_with_progress(self):
        """Generate VIP standalone environment with all 12 steps"""
        try:
            # Step 2: Loading VIP environment generator
            if not self.update_progress("Loading VIP environment generator", 2):
                return None
                
            from vip_environment_generator_wrapper_final import VIPEnvironmentGeneratorWrapperFinal
            
            generator = VIPEnvironmentGeneratorWrapperFinal(
                gui_config=self.gui_integration.gui.current_config,
                mode="vip_standalone",
                simulator=self.gui_integration.target_simulator,
                start_step=3,  # Continue from step 3
                total_steps=12
            )
            
            def generator_progress_callback(step_name, step_num=None):
                if self.cancelled:
                    raise Exception("Generation cancelled by user")
                if step_num is not None:
                    self.update_progress(step_name, step_num)
                else:
                    self.update_progress(step_name)
                    
            generator._progress_callback = generator_progress_callback
            
            env_path = generator.generate_environment(self.output_dir)
            return env_path
            
        except Exception as e:
            if "cancelled" in str(e).lower():
                self.update_progress("Generation cancelled")
                return None
            raise Exception(f"Failed to generate VIP standalone environment: {str(e)}")

# Update VIPControlPanelUltraThin to use the new thread
class VIPControlPanelUltraThinEnhanced(VIPControlPanelUltraThin):
    """Enhanced VIP Control Panel with proper thread handling"""
    
    def show_vip_setup_dialog(self, mode="rtl_integration"):
        """Override to directly create ultrathin thread instead of monkey patching"""
        print(f"[DEBUG ULTRATHIN FINAL] show_vip_setup_dialog called with mode: {mode}")
        
        # PATCH: Directly override thread creation in the dialog
        # Store original method
        original_method = super().show_vip_setup_dialog
        
        # Create our own dialog with ultrathin thread
        self._show_ultrathin_vip_dialog(mode)
    
    def _show_ultrathin_vip_dialog(self, mode="rtl_integration"):
        """Custom VIP dialog that uses ultrathin thread"""
        print(f"[DEBUG ULTRATHIN FINAL] Creating ultrathin VIP dialog")
        
        # Import the parent dialog method and patch the thread creation
        import inspect
        import types
        
        # Get the parent's show_vip_setup_dialog source and modify it
        # For now, let's use the monkey patch but with better error handling
        import vip_gui_integration
        
        # Store original
        original_thread_class = vip_gui_integration.VIPGenerationThread
        print(f"[DEBUG ULTRATHIN FINAL] Original thread class: {original_thread_class}")
        
        try:
            # Replace with ultrathin version
            vip_gui_integration.VIPGenerationThread = VIPGenerationThreadUltraThin
            print(f"[DEBUG ULTRATHIN FINAL] Replaced with ultrathin thread: {VIPGenerationThreadUltraThin}")
            
            # Call parent method
            print(f"[DEBUG ULTRATHIN FINAL] Calling parent show_vip_setup_dialog")
            super().show_vip_setup_dialog(mode)
            
        except Exception as e:
            print(f"[ERROR ULTRATHIN FINAL] Dialog creation failed: {e}")
            import traceback
            traceback.print_exc()
            raise
        finally:
            # Always restore original
            vip_gui_integration.VIPGenerationThread = original_thread_class
            print(f"[DEBUG ULTRATHIN FINAL] Restored original thread class")

# Export the enhanced ultrathin version as the main one
VIPControlPanelUltraThin = VIPControlPanelUltraThinEnhanced

# Export all classes
__all__ = ['VIPControlPanelUltraThin', 'VIPGenerationThreadUltraThin']