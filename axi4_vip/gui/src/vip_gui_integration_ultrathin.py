#!/usr/bin/env python3
"""
VIP GUI Integration Module - UltraThin Version
Fixes GUI hanging issue by deferring heavy imports
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
    SimulationStatus, 
    SimulationEngine,
    VIPIntegrationError,
    ResultsPanel,
    TestGeneratorPanel,
    SimulationControlPanel,
    VIPControlPanel,
    VIPGenerationThread
)

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
    """Enhanced Generation Thread with fast VIP generation"""
    
    def update_progress(self, step_name, step_number=None):
        """Override to add debug logging"""
        print(f"[DEBUG] update_progress called: step_name='{step_name}', step_number={step_number}, current_step={self.current_step}")
        result = super().update_progress(step_name, step_number)
        print(f"[DEBUG] After update: current_step={self.current_step}, total_steps={self.total_steps}")
        return result
    
    def run(self):
        """Override run to avoid extra progress update"""
        try:
            self.update_progress("Starting VIP generation", 0)
            
            if self.rtl_mode:
                # RTL Integration Mode
                if self.rtl_source == "generate":
                    # Use parent's RTL generation (handles steps 2-4)
                    # Import parent's method
                    parent_generate_rtl = VIPGenerationThread._generate_rtl_with_progress
                    if not parent_generate_rtl(self):
                        return
                    
                self.update_progress("Creating RTL integration environment", 5)
                env_path = self._generate_rtl_integration_with_progress()
            else:
                # VIP Standalone Mode
                self.update_progress("Creating VIP standalone environment", 1)
                env_path = self._generate_vip_standalone_with_progress()
                
            if env_path and not self.cancelled:
                # Only mark complete if we've actually reached step 12
                print(f"[DEBUG] Checking completion: current_step={self.current_step}, total_steps={self.total_steps}")
                if self.current_step >= self.total_steps:
                    self.result_path = env_path
                    self.completed = True
                    # Update final status in GUI thread
                    final_status = f"[SUCCESS] Success: VIP generated and saved to {env_path}"
                    self.status_var.set(final_status)
                else:
                    # Not all steps completed - this is an error
                    print(f"[ERROR] Generation returned but only completed {self.current_step}/{self.total_steps} steps!")
                    self.error_message = f"Generation incomplete: only {self.current_step}/{self.total_steps} steps completed"
                    error_status = f"[ERROR] Error: {self.error_message}"
                    self.status_var.set(error_status)
                
                # Change status label color based on success/error
                def update_label_color():
                    if self.status_label:
                        if self.completed:
                            self.status_label.config(foreground="green")
                        else:
                            self.status_label.config(foreground="red")
                        
                # Schedule GUI update
                if hasattr(self.gui_integration, 'gui') and hasattr(self.gui_integration.gui, 'root'):
                    self.gui_integration.gui.root.after(0, update_label_color)
                    
        except Exception as e:
            self.error_message = str(e)
            error_status = f"[ERROR] Error: {self.error_message}"
            self.status_var.set(error_status)
            
            # Change status label color to red in GUI thread
            def update_label_color():
                if self.status_label:
                    self.status_label.config(foreground="red")
                    
            if hasattr(self.gui_integration, 'gui') and hasattr(self.gui_integration.gui, 'root'):
                self.gui_integration.gui.root.after(0, update_label_color)
            
            print(f"VIP Generation Error: {self.error_message}")
            import traceback
            traceback.print_exc()
    
    
    def _generate_rtl_integration_with_progress(self):
        """Generate RTL integration environment with progress updates"""
        try:
            if not self.update_progress("Loading VIP environment generator", 6):
                return None
                
            # Use the wrapper instead of direct import
            from vip_environment_generator_wrapper import VIPEnvironmentGenerator
            
            # Create generator instance with cancellation support
            generator = VIPEnvironmentGenerator(
                gui_config=self.gui_integration.gui.current_config,
                mode="rtl_integration",
                simulator=self.gui_integration.target_simulator
            )
            
            # Add progress callback to generator
            def generator_progress_callback(step_name, step_num=None):
                if self.cancelled:
                    raise Exception("Generation cancelled by user")
                # Map generator steps to our progress tracking
                print(f"[DEBUG] Progress callback: {step_name}, step_num={step_num}")
                if step_num is not None:
                    self.update_progress(step_name, step_num)
                else:
                    self.update_progress(step_name)
                    
            # Inject our progress callback
            generator._progress_callback = generator_progress_callback
            
            # Generate the environment
            print(f"[DEBUG] About to call generator.generate_environment")
            env_path = generator.generate_environment(self.output_dir)
            
            print(f"[DEBUG] Generation returned env_path: {env_path}")
            print(f"[DEBUG] Current step after generation: {self.current_step}")
            
            # Handle RTL integration - but don't update progress here
            if hasattr(self.gui_integration, 'generated_rtl_path') and os.path.exists(self.gui_integration.generated_rtl_path):
                import shutil
                dest_rtl_dir = os.path.join(env_path, "rtl_wrapper", "generated_rtl")
                if os.path.exists(dest_rtl_dir):
                    shutil.rmtree(dest_rtl_dir)
                shutil.copytree(self.gui_integration.generated_rtl_path, dest_rtl_dir)
                self.gui_integration._update_rtl_filelist(env_path)
            elif hasattr(self.gui_integration, 'existing_rtl_path') and os.path.exists(self.gui_integration.existing_rtl_path):
                # Use existing RTL
                import shutil
                dest_rtl_dir = os.path.join(env_path, "rtl_wrapper", "existing_rtl")
                if os.path.exists(dest_rtl_dir):
                    shutil.rmtree(dest_rtl_dir)
                shutil.copytree(self.gui_integration.existing_rtl_path, dest_rtl_dir)
                self.gui_integration._update_rtl_filelist(env_path)
            
            # Don't add ANY extra progress updates - the wrapper should handle all 12
            return env_path
            
        except Exception as e:
            if "cancelled" in str(e).lower():
                self.update_progress("Generation cancelled")
                return None
            raise Exception(f"Failed to generate RTL integration environment: {str(e)}")
            
    def _generate_vip_standalone_with_progress(self):
        """Generate VIP standalone environment with progress updates"""
        try:
            # In standalone mode, we might be at step 2
            if not self.update_progress("Loading VIP environment generator", 2):
                return None
                
            # Use the wrapper instead of direct import
            from vip_environment_generator_wrapper import VIPEnvironmentGenerator
            
            # Create generator instance  
            generator = VIPEnvironmentGenerator(
                gui_config=self.gui_integration.gui.current_config,
                mode="vip_standalone",
                simulator=self.gui_integration.target_simulator
            )
            
            # Add progress callback
            def generator_progress_callback(step_name, step_num=None):
                if self.cancelled:
                    raise Exception("Generation cancelled by user")
                print(f"[DEBUG] Progress callback: {step_name}, step_num={step_num}")
                if step_num is not None:
                    self.update_progress(step_name, step_num)
                else:
                    self.update_progress(step_name)
                    
            generator._progress_callback = generator_progress_callback
            
            # Generate the environment
            env_path = generator.generate_environment(self.output_dir)
            
            # Don't add extra progress update here - let the 12/12 show
            # if not self.update_progress("VIP standalone environment completed"):
            #     return None
                
            return env_path
            
        except Exception as e:
            if "cancelled" in str(e).lower():
                self.update_progress("Generation cancelled")
                return None
            raise Exception(f"Failed to generate VIP standalone environment: {str(e)}")

# Update VIPControlPanelUltraThin to use the new thread
class VIPControlPanelUltraThinEnhanced(VIPControlPanelUltraThin):
    """Enhanced VIP Control Panel with fast generation"""
    
    def show_vip_setup_dialog(self, mode="rtl_integration"):
        """Override to use ultrathin generation thread"""
        # Store the original thread class
        original_thread_class = VIPGenerationThread
        
        # Temporarily replace with our ultrathin version
        import vip_gui_integration
        vip_gui_integration.VIPGenerationThread = VIPGenerationThreadUltraThin
        
        try:
            # Call parent method which will use our thread
            super().show_vip_setup_dialog(mode)
        finally:
            # Restore original
            vip_gui_integration.VIPGenerationThread = original_thread_class

# Export the enhanced ultrathin version as the main one
VIPControlPanelUltraThin = VIPControlPanelUltraThinEnhanced

# Export all classes
__all__ = ['VIPControlPanelUltraThin', 'SimulationStatus', 'SimulationEngine',
           'VIPIntegrationError', 'ResultsPanel', 'TestGeneratorPanel', 
           'SimulationControlPanel', 'VIPGenerationThreadUltraThin']