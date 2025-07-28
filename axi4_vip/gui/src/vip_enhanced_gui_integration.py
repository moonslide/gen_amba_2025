#!/usr/bin/env python3
"""
Enhanced VIP GUI Integration
Integrates all new test cases and features into the GUI
Based on tim_axi4_vip comprehensive test suite
"""

import os
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import json
import threading
import queue
from datetime import datetime
from typing import Dict, List, Optional, Any
import logging

# Import all test generators
from vip_enhanced_test_sequences import VIPEnhancedTestSequences
from vip_cache_coherency_tests import VIPCacheCoherencyTestGenerator
from vip_atomic_transaction_tests import VIPAtomicTransactionTestGenerator
from vip_narrow_transfer_tests import VIPNarrowTransferTestGenerator
from vip_unaligned_address_tests import VIPUnalignedAddressTestGenerator

class VIPEnhancedGUIIntegration:
    """Enhanced GUI integration with all new test cases"""
    
    def __init__(self, parent_window=None):
        self.parent = parent_window
        self.logger = self._setup_logging()
        
        # Test generators
        self.test_generators = {}
        self.test_categories = {}
        self.selected_tests = {}
        
        # GUI state
        self.generation_progress = 0
        self.test_selection_vars = {}
        
        # Create enhanced GUI
        self._create_enhanced_gui()
        self._initialize_test_categories()
        
    def _setup_logging(self) -> logging.Logger:
        """Setup logging"""
        logger = logging.getLogger('VIPEnhancedGUI')
        logger.setLevel(logging.INFO)
        
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            
        return logger
        
    def _create_enhanced_gui(self):
        """Create enhanced GUI with all test categories"""
        
        if self.parent:
            self.root = tk.Toplevel(self.parent)
        else:
            self.root = tk.Tk()
            
        self.root.title("AXI4 VIP Enhanced Test Suite")
        self.root.geometry("1200x800")
        
        # Create main notebook
        self.main_notebook = ttk.Notebook(self.root)
        self.main_notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # Create tabs
        self._create_test_selection_tab()
        self._create_test_configuration_tab()
        self._create_generation_control_tab()
        self._create_test_summary_tab()
        
        # Status bar
        self._create_status_bar()
        
    def _initialize_test_categories(self):
        """Initialize all test categories from tim_axi4_vip"""
        
        # Base configuration
        self.base_config = {
            'num_masters': 4,
            'num_slaves': 4,
            'data_width': 128,
            'addr_width': 64,
            'id_width': 8,
            'user_width': 32,
            'support_axi3': True,
            'support_exclusive': True,
            'support_qos': True,
            'support_region': True
        }
        
        # Initialize generators
        self.test_generators['enhanced'] = VIPEnhancedTestSequences(self.base_config)
        self.test_generators['cache_coherency'] = VIPCacheCoherencyTestGenerator(self.base_config)
        self.test_generators['atomic'] = VIPAtomicTransactionTestGenerator(self.base_config)
        self.test_generators['narrow'] = VIPNarrowTransferTestGenerator(self.base_config)
        self.test_generators['unaligned'] = VIPUnalignedAddressTestGenerator(self.base_config)
        
        # Get test categories from enhanced generator
        self.test_categories = self.test_generators['enhanced'].test_sequences
        
    def _create_test_selection_tab(self):
        """Create test selection tab"""
        
        selection_frame = ttk.Frame(self.main_notebook)
        self.main_notebook.add(selection_frame, text="Test Selection")
        
        # Create scrollable frame
        canvas = tk.Canvas(selection_frame)
        scrollbar = ttk.Scrollbar(selection_frame, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # Control buttons
        control_frame = ttk.Frame(selection_frame)
        control_frame.pack(side=tk.TOP, fill=tk.X, padx=5, pady=5)
        
        ttk.Button(control_frame, text="Select All", command=self._select_all_tests).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Clear All", command=self._clear_all_tests).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Select Recommended", command=self._select_recommended_tests).pack(side=tk.LEFT, padx=5)
        
        # Test count label
        self.test_count_label = ttk.Label(control_frame, text="Selected: 0 tests")
        self.test_count_label.pack(side=tk.RIGHT, padx=5)
        
        # Create test category frames
        row = 0
        for category, tests in self.test_categories.items():
            # Category frame
            cat_frame = ttk.LabelFrame(scrollable_frame, text=f"{category.replace('_', ' ').title()} ({len(tests)} tests)")
            cat_frame.grid(row=row, column=0, columnspan=2, sticky="ew", padx=5, pady=5)
            
            # Category select all
            cat_var = tk.BooleanVar(value=False)
            cat_check = ttk.Checkbutton(
                cat_frame, 
                text=f"Select all {category} tests",
                variable=cat_var,
                command=lambda c=category, v=cat_var: self._toggle_category(c, v)
            )
            cat_check.grid(row=0, column=0, columnspan=2, sticky="w", padx=5, pady=2)
            
            # Individual tests
            test_row = 1
            test_col = 0
            for test in tests:
                if test not in self.test_selection_vars:
                    self.test_selection_vars[test] = tk.BooleanVar(value=False)
                    
                test_check = ttk.Checkbutton(
                    cat_frame,
                    text=test,
                    variable=self.test_selection_vars[test],
                    command=self._update_test_count
                )
                test_check.grid(row=test_row, column=test_col, sticky="w", padx=20, pady=1)
                
                test_col += 1
                if test_col > 1:
                    test_col = 0
                    test_row += 1
                    
            row += 1
            
        # Pack canvas and scrollbar
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
    def _create_test_configuration_tab(self):
        """Create test configuration tab"""
        
        config_frame = ttk.Frame(self.main_notebook)
        self.main_notebook.add(config_frame, text="Test Configuration")
        
        # Bus configuration
        bus_frame = ttk.LabelFrame(config_frame, text="Bus Configuration")
        bus_frame.pack(fill=tk.X, padx=10, pady=5)
        
        # Masters/Slaves
        ttk.Label(bus_frame, text="Number of Masters:").grid(row=0, column=0, sticky="w", padx=5, pady=2)
        self.masters_var = tk.IntVar(value=4)
        ttk.Spinbox(bus_frame, from_=1, to=16, textvariable=self.masters_var, width=10).grid(row=0, column=1, padx=5, pady=2)
        
        ttk.Label(bus_frame, text="Number of Slaves:").grid(row=0, column=2, sticky="w", padx=5, pady=2)
        self.slaves_var = tk.IntVar(value=4)
        ttk.Spinbox(bus_frame, from_=1, to=16, textvariable=self.slaves_var, width=10).grid(row=0, column=3, padx=5, pady=2)
        
        # Data width
        ttk.Label(bus_frame, text="Data Width:").grid(row=1, column=0, sticky="w", padx=5, pady=2)
        self.data_width_var = tk.StringVar(value="128")
        width_combo = ttk.Combobox(bus_frame, textvariable=self.data_width_var, width=10)
        width_combo['values'] = ('32', '64', '128', '256', '512', '1024')
        width_combo.grid(row=1, column=1, padx=5, pady=2)
        
        # Address width
        ttk.Label(bus_frame, text="Address Width:").grid(row=1, column=2, sticky="w", padx=5, pady=2)
        self.addr_width_var = tk.IntVar(value=64)
        ttk.Spinbox(bus_frame, from_=32, to=64, textvariable=self.addr_width_var, width=10).grid(row=1, column=3, padx=5, pady=2)
        
        # Test parameters
        test_frame = ttk.LabelFrame(config_frame, text="Test Parameters")
        test_frame.pack(fill=tk.X, padx=10, pady=5)
        
        # Number of transactions
        ttk.Label(test_frame, text="Transactions per Test:").grid(row=0, column=0, sticky="w", padx=5, pady=2)
        self.num_trans_var = tk.IntVar(value=100)
        ttk.Spinbox(test_frame, from_=10, to=10000, increment=10, textvariable=self.num_trans_var, width=15).grid(row=0, column=1, padx=5, pady=2)
        
        # Test seed
        ttk.Label(test_frame, text="Random Seed:").grid(row=1, column=0, sticky="w", padx=5, pady=2)
        self.seed_var = tk.IntVar(value=12345)
        ttk.Entry(test_frame, textvariable=self.seed_var, width=15).grid(row=1, column=1, padx=5, pady=2)
        
        # Feature enables
        feature_frame = ttk.LabelFrame(config_frame, text="Protocol Features")
        feature_frame.pack(fill=tk.X, padx=10, pady=5)
        
        self.feature_vars = {}
        features = [
            ("Enable AXI3 Mode", "axi3_mode"),
            ("Enable QoS", "enable_qos"),
            ("Enable REGION", "enable_region"),
            ("Enable USER signals", "enable_user"),
            ("Enable Exclusive Access", "enable_exclusive"),
            ("Enable Cache Coherency", "enable_cache"),
            ("Enable Low Power", "enable_lowpower"),
            ("Enable ACE-Lite", "enable_ace_lite")
        ]
        
        row = 0
        col = 0
        for label, key in features:
            self.feature_vars[key] = tk.BooleanVar(value=True)
            ttk.Checkbutton(feature_frame, text=label, variable=self.feature_vars[key]).grid(row=row, column=col, sticky="w", padx=5, pady=2)
            col += 1
            if col > 3:
                col = 0
                row += 1
                
    def _create_generation_control_tab(self):
        """Create generation control tab"""
        
        control_frame = ttk.Frame(self.main_notebook)
        self.main_notebook.add(control_frame, text="Generation Control")
        
        # Output directory
        output_frame = ttk.LabelFrame(control_frame, text="Output Configuration")
        output_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Label(output_frame, text="Output Directory:").grid(row=0, column=0, sticky="w", padx=5, pady=5)
        self.output_dir_var = tk.StringVar(value="vip_output/enhanced_tests")
        ttk.Entry(output_frame, textvariable=self.output_dir_var, width=50).grid(row=0, column=1, padx=5, pady=5)
        ttk.Button(output_frame, text="Browse", command=self._browse_output_dir).grid(row=0, column=2, padx=5, pady=5)
        
        # Generation options
        options_frame = ttk.LabelFrame(control_frame, text="Generation Options")
        options_frame.pack(fill=tk.X, padx=10, pady=5)
        
        self.gen_options = {}
        options = [
            ("Generate SystemVerilog", "gen_sv", True),
            ("Generate UVM Components", "gen_uvm", True),
            ("Generate Coverage Models", "gen_coverage", True),
            ("Generate Assertions", "gen_assertions", True),
            ("Generate Documentation", "gen_docs", True),
            ("Generate Makefiles", "gen_makefiles", True)
        ]
        
        row = 0
        col = 0
        for label, key, default in options:
            self.gen_options[key] = tk.BooleanVar(value=default)
            ttk.Checkbutton(options_frame, text=label, variable=self.gen_options[key]).grid(row=row, column=col, sticky="w", padx=5, pady=2)
            col += 1
            if col > 2:
                col = 0
                row += 1
                
        # Control buttons
        button_frame = ttk.Frame(control_frame)
        button_frame.pack(pady=20)
        
        self.generate_btn = ttk.Button(button_frame, text="Generate Tests", command=self._generate_tests, style="Accent.TButton")
        self.generate_btn.pack(side=tk.LEFT, padx=5)
        
        self.validate_btn = ttk.Button(button_frame, text="Validate Configuration", command=self._validate_configuration)
        self.validate_btn.pack(side=tk.LEFT, padx=5)
        
        # Progress frame
        progress_frame = ttk.LabelFrame(control_frame, text="Generation Progress")
        progress_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(progress_frame, variable=self.progress_var, maximum=100)
        self.progress_bar.pack(fill=tk.X, padx=10, pady=10)
        
        self.progress_text = tk.Text(progress_frame, height=10, width=80)
        self.progress_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # Add scrollbar to progress text
        progress_scroll = ttk.Scrollbar(progress_frame, command=self.progress_text.yview)
        progress_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.progress_text.config(yscrollcommand=progress_scroll.set)
        
    def _create_test_summary_tab(self):
        """Create test summary tab"""
        
        summary_frame = ttk.Frame(self.main_notebook)
        self.main_notebook.add(summary_frame, text="Test Summary")
        
        # Summary text
        self.summary_text = tk.Text(summary_frame, wrap=tk.WORD)
        self.summary_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Add scrollbar
        summary_scroll = ttk.Scrollbar(summary_frame, command=self.summary_text.yview)
        summary_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.summary_text.config(yscrollcommand=summary_scroll.set)
        
        # Update summary
        self._update_test_summary()
        
    def _create_status_bar(self):
        """Create status bar"""
        
        self.status_bar = ttk.Label(self.root, text="Ready", relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
    def _select_all_tests(self):
        """Select all tests"""
        for var in self.test_selection_vars.values():
            var.set(True)
        self._update_test_count()
        
    def _clear_all_tests(self):
        """Clear all test selections"""
        for var in self.test_selection_vars.values():
            var.set(False)
        self._update_test_count()
        
    def _select_recommended_tests(self):
        """Select recommended tests for comprehensive coverage"""
        
        recommended = {
            # Protocol violations - essential
            "4kb_boundary_violation", "exclusive_access_violation", "awvalid_without_awready",
            
            # Cache coherency - important
            "write_through_cache_test", "write_back_cache_test", "cache_line_boundary_test",
            
            # Atomic transactions - critical
            "exclusive_read_write_success", "exclusive_read_write_fail", "multi_master_exclusive",
            
            # Narrow transfers - common
            "narrow_write_8b_on_32b", "sparse_write_strobe", "narrow_wrap_sequence",
            
            # Unaligned - important
            "unaligned_write_sequence", "boundary_crossing_sequence", "near_4kb_boundary_sequence",
            
            # Performance
            "maximum_throughput_test", "back_to_back_transfer"
        }
        
        # Clear all first
        self._clear_all_tests()
        
        # Select recommended
        for test_name, var in self.test_selection_vars.items():
            if test_name in recommended:
                var.set(True)
                
        self._update_test_count()
        self._log_progress("Selected recommended test suite")
        
    def _toggle_category(self, category: str, var: tk.BooleanVar):
        """Toggle all tests in a category"""
        
        value = var.get()
        for test in self.test_categories.get(category, []):
            if test in self.test_selection_vars:
                self.test_selection_vars[test].set(value)
                
        self._update_test_count()
        
    def _update_test_count(self):
        """Update selected test count"""
        
        count = sum(1 for var in self.test_selection_vars.values() if var.get())
        self.test_count_label.config(text=f"Selected: {count} tests")
        
    def _browse_output_dir(self):
        """Browse for output directory"""
        
        directory = filedialog.askdirectory()
        if directory:
            self.output_dir_var.set(directory)
            
    def _validate_configuration(self):
        """Validate test configuration"""
        
        errors = []
        warnings = []
        
        # Check test selection
        selected_count = sum(1 for var in self.test_selection_vars.values() if var.get())
        if selected_count == 0:
            errors.append("No tests selected")
            
        # Check bus configuration
        if self.masters_var.get() < 1:
            errors.append("At least 1 master required")
        if self.slaves_var.get() < 1:
            errors.append("At least 1 slave required")
            
        # Check output directory
        output_dir = self.output_dir_var.get()
        if not output_dir:
            errors.append("Output directory not specified")
            
        # Warnings
        if selected_count > 100:
            warnings.append(f"Large number of tests selected ({selected_count}). Generation may take time.")
            
        if self.num_trans_var.get() > 1000:
            warnings.append(f"High transaction count ({self.num_trans_var.get()}) may result in large files.")
            
        # Show results
        if errors:
            messagebox.showerror("Configuration Errors", "\n".join(errors))
            return False
        elif warnings:
            result = messagebox.askokcancel("Configuration Warnings", 
                                          "\n".join(warnings) + "\n\nContinue anyway?")
            return result
        else:
            messagebox.showinfo("Configuration Valid", "Configuration is valid!")
            return True
            
    def _generate_tests(self):
        """Generate selected tests"""
        
        # Validate first
        if not self._validate_configuration():
            return
            
        # Disable generate button
        self.generate_btn.config(state=tk.DISABLED)
        
        # Start generation in thread
        thread = threading.Thread(target=self._run_generation)
        thread.daemon = True
        thread.start()
        
    def _run_generation(self):
        """Run test generation in background thread"""
        
        try:
            self._log_progress("Starting test generation...")
            
            # Update configuration
            self._update_generator_config()
            
            # Create output directory
            output_dir = self.output_dir_var.get()
            os.makedirs(output_dir, exist_ok=True)
            
            # Get selected tests by category
            selected_by_category = self._get_selected_tests_by_category()
            
            total_tests = sum(len(tests) for tests in selected_by_category.values())
            completed = 0
            
            # Generate enhanced test sequences
            if selected_by_category:
                self._log_progress(f"\nGenerating {total_tests} test sequences...")
                
                # Generate base sequences
                enhanced_gen = self.test_generators['enhanced']
                enhanced_gen.generate_all_test_sequences(output_dir)
                
                # Generate specialized components
                if any('cache' in cat for cat in selected_by_category):
                    self._log_progress("\nGenerating cache coherency components...")
                    cache_gen = self.test_generators['cache_coherency']
                    cache_gen.generate_cache_coherency_tests(output_dir)
                    
                if any('atomic' in cat for cat in selected_by_category):
                    self._log_progress("\nGenerating atomic transaction components...")
                    atomic_gen = self.test_generators['atomic']
                    atomic_gen.generate_atomic_transaction_tests(output_dir)
                    
                if any('narrow' in cat for cat in selected_by_category):
                    self._log_progress("\nGenerating narrow transfer components...")
                    narrow_gen = self.test_generators['narrow']
                    narrow_gen.generate_narrow_transfer_tests(output_dir)
                    
                if any('unaligned' in cat for cat in selected_by_category):
                    self._log_progress("\nGenerating unaligned address components...")
                    unaligned_gen = self.test_generators['unaligned']
                    unaligned_gen.generate_unaligned_address_tests(output_dir)
                    
            # Generate summary
            self._generate_test_summary(output_dir, selected_by_category)
            
            self._log_progress(f"\n✓ Test generation completed successfully!")
            self._log_progress(f"Output directory: {output_dir}")
            
            # Update progress
            self.progress_var.set(100)
            
        except Exception as e:
            self._log_progress(f"\n✗ Error during generation: {str(e)}")
            messagebox.showerror("Generation Error", str(e))
            
        finally:
            # Re-enable button
            self.root.after(0, lambda: self.generate_btn.config(state=tk.NORMAL))
            
    def _update_generator_config(self):
        """Update generator configurations"""
        
        config = {
            'num_masters': self.masters_var.get(),
            'num_slaves': self.slaves_var.get(),
            'data_width': int(self.data_width_var.get()),
            'addr_width': self.addr_width_var.get(),
            'id_width': 8,
            'user_width': 32,
            'support_axi3': self.feature_vars['axi3_mode'].get(),
            'support_exclusive': self.feature_vars['enable_exclusive'].get(),
            'support_qos': self.feature_vars['enable_qos'].get(),
            'support_region': self.feature_vars['enable_region'].get(),
            'support_ace_lite': self.feature_vars['enable_ace_lite'].get()
        }
        
        # Update all generators
        for gen in self.test_generators.values():
            gen.config = config
            
    def _get_selected_tests_by_category(self) -> Dict[str, List[str]]:
        """Get selected tests organized by category"""
        
        selected = {}
        
        for category, tests in self.test_categories.items():
            selected_in_category = []
            for test in tests:
                if test in self.test_selection_vars and self.test_selection_vars[test].get():
                    selected_in_category.append(test)
                    
            if selected_in_category:
                selected[category] = selected_in_category
                
        return selected
        
    def _generate_test_summary(self, output_dir: str, selected_tests: Dict[str, List[str]]):
        """Generate test summary report"""
        
        summary_file = os.path.join(output_dir, "test_generation_summary.txt")
        
        with open(summary_file, 'w') as f:
            f.write("AXI4 VIP Enhanced Test Generation Summary\n")
            f.write("=" * 60 + "\n\n")
            f.write(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
            
            f.write("Configuration:\n")
            f.write(f"  Masters: {self.masters_var.get()}\n")
            f.write(f"  Slaves: {self.slaves_var.get()}\n")
            f.write(f"  Data Width: {self.data_width_var.get()} bits\n")
            f.write(f"  Address Width: {self.addr_width_var.get()} bits\n\n")
            
            f.write("Test Selection:\n")
            total = 0
            for category, tests in selected_tests.items():
                f.write(f"  {category}: {len(tests)} tests\n")
                for test in tests:
                    f.write(f"    - {test}\n")
                total += len(tests)
                
            f.write(f"\nTotal Tests Generated: {total}\n")
            
        self._log_progress(f"\nTest summary saved to: {summary_file}")
        
    def _update_test_summary(self):
        """Update test summary display"""
        
        self.summary_text.delete(1.0, tk.END)
        
        # Calculate statistics
        total_available = sum(len(tests) for tests in self.test_categories.items())
        
        summary = f"""AXI4 VIP Enhanced Test Suite Summary
=====================================

Total Available Tests: {total_available}

Test Categories:
"""
        
        for category, tests in self.test_categories.items():
            summary += f"\n{category.replace('_', ' ').title()}: {len(tests)} tests\n"
            
        summary += f"""
Key Features:
- Protocol violation detection
- Cache coherency verification  
- Atomic transaction testing
- Narrow transfer support
- Unaligned address handling
- Outstanding transaction management
- AXI3 interleaving support
- Low power interface testing
- Multi-layer interconnect scenarios

Based on tim_axi4_vip architecture with:
- Scalable bus matrix (up to 64x64)
- Complete AXI4 protocol coverage
- UVM-based verification environment
- Comprehensive coverage models
- Advanced error injection
- Statistical analysis and reporting
"""
        
        self.summary_text.insert(tk.END, summary)
        
    def _log_progress(self, message: str):
        """Log progress message"""
        
        self.logger.info(message)
        
        # Update GUI
        self.root.after(0, lambda: self._update_progress_display(message))
        
    def _update_progress_display(self, message: str):
        """Update progress display in GUI"""
        
        self.progress_text.insert(tk.END, message + "\n")
        self.progress_text.see(tk.END)
        self.status_bar.config(text=message)

def launch_enhanced_vip_gui(parent=None):
    """Launch the enhanced VIP GUI"""
    
    gui = VIPEnhancedGUIIntegration(parent)
    
    if not parent:
        gui.root.mainloop()
        
    return gui

if __name__ == "__main__":
    launch_enhanced_vip_gui()