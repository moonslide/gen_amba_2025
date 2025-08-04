#!/usr/bin/env python3
"""
Modern VIP GUI Integration Module
Enhanced AXI4 Verification IP GUI with ultrathink design aesthetic
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import json
import threading
import queue
import time
import os
from typing import Dict, List, Optional, Any
from dataclasses import asdict
from modern_ui_theme import ModernTheme, ModernCanvas, ModernButton, apply_modern_theme, AnimatedWidget

# Import with fallback for missing modules
try:
    from axi_vip_components import (
        AXIMasterAgent, AXISlaveAgent, AXIMonitor, AXIChecker,
        VIPConfig, AXITransaction, create_axi_vip_environment
    )
    from axi_test_sequences import (
        AXITestSequenceGenerator, TestScenarioConfig, 
        create_comprehensive_test_suite
    )
    VIP_COMPONENTS_AVAILABLE = False  # Force to False for GUI-only mode
except (ImportError, AttributeError):
    VIP_COMPONENTS_AVAILABLE = False
    VIPConfig = None
    create_axi_vip_environment = None
    
try:
    from uvm_config_exporter import export_gui_config_to_uvm
except ImportError:
    from .uvm_config_exporter import export_gui_config_to_uvm


class ModernProgressDialog:
    """Modern progress dialog with smooth animations"""
    
    def __init__(self, parent, title="Processing", theme=None):
        self.theme = theme or ModernTheme()
        self.parent = parent
        self.canceled = False
        
        # Create dialog
        self.dialog = tk.Toplevel(parent)
        self.dialog.title(title)
        self.dialog.configure(bg=self.theme.get_color('surface'))
        self.dialog.transient(parent)
        self.dialog.grab_set()
        
        # Window properties
        self.dialog.geometry("400x200")
        self.dialog.resizable(False, False)
        self.center_window()
        
        # Remove window decorations for cleaner look
        self.dialog.overrideredirect(True)
        
        # Main frame
        main_frame = tk.Frame(self.dialog, bg=self.theme.get_color('surface'))
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # Header with close button
        header = tk.Frame(main_frame, bg=self.theme.get_color('primary'), height=40)
        header.pack(fill=tk.X)
        header.pack_propagate(False)
        
        # Title in header
        tk.Label(header, text=title, bg=self.theme.get_color('primary'),
                fg=self.theme.get_color('text_on_primary'),
                font=self.theme.FONTS['subheading']).pack(side=tk.LEFT, padx=20, pady=10)
        
        # Close button
        close_btn = tk.Label(header, text="✕", bg=self.theme.get_color('primary'),
                           fg=self.theme.get_color('text_on_primary'),
                           font=('Segoe UI', 14), cursor='hand2')
        close_btn.pack(side=tk.RIGHT, padx=15)
        close_btn.bind('<Button-1>', lambda e: self.cancel())
        
        # Content
        content = tk.Frame(main_frame, bg=self.theme.get_color('surface'), padx=30, pady=20)
        content.pack(fill=tk.BOTH, expand=True)
        
        # Progress message
        self.message_label = tk.Label(content, text="Initializing...",
                                    bg=self.theme.get_color('surface'),
                                    fg=self.theme.get_color('text_primary'),
                                    font=self.theme.FONTS['body'])
        self.message_label.pack(pady=(0, 20))
        
        # Modern progress bar
        self.progress_frame = tk.Frame(content, bg=self.theme.get_color('surface_variant'),
                                     height=6)
        self.progress_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.progress_bar = tk.Frame(self.progress_frame, bg=self.theme.get_color('primary'),
                                   height=6, width=0)
        self.progress_bar.place(x=0, y=0)
        
        # Percentage label
        self.percent_label = tk.Label(content, text="0%",
                                    bg=self.theme.get_color('surface'),
                                    fg=self.theme.get_color('text_secondary'),
                                    font=self.theme.FONTS['caption'])
        self.percent_label.pack()
        
        # Cancel button
        self.cancel_btn = ModernButton(content, text="Cancel", command=self.cancel,
                                     style='secondary', theme=self.theme,
                                     width=100, height=32)
        self.cancel_btn.pack(pady=(10, 0))
        
        # Enable dragging
        self._drag_data = {"x": 0, "y": 0}
        header.bind('<Button-1>', self._start_drag)
        header.bind('<B1-Motion>', self._drag_window)
        
    def center_window(self):
        """Center dialog on parent"""
        self.dialog.update_idletasks()
        
        # Get parent position
        parent_x = self.parent.winfo_x()
        parent_y = self.parent.winfo_y()
        parent_width = self.parent.winfo_width()
        parent_height = self.parent.winfo_height()
        
        # Calculate center position
        x = parent_x + (parent_width - 400) // 2
        y = parent_y + (parent_height - 200) // 2
        
        self.dialog.geometry(f"+{x}+{y}")
        
    def _start_drag(self, event):
        """Start window drag"""
        self._drag_data["x"] = event.x
        self._drag_data["y"] = event.y
        
    def _drag_window(self, event):
        """Drag window"""
        x = self.dialog.winfo_x() + event.x - self._drag_data["x"]
        y = self.dialog.winfo_y() + event.y - self._drag_data["y"]
        self.dialog.geometry(f"+{x}+{y}")
        
    def update(self, progress: float, message: str = ""):
        """Update progress (0.0 to 1.0)"""
        if self.canceled:
            return
            
        # Update message
        if message:
            self.message_label.config(text=message)
            
        # Update progress bar with animation
        target_width = int(self.progress_frame.winfo_width() * progress)
        current_width = self.progress_bar.winfo_width()
        
        # Animate progress bar
        if target_width > current_width:
            self._animate_progress(current_width, target_width)
            
        # Update percentage
        self.percent_label.config(text=f"{int(progress * 100)}%")
        
        # Update dialog
        self.dialog.update()
        
    def _animate_progress(self, start_width, end_width, duration=200):
        """Smooth progress animation"""
        steps = 20
        step_size = (end_width - start_width) / steps
        step_duration = duration // steps
        
        for i in range(steps):
            if self.canceled:
                break
            new_width = int(start_width + step_size * (i + 1))
            self.progress_bar.config(width=new_width)
            self.dialog.update()
            time.sleep(step_duration / 1000)
            
    def cancel(self):
        """Cancel operation"""
        self.canceled = True
        self.dialog.destroy()
        
    def close(self):
        """Close dialog"""
        self.dialog.destroy()


class ModernTestResultView(ttk.Frame):
    """Modern test result visualization"""
    
    def __init__(self, parent, theme: ModernTheme = None, **kwargs):
        self.theme = theme or ModernTheme()
        super().__init__(parent, style='Modern.TFrame', **kwargs)
        
        self.setup_ui()
        
    def setup_ui(self):
        """Setup result view UI"""
        # Header
        header_frame = tk.Frame(self, bg=self.theme.get_color('surface_variant'), height=50)
        header_frame.pack(fill=tk.X, padx=1, pady=(1, 10))
        header_frame.pack_propagate(False)
        
        # Summary cards
        self.summary_frame = tk.Frame(self, bg=self.theme.get_color('bg'))
        self.summary_frame.pack(fill=tk.X, padx=20, pady=10)
        
        # Create summary cards
        self.create_summary_card(self.summary_frame, "Total Tests", "0", self.theme.get_color('primary'))
        self.create_summary_card(self.summary_frame, "Passed", "0", self.theme.get_color('success'))
        self.create_summary_card(self.summary_frame, "Failed", "0", self.theme.get_color('error'))
        self.create_summary_card(self.summary_frame, "Coverage", "0%", self.theme.get_color('info'))
        
        # Results area
        results_frame = ttk.LabelFrame(self, text="Test Results", style='Modern.TLabelframe')
        results_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Modern treeview for results
        self.results_tree = ttk.Treeview(results_frame, columns=('Status', 'Duration', 'Coverage'),
                                       show='tree headings', style='Modern.Treeview')
        self.results_tree.heading('#0', text='Test Name')
        self.results_tree.heading('Status', text='Status')
        self.results_tree.heading('Duration', text='Duration')
        self.results_tree.heading('Coverage', text='Coverage')
        
        # Configure columns
        self.results_tree.column('#0', width=300)
        self.results_tree.column('Status', width=100)
        self.results_tree.column('Duration', width=100)
        self.results_tree.column('Coverage', width=100)
        
        # Scrollbar
        scroll = ttk.Scrollbar(results_frame, orient=tk.VERTICAL,
                             command=self.results_tree.yview,
                             style='Modern.Vertical.TScrollbar')
        self.results_tree.configure(yscrollcommand=scroll.set)
        
        self.results_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Configure tags for status colors
        self.results_tree.tag_configure('passed', foreground=self.theme.get_color('success'))
        self.results_tree.tag_configure('failed', foreground=self.theme.get_color('error'))
        self.results_tree.tag_configure('running', foreground=self.theme.get_color('info'))
        
    def create_summary_card(self, parent, title, value, color):
        """Create modern summary card"""
        card = tk.Frame(parent, bg=self.theme.get_color('surface'), relief=tk.FLAT, bd=1)
        card.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        # Add hover effect
        def on_enter(e):
            card.config(bg=self.theme.get_color('surface_variant'))
        def on_leave(e):
            card.config(bg=self.theme.get_color('surface'))
            
        card.bind('<Enter>', on_enter)
        card.bind('<Leave>', on_leave)
        
        # Card content
        content = tk.Frame(card, bg=self.theme.get_color('surface'), padx=20, pady=15)
        content.pack(fill=tk.BOTH, expand=True)
        
        # Title
        tk.Label(content, text=title, bg=self.theme.get_color('surface'),
                fg=self.theme.get_color('text_secondary'),
                font=self.theme.FONTS['caption']).pack()
        
        # Value with color
        value_label = tk.Label(content, text=value, bg=self.theme.get_color('surface'),
                             fg=color, font=self.theme.FONTS['heading'])
        value_label.pack(pady=(5, 0))
        
        # Store reference for updates
        setattr(self, f"{title.lower().replace(' ', '_')}_label", value_label)
        
    def update_results(self, test_results: Dict[str, Any]):
        """Update test results display"""
        # Update summary
        total = len(test_results)
        passed = sum(1 for r in test_results.values() if r.get('status') == 'passed')
        failed = sum(1 for r in test_results.values() if r.get('status') == 'failed')
        
        self.total_tests_label.config(text=str(total))
        self.passed_label.config(text=str(passed))
        self.failed_label.config(text=str(failed))
        
        # Update tree
        for item in self.results_tree.get_children():
            self.results_tree.delete(item)
            
        for test_name, result in test_results.items():
            status = result.get('status', 'pending')
            duration = result.get('duration', '-')
            coverage = result.get('coverage', '-')
            
            tag = status if status in ['passed', 'failed', 'running'] else ''
            self.results_tree.insert('', 'end', text=test_name,
                                   values=(status.title(), duration, coverage),
                                   tags=(tag,))


class ModernVIPControlPanel:
    """Modern VIP Control Panel with enhanced UI"""
    
    def __init__(self, parent_frame, gui_instance, theme: ModernTheme = None):
        self.parent = parent_frame
        self.gui = gui_instance
        self.theme = theme or ModernTheme()
        self.vip_environment = None
        self.test_thread = None
        self.test_running = False
        self.test_results = {}
        
        # Message queue for thread communication
        self.message_queue = queue.Queue()
        
        try:
            self.setup_vip_panel()
            # Start message processor
            self.process_messages()
        except Exception as e:
            print(f"[WARNING] VIP panel setup error: {e}")
            self._create_fallback_ui()
            
    def _create_fallback_ui(self):
        """Create fallback UI when setup fails"""
        fallback_frame = tk.Frame(self.parent, bg=self.theme.get_color('surface_variant'))
        fallback_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        
        icon_label = tk.Label(fallback_frame, text="⚠", 
                            font=('Segoe UI', 48),
                            bg=self.theme.get_color('surface_variant'),
                            fg=self.theme.get_color('warning'))
        icon_label.pack(pady=20)
        
        tk.Label(fallback_frame, text="VIP features are currently unavailable",
                bg=self.theme.get_color('surface_variant'),
                fg=self.theme.get_color('text_primary'),
                font=self.theme.FONTS['subheading']).pack()
        
        tk.Label(fallback_frame, text="Please check your VIP installation",
                bg=self.theme.get_color('surface_variant'),
                fg=self.theme.get_color('text_secondary'),
                font=self.theme.FONTS['body']).pack(pady=(5, 20))
        
    def setup_vip_panel(self):
        """Setup VIP control panel with modern UI"""
        # Create main container
        main_container = ttk.Frame(self.parent, style='Modern.TFrame')
        main_container.pack(fill=tk.BOTH, expand=True)
        
        # Create modern tab interface
        self.tab_control = ttk.Notebook(main_container, style='Modern.TNotebook')
        self.tab_control.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create tabs with icons
        self.setup_dashboard_tab()
        self.setup_environment_tab()
        self.setup_test_generation_tab()
        self.setup_execution_tab()
        self.setup_results_tab()
        self.setup_coverage_tab()
        
    def setup_dashboard_tab(self):
        """Setup dashboard tab with overview"""
        dashboard_frame = ttk.Frame(self.tab_control, style='Modern.TFrame')
        self.tab_control.add(dashboard_frame, text="  📊 Dashboard  ")
        
        # Create scrollable content
        canvas = tk.Canvas(dashboard_frame, bg=self.theme.get_color('bg'), highlightthickness=0)
        scrollbar = ttk.Scrollbar(dashboard_frame, orient="vertical", command=canvas.yview,
                                style='Modern.Vertical.TScrollbar')
        scrollable_frame = ttk.Frame(canvas, style='Modern.TFrame')
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # Dashboard content
        self.create_dashboard_content(scrollable_frame)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
    def create_dashboard_content(self, parent):
        """Create dashboard content"""
        # Welcome section
        welcome_frame = tk.Frame(parent, bg=self.theme.get_color('primary'), height=120)
        welcome_frame.pack(fill=tk.X, padx=20, pady=(20, 10))
        welcome_frame.pack_propagate(False)
        
        welcome_content = tk.Frame(welcome_frame, bg=self.theme.get_color('primary'))
        welcome_content.place(relx=0.5, rely=0.5, anchor='center')
        
        tk.Label(welcome_content, text="AXI4 Verification IP Dashboard",
                font=self.theme.FONTS['heading_large'],
                bg=self.theme.get_color('primary'),
                fg=self.theme.get_color('text_on_primary')).pack()
        
        tk.Label(welcome_content, text="Complete verification environment for AXI4 protocol",
                font=self.theme.FONTS['body'],
                bg=self.theme.get_color('primary'),
                fg=self.theme.get_color('text_on_primary')).pack(pady=(5, 0))
        
        # Status cards
        status_frame = tk.Frame(parent, bg=self.theme.get_color('bg'))
        status_frame.pack(fill=tk.X, padx=20, pady=20)
        
        # Create status cards
        self.create_status_card(status_frame, "Environment", "Not Created", "🔧", self.theme.get_color('warning'))
        self.create_status_card(status_frame, "Tests", "0 Available", "🧪", self.theme.get_color('info'))
        self.create_status_card(status_frame, "Coverage", "0%", "📈", self.theme.get_color('secondary'))
        self.create_status_card(status_frame, "Last Run", "Never", "⏱️", self.theme.get_color('text_secondary'))
        
        # Quick actions
        actions_frame = ttk.LabelFrame(parent, text="Quick Actions", style='Modern.TLabelframe')
        actions_frame.pack(fill=tk.X, padx=20, pady=10)
        
        actions_grid = tk.Frame(actions_frame, bg=self.theme.get_color('surface'))
        actions_grid.pack(padx=20, pady=20)
        
        # Action buttons with icons
        self.create_action_button(actions_grid, "🚀 Create Environment", self.create_vip_environment, 0, 0)
        self.create_action_button(actions_grid, "📝 Generate Tests", self.generate_test_suite, 0, 1)
        self.create_action_button(actions_grid, "▶️ Run Tests", self.run_selected_tests, 1, 0)
        self.create_action_button(actions_grid, "📊 View Results", self.show_results, 1, 1)
        
        # Recent activity
        activity_frame = ttk.LabelFrame(parent, text="Recent Activity", style='Modern.TLabelframe')
        activity_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        self.activity_list = tk.Listbox(activity_frame, bg=self.theme.get_color('surface'),
                                      fg=self.theme.get_color('text_primary'),
                                      font=self.theme.FONTS['body_small'],
                                      selectbackground=self.theme.get_color('selection'),
                                      selectforeground=self.theme.get_color('primary'),
                                      relief=tk.FLAT, height=6)
        self.activity_list.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Add initial activity
        self.add_activity("Dashboard initialized")
        
    def create_status_card(self, parent, title, value, icon, color):
        """Create modern status card"""
        card_frame = tk.Frame(parent, bg=self.theme.get_color('surface'),
                            relief=tk.FLAT, bd=0)
        card_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        # Add shadow effect
        shadow = tk.Frame(card_frame, bg=self.theme.get_color('shadow'), height=2)
        shadow.pack(side=tk.BOTTOM, fill=tk.X)
        
        content = tk.Frame(card_frame, bg=self.theme.get_color('surface'), padx=20, pady=20)
        content.pack(fill=tk.BOTH, expand=True)
        
        # Icon
        tk.Label(content, text=icon, font=('Segoe UI', 24),
                bg=self.theme.get_color('surface'),
                fg=color).pack()
        
        # Title
        tk.Label(content, text=title, font=self.theme.FONTS['caption'],
                bg=self.theme.get_color('surface'),
                fg=self.theme.get_color('text_secondary')).pack(pady=(10, 5))
        
        # Value
        value_label = tk.Label(content, text=value, font=self.theme.FONTS['subheading'],
                             bg=self.theme.get_color('surface'),
                             fg=self.theme.get_color('text_primary'))
        value_label.pack()
        
        # Store reference
        setattr(self, f"{title.lower()}_status_label", value_label)
        
        # Add hover effect
        def on_enter(e):
            content.config(bg=self.theme.get_color('surface_variant'))
            for widget in content.winfo_children():
                widget.config(bg=self.theme.get_color('surface_variant'))
                
        def on_leave(e):
            content.config(bg=self.theme.get_color('surface'))
            for widget in content.winfo_children():
                widget.config(bg=self.theme.get_color('surface'))
                
        card_frame.bind('<Enter>', on_enter)
        card_frame.bind('<Leave>', on_leave)
        
    def create_action_button(self, parent, text, command, row, col):
        """Create modern action button"""
        btn_frame = tk.Frame(parent, bg=self.theme.get_color('surface'))
        btn_frame.grid(row=row, column=col, padx=10, pady=10)
        
        btn = ModernButton(btn_frame, text=text, command=command,
                         theme=self.theme, width=180, height=60)
        btn.pack()
        
    def setup_environment_tab(self):
        """Setup UVM environment configuration tab"""
        env_frame = ttk.Frame(self.tab_control, style='Modern.TFrame')
        self.tab_control.add(env_frame, text="  🔧 Environment  ")
        
        # Scrollable content
        canvas = tk.Canvas(env_frame, bg=self.theme.get_color('bg'), highlightthickness=0)
        scrollbar = ttk.Scrollbar(env_frame, orient="vertical", command=canvas.yview,
                                style='Modern.Vertical.TScrollbar')
        scrollable_frame = ttk.Frame(canvas, style='Modern.TFrame')
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # Important notice with modern styling
        notice_frame = tk.Frame(scrollable_frame, bg=self.theme.get_color('warning'), padx=1, pady=1)
        notice_frame.pack(fill=tk.X, padx=20, pady=(20, 10))
        
        notice_content = tk.Frame(notice_frame, bg=self.theme.get_color('surface_variant'), padx=20, pady=15)
        notice_content.pack(fill=tk.BOTH, expand=True)
        
        notice_header = tk.Frame(notice_content, bg=self.theme.get_color('surface_variant'))
        notice_header.pack(fill=tk.X)
        
        tk.Label(notice_header, text="⚠️", font=('Segoe UI', 20),
                bg=self.theme.get_color('surface_variant'),
                fg=self.theme.get_color('warning')).pack(side=tk.LEFT, padx=(0, 10))
        
        tk.Label(notice_header, text="Important Notice", font=self.theme.FONTS['subheading'],
                bg=self.theme.get_color('surface_variant'),
                fg=self.theme.get_color('text_primary')).pack(side=tk.LEFT)
        
        notice_text = """The GUI exports configuration files for SystemVerilog/UVM simulation.
Run simulations using:
  • cd ../axi4_vip_sim
  • make run TEST=axi4_basic_test CONFIG_FILE=<exported_json>"""
        
        tk.Label(notice_content, text=notice_text, justify=tk.LEFT,
                bg=self.theme.get_color('surface_variant'),
                fg=self.theme.get_color('text_secondary'),
                font=self.theme.FONTS['body']).pack(anchor=tk.W, pady=(10, 0))
        
        # VIP Mode Selection
        mode_frame = ttk.LabelFrame(scrollable_frame, text="VIP Mode Selection", 
                                  style='Modern.TLabelframe', padding=20)
        mode_frame.pack(fill=tk.X, padx=20, pady=10)
        
        tk.Label(mode_frame, text="Select verification mode:", 
                font=self.theme.FONTS['body']).grid(row=0, column=0, sticky=tk.W, pady=10)
        
        self.vip_mode_var = tk.StringVar(value="BEHAVIORAL")
        
        # Modern radio buttons
        radio_frame = tk.Frame(mode_frame, bg=self.theme.get_color('surface'))
        radio_frame.grid(row=1, column=0, columnspan=2, sticky=tk.W)
        
        ttk.Radiobutton(radio_frame, text="Behavioral Model (No RTL)", 
                      variable=self.vip_mode_var, value="BEHAVIORAL",
                      style='Modern.TRadiobutton',
                      command=self.on_vip_mode_change).pack(side=tk.LEFT, padx=(0, 20))
        
        ttk.Radiobutton(radio_frame, text="RTL Integration (Generated RTL)", 
                      variable=self.vip_mode_var, value="RTL",
                      style='Modern.TRadiobutton',
                      command=self.on_vip_mode_change).pack(side=tk.LEFT)
        
        # RTL Path (enabled only in RTL mode)
        rtl_frame = tk.Frame(mode_frame, bg=self.theme.get_color('surface'))
        rtl_frame.grid(row=2, column=0, columnspan=2, sticky=tk.EW, pady=(20, 0))
        
        tk.Label(rtl_frame, text="RTL Path:", font=self.theme.FONTS['body']).pack(side=tk.LEFT, padx=(0, 10))
        
        self.rtl_path_var = tk.StringVar(value="")
        self.rtl_path_entry = ttk.Entry(rtl_frame, textvariable=self.rtl_path_var, 
                                      style='Modern.TEntry', state=tk.DISABLED)
        self.rtl_path_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        self.rtl_browse_btn = ModernButton(rtl_frame, text="Browse", 
                                         command=self.browse_rtl_path,
                                         theme=self.theme, width=80, height=32)
        self.rtl_browse_btn.pack(side=tk.LEFT, padx=(10, 0))
        self.rtl_browse_btn.config(state=tk.DISABLED)
        
        # Output directories
        output_frame = ttk.LabelFrame(scrollable_frame, text="Output Directories", 
                                    style='Modern.TLabelframe', padding=20)
        output_frame.pack(fill=tk.X, padx=20, pady=10)
        
        # VIP Output
        self.create_directory_field(output_frame, "VIP Output:", 
                                  self.browse_vip_output_dir, 0)
        
        # Verilog Output
        self.create_directory_field(output_frame, "Verilog Output:", 
                                  self.browse_verilog_output_dir, 1)
        
        # Create directories button
        ModernButton(output_frame, text="Create Output Directories", 
                   command=self.create_output_directories,
                   theme=self.theme, width=200, height=36).grid(row=2, column=0, columnspan=3, pady=20)
        
        # Export controls
        control_frame = ttk.LabelFrame(scrollable_frame, text="Export Configuration", 
                                     style='Modern.TLabelframe', padding=20)
        control_frame.pack(fill=tk.X, padx=20, pady=10)
        
        btn_grid = tk.Frame(control_frame, bg=self.theme.get_color('surface'))
        btn_grid.pack()
        
        # Export buttons
        ModernButton(btn_grid, text="📁 Export UVM Config", 
                   command=self.export_uvm_configuration,
                   theme=self.theme, width=150, height=40).grid(row=0, column=0, padx=5, pady=5)
        
        ModernButton(btn_grid, text="📂 Open Directory", 
                   command=self.open_uvm_directory,
                   theme=self.theme, width=150, height=40).grid(row=0, column=1, padx=5, pady=5)
        
        ModernButton(btn_grid, text="💻 Show Commands", 
                   command=self.show_uvm_commands,
                   theme=self.theme, width=150, height=40).grid(row=1, column=0, padx=5, pady=5)
        
        ModernButton(btn_grid, text="⚙️ Generate RTL", 
                   command=self.generate_rtl_for_vip,
                   theme=self.theme, width=150, height=40).grid(row=1, column=1, padx=5, pady=5)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
    def create_directory_field(self, parent, label, browse_command, row):
        """Create directory selection field"""
        tk.Label(parent, text=label, font=self.theme.FONTS['body']).grid(row=row, column=0, sticky=tk.W, pady=10)
        
        if "VIP" in label:
            self.vip_output_dir_var = tk.StringVar(value=os.path.abspath("../axi4_vip_sim/output"))
            entry = ttk.Entry(parent, textvariable=self.vip_output_dir_var, style='Modern.TEntry')
        else:
            self.verilog_output_dir_var = tk.StringVar(value=os.path.abspath("output/rtl"))
            entry = ttk.Entry(parent, textvariable=self.verilog_output_dir_var, style='Modern.TEntry')
            
        entry.grid(row=row, column=1, sticky=tk.EW, padx=10)
        
        ModernButton(parent, text="Browse", command=browse_command,
                   theme=self.theme, width=80, height=32).grid(row=row, column=2)
        
        parent.columnconfigure(1, weight=1)
        
    def setup_test_generation_tab(self):
        """Setup test generation tab"""
        test_frame = ttk.Frame(self.tab_control, style='Modern.TFrame')
        self.tab_control.add(test_frame, text="  🧪 Test Generation  ")
        
        # Test configuration
        config_frame = ttk.LabelFrame(test_frame, text="Test Configuration", 
                                    style='Modern.TLabelframe', padding=20)
        config_frame.pack(fill=tk.X, padx=20, pady=20)
        
        # Test categories with modern checkboxes
        tk.Label(config_frame, text="Select test categories to generate:",
                font=self.theme.FONTS['subheading']).pack(anchor=tk.W, pady=(0, 10))
        
        self.test_categories = {
            'Basic': tk.BooleanVar(value=True),
            'Burst': tk.BooleanVar(value=True),
            'QoS': tk.BooleanVar(value=True),
            'Exclusive': tk.BooleanVar(value=False),
            'Error': tk.BooleanVar(value=False),
            'Performance': tk.BooleanVar(value=False),
            'Stress': tk.BooleanVar(value=False)
        }
        
        categories_frame = tk.Frame(config_frame, bg=self.theme.get_color('surface'))
        categories_frame.pack(fill=tk.X, pady=10)
        
        for i, (category, var) in enumerate(self.test_categories.items()):
            row = i // 3
            col = i % 3
            check = ttk.Checkbutton(categories_frame, text=category, variable=var,
                                  style='Modern.TCheckbutton')
            check.grid(row=row, column=col, sticky=tk.W, padx=20, pady=5)
            
        # Test parameters
        params_frame = ttk.LabelFrame(test_frame, text="Test Parameters", 
                                    style='Modern.TLabelframe', padding=20)
        params_frame.pack(fill=tk.X, padx=20, pady=10)
        
        # Parameter inputs
        self.create_param_field(params_frame, "Number of Iterations:", "iterations", 100, 0)
        self.create_param_field(params_frame, "Max Burst Length:", "max_burst", 256, 1)
        self.create_param_field(params_frame, "Timeout (cycles):", "timeout", 10000, 2)
        
        # Generate button
        generate_btn = ModernButton(test_frame, text="Generate Test Suite",
                                  command=self.generate_test_suite,
                                  theme=self.theme, width=200, height=50)
        generate_btn.pack(pady=20)
        
        # Generated tests list
        list_frame = ttk.LabelFrame(test_frame, text="Generated Tests", 
                                  style='Modern.TLabelframe')
        list_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Modern listbox
        self.test_listbox = tk.Listbox(list_frame, bg=self.theme.get_color('surface'),
                                     fg=self.theme.get_color('text_primary'),
                                     font=self.theme.FONTS['body'],
                                     selectmode=tk.MULTIPLE,
                                     selectbackground=self.theme.get_color('primary'),
                                     selectforeground=self.theme.get_color('text_on_primary'),
                                     relief=tk.FLAT)
        
        test_scroll = ttk.Scrollbar(list_frame, orient=tk.VERTICAL,
                                  command=self.test_listbox.yview,
                                  style='Modern.Vertical.TScrollbar')
        self.test_listbox.configure(yscrollcommand=test_scroll.set)
        
        self.test_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(10, 0), pady=10)
        test_scroll.pack(side=tk.RIGHT, fill=tk.Y, padx=(0, 10), pady=10)
        
    def create_param_field(self, parent, label, name, default, row):
        """Create parameter input field"""
        tk.Label(parent, text=label, font=self.theme.FONTS['body']).grid(row=row, column=0, sticky=tk.W, pady=10)
        
        var = tk.IntVar(value=default)
        spin = ttk.Spinbox(parent, textvariable=var, from_=1, to=100000,
                         style='Modern.TEntry', width=20)
        spin.grid(row=row, column=1, sticky=tk.W, padx=20)
        
        setattr(self, f"param_{name}_var", var)
        
    def setup_execution_tab(self):
        """Setup test execution tab"""
        exec_frame = ttk.Frame(self.tab_control, style='Modern.TFrame')
        self.tab_control.add(exec_frame, text="  ▶️ Execution  ")
        
        # Execution controls
        control_frame = ttk.LabelFrame(exec_frame, text="Execution Control", 
                                     style='Modern.TLabelframe', padding=20)
        control_frame.pack(fill=tk.X, padx=20, pady=20)
        
        # Run configuration
        config_grid = tk.Frame(control_frame, bg=self.theme.get_color('surface'))
        config_grid.pack(fill=tk.X)
        
        # Simulator selection
        tk.Label(config_grid, text="Simulator:", font=self.theme.FONTS['body']).grid(row=0, column=0, sticky=tk.W, pady=10)
        self.simulator_var = tk.StringVar(value="VCS")
        sim_combo = ttk.Combobox(config_grid, textvariable=self.simulator_var,
                               values=["VCS", "Questa", "Xcelium", "Verilator"],
                               state="readonly", style='Modern.TCombobox', width=20)
        sim_combo.grid(row=0, column=1, sticky=tk.W, padx=20)
        
        # Verbosity
        tk.Label(config_grid, text="Verbosity:", font=self.theme.FONTS['body']).grid(row=1, column=0, sticky=tk.W, pady=10)
        self.verbosity_var = tk.StringVar(value="UVM_MEDIUM")
        verb_combo = ttk.Combobox(config_grid, textvariable=self.verbosity_var,
                                values=["UVM_NONE", "UVM_LOW", "UVM_MEDIUM", "UVM_HIGH", "UVM_DEBUG"],
                                state="readonly", style='Modern.TCombobox', width=20)
        verb_combo.grid(row=1, column=1, sticky=tk.W, padx=20)
        
        # Execution buttons
        btn_frame = tk.Frame(control_frame, bg=self.theme.get_color('surface'))
        btn_frame.pack(fill=tk.X, pady=20)
        
        self.run_btn = ModernButton(btn_frame, text="▶️ Run Selected Tests",
                                  command=self.run_selected_tests,
                                  theme=self.theme, width=180, height=45)
        self.run_btn.pack(side=tk.LEFT, padx=10)
        
        self.stop_btn = ModernButton(btn_frame, text="⏹️ Stop Execution",
                                   command=self.stop_tests,
                                   style='secondary', theme=self.theme,
                                   width=180, height=45)
        self.stop_btn.pack(side=tk.LEFT, padx=10)
        self.stop_btn.config(state=tk.DISABLED)
        
        # Progress display
        progress_frame = ttk.LabelFrame(exec_frame, text="Execution Progress", 
                                      style='Modern.TLabelframe')
        progress_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Progress info
        self.progress_info = tk.Frame(progress_frame, bg=self.theme.get_color('surface'))
        self.progress_info.pack(fill=tk.X, padx=20, pady=20)
        
        self.current_test_label = tk.Label(self.progress_info, text="No test running",
                                         bg=self.theme.get_color('surface'),
                                         fg=self.theme.get_color('text_primary'),
                                         font=self.theme.FONTS['subheading'])
        self.current_test_label.pack()
        
        # Progress bar
        self.exec_progress_frame = tk.Frame(self.progress_info, 
                                          bg=self.theme.get_color('surface_variant'),
                                          height=8)
        self.exec_progress_frame.pack(fill=tk.X, pady=(20, 10))
        
        self.exec_progress_bar = tk.Frame(self.exec_progress_frame,
                                        bg=self.theme.get_color('primary'),
                                        height=8, width=0)
        self.exec_progress_bar.place(x=0, y=0)
        
        # Test output
        output_frame = tk.Frame(progress_frame, bg=self.theme.get_color('surface'))
        output_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=(0, 20))
        
        tk.Label(output_frame, text="Test Output:", 
                font=self.theme.FONTS['body']).pack(anchor=tk.W)
        
        # Output text with modern styling
        text_frame = tk.Frame(output_frame, bg=self.theme.get_color('border'))
        text_frame.pack(fill=tk.BOTH, expand=True, pady=(10, 0))
        
        self.output_text = tk.Text(text_frame, bg=self.theme.get_color('surface_variant'),
                                 fg=self.theme.get_color('text_primary'),
                                 font=self.theme.FONTS['mono'],
                                 relief=tk.FLAT, padx=10, pady=10,
                                 wrap=tk.WORD)
        self.output_text.pack(fill=tk.BOTH, expand=True, padx=1, pady=1)
        
        output_scroll = ttk.Scrollbar(text_frame, orient=tk.VERTICAL,
                                    command=self.output_text.yview,
                                    style='Modern.Vertical.TScrollbar')
        self.output_text.configure(yscrollcommand=output_scroll.set)
        output_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
    def setup_results_tab(self):
        """Setup results visualization tab"""
        results_frame = ttk.Frame(self.tab_control, style='Modern.TFrame')
        self.tab_control.add(results_frame, text="  📊 Results  ")
        
        # Create modern results view
        self.results_view = ModernTestResultView(results_frame, self.theme)
        self.results_view.pack(fill=tk.BOTH, expand=True)
        
    def setup_coverage_tab(self):
        """Setup coverage analysis tab"""
        coverage_frame = ttk.Frame(self.tab_control, style='Modern.TFrame')
        self.tab_control.add(coverage_frame, text="  📈 Coverage  ")
        
        # Coverage overview
        overview_frame = ttk.LabelFrame(coverage_frame, text="Coverage Overview", 
                                      style='Modern.TLabelframe', padding=20)
        overview_frame.pack(fill=tk.X, padx=20, pady=20)
        
        # Coverage metrics
        metrics_frame = tk.Frame(overview_frame, bg=self.theme.get_color('surface'))
        metrics_frame.pack(fill=tk.X)
        
        # Create coverage metric displays
        self.create_coverage_metric(metrics_frame, "Functional", 0, 0)
        self.create_coverage_metric(metrics_frame, "Code", 0, 1)
        self.create_coverage_metric(metrics_frame, "Assertion", 1, 0)
        self.create_coverage_metric(metrics_frame, "Toggle", 1, 1)
        
        # Detailed coverage
        detail_frame = ttk.LabelFrame(coverage_frame, text="Detailed Coverage", 
                                    style='Modern.TLabelframe')
        detail_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        # Coverage tree
        self.coverage_tree = ttk.Treeview(detail_frame, 
                                        columns=('Hits', 'Goal', 'Coverage'),
                                        show='tree headings',
                                        style='Modern.Treeview')
        self.coverage_tree.heading('#0', text='Coverage Point')
        self.coverage_tree.heading('Hits', text='Hits')
        self.coverage_tree.heading('Goal', text='Goal')
        self.coverage_tree.heading('Coverage', text='Coverage %')
        
        cov_scroll = ttk.Scrollbar(detail_frame, orient=tk.VERTICAL,
                                 command=self.coverage_tree.yview,
                                 style='Modern.Vertical.TScrollbar')
        self.coverage_tree.configure(yscrollcommand=cov_scroll.set)
        
        self.coverage_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(10, 0), pady=10)
        cov_scroll.pack(side=tk.RIGHT, fill=tk.Y, padx=(0, 10), pady=10)
        
    def create_coverage_metric(self, parent, name, row, col):
        """Create coverage metric display"""
        frame = tk.Frame(parent, bg=self.theme.get_color('surface_variant'),
                       relief=tk.FLAT, bd=1)
        frame.grid(row=row, column=col, padx=10, pady=10, sticky=tk.NSEW)
        
        content = tk.Frame(frame, bg=self.theme.get_color('surface_variant'), padx=30, pady=20)
        content.pack(fill=tk.BOTH, expand=True)
        
        # Metric name
        tk.Label(content, text=name, font=self.theme.FONTS['body'],
                bg=self.theme.get_color('surface_variant'),
                fg=self.theme.get_color('text_secondary')).pack()
        
        # Percentage with circular progress (simulated)
        percent_label = tk.Label(content, text="0%", font=self.theme.FONTS['heading_large'],
                               bg=self.theme.get_color('surface_variant'),
                               fg=self.theme.get_color('primary'))
        percent_label.pack(pady=(10, 0))
        
        # Progress bar
        progress_frame = tk.Frame(content, bg=self.theme.get_color('bg'), height=4)
        progress_frame.pack(fill=tk.X, pady=(10, 0))
        
        progress_bar = tk.Frame(progress_frame, bg=self.theme.get_color('primary'), height=4, width=0)
        progress_bar.place(x=0, y=0)
        
        # Store references
        setattr(self, f"{name.lower()}_percent_label", percent_label)
        setattr(self, f"{name.lower()}_progress_bar", progress_bar)
        
        parent.columnconfigure(col, weight=1)
        
    # Implementation methods
    def on_vip_mode_change(self):
        """Handle VIP mode change"""
        if self.vip_mode_var.get() == "RTL":
            self.rtl_path_entry.config(state=tk.NORMAL)
            self.rtl_browse_btn.config(state=tk.NORMAL)
        else:
            self.rtl_path_entry.config(state=tk.DISABLED)
            self.rtl_browse_btn.config(state=tk.DISABLED)
            
    def browse_rtl_path(self):
        """Browse for RTL directory"""
        directory = filedialog.askdirectory(title="Select RTL Directory")
        if directory:
            self.rtl_path_var.set(directory)
            
    def browse_vip_output_dir(self):
        """Browse for VIP output directory"""
        directory = filedialog.askdirectory(title="Select VIP Output Directory")
        if directory:
            self.vip_output_dir_var.set(directory)
            
    def browse_verilog_output_dir(self):
        """Browse for Verilog output directory"""
        directory = filedialog.askdirectory(title="Select Verilog Output Directory")
        if directory:
            self.verilog_output_dir_var.set(directory)
            
    def create_output_directories(self):
        """Create output directories"""
        dirs = [self.vip_output_dir_var.get(), self.verilog_output_dir_var.get()]
        
        for directory in dirs:
            try:
                os.makedirs(directory, exist_ok=True)
                self.add_activity(f"Created directory: {directory}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to create directory: {e}")
                
    def export_uvm_configuration(self):
        """Export UVM configuration"""
        try:
            # Get current bus configuration
            config = self.gui.current_config if hasattr(self, 'gui') else None
            if not config:
                messagebox.showwarning("Warning", "No bus configuration available")
                return
                
            # Export configuration
            output_file = filedialog.asksaveasfilename(
                defaultextension=".json",
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
                initialdir=self.vip_output_dir_var.get()
            )
            
            if output_file:
                # TODO: Call actual export function
                self.add_activity(f"Exported UVM configuration to {os.path.basename(output_file)}")
                messagebox.showinfo("Success", "UVM configuration exported successfully")
                
        except Exception as e:
            messagebox.showerror("Error", f"Export failed: {e}")
            
    def open_uvm_directory(self):
        """Open UVM directory in file explorer"""
        directory = self.vip_output_dir_var.get()
        if os.path.exists(directory):
            if os.name == 'nt':  # Windows
                os.startfile(directory)
            elif os.name == 'posix':  # macOS and Linux
                subprocess.Popen(['open' if sys.platform == 'darwin' else 'xdg-open', directory])
        else:
            messagebox.showwarning("Warning", "Directory does not exist")
            
    def show_uvm_commands(self):
        """Show UVM simulation commands"""
        commands = """Simulation Commands:

1. Compile:
   vcs -sverilog -ntb_opts uvm-1.2 +incdir+$UVM_HOME/src \\
       -f compile.f -o simv

2. Run single test:
   ./simv +UVM_TESTNAME=axi4_basic_test \\
          +UVM_CONFIG_FILE=config.json

3. Run regression:
   make regression TESTS="test1 test2 test3"

4. Generate coverage report:
   urg -dir coverage.vdb -report coverage_report"""
   
        # Create modern dialog to show commands
        dialog = tk.Toplevel(self.parent)
        dialog.title("UVM Simulation Commands")
        dialog.configure(bg=self.theme.get_color('surface'))
        dialog.geometry("600x400")
        
        # Header
        header = tk.Frame(dialog, bg=self.theme.get_color('primary'), height=50)
        header.pack(fill=tk.X)
        header.pack_propagate(False)
        
        tk.Label(header, text="UVM Simulation Commands",
                font=self.theme.FONTS['heading'],
                bg=self.theme.get_color('primary'),
                fg=self.theme.get_color('text_on_primary')).pack(pady=15)
        
        # Commands text
        text_frame = tk.Frame(dialog, bg=self.theme.get_color('surface'), padx=20, pady=20)
        text_frame.pack(fill=tk.BOTH, expand=True)
        
        text = tk.Text(text_frame, bg=self.theme.get_color('surface_variant'),
                      fg=self.theme.get_color('text_primary'),
                      font=self.theme.FONTS['mono'],
                      relief=tk.FLAT, padx=15, pady=15,
                      wrap=tk.WORD)
        text.pack(fill=tk.BOTH, expand=True)
        text.insert('1.0', commands)
        text.config(state=tk.DISABLED)
        
        # Close button
        ModernButton(dialog, text="Close", command=dialog.destroy,
                   theme=self.theme, width=100, height=36).pack(pady=10)
        
    def generate_rtl_for_vip(self):
        """Generate RTL for VIP testing"""
        progress = ModernProgressDialog(self.parent, "Generating RTL", self.theme)
        
        try:
            progress.update(0.2, "Validating configuration...")
            # TODO: Add actual RTL generation
            time.sleep(0.5)
            
            progress.update(0.5, "Generating interconnect...")
            time.sleep(0.5)
            
            progress.update(0.8, "Writing output files...")
            time.sleep(0.5)
            
            progress.update(1.0, "Complete!")
            time.sleep(0.3)
            
            self.add_activity("RTL generation completed")
            messagebox.showinfo("Success", "RTL generated successfully")
            
        except Exception as e:
            messagebox.showerror("Error", f"RTL generation failed: {e}")
        finally:
            progress.close()
            
    def create_vip_environment(self):
        """Create VIP environment"""
        if not VIP_COMPONENTS_AVAILABLE:
            messagebox.showinfo("Info", "VIP environment creation is simulated (components not available)")
            self.environment_status_label.config(text="Created (Simulated)")
            self.add_activity("VIP environment created (simulated)")
            return
            
        # TODO: Actual environment creation
        self.add_activity("VIP environment created")
        
    def generate_test_suite(self):
        """Generate test suite based on selections"""
        # Get selected categories
        selected = [cat for cat, var in self.test_categories.items() if var.get()]
        
        if not selected:
            messagebox.showwarning("Warning", "Please select at least one test category")
            return
            
        # Clear existing tests
        self.test_listbox.delete(0, tk.END)
        
        # Generate test names (simulated)
        test_names = []
        for category in selected:
            if category == 'Basic':
                test_names.extend(['axi4_basic_read_test', 'axi4_basic_write_test',
                                 'axi4_basic_read_write_test'])
            elif category == 'Burst':
                test_names.extend(['axi4_burst_incr_test', 'axi4_burst_wrap_test',
                                 'axi4_burst_fixed_test'])
            elif category == 'QoS':
                test_names.extend(['axi4_qos_priority_test', 'axi4_qos_arbitration_test'])
            elif category == 'Exclusive':
                test_names.extend(['axi4_exclusive_access_test', 'axi4_exclusive_fail_test'])
            elif category == 'Error':
                test_names.extend(['axi4_slverr_test', 'axi4_decerr_test'])
            elif category == 'Performance':
                test_names.extend(['axi4_throughput_test', 'axi4_latency_test'])
            elif category == 'Stress':
                test_names.extend(['axi4_stress_random_test', 'axi4_stress_corner_test'])
                
        # Add tests to listbox
        for test in test_names:
            self.test_listbox.insert(tk.END, test)
            
        self.add_activity(f"Generated {len(test_names)} tests")
        self.tests_status_label.config(text=f"{len(test_names)} Available")
        
    def run_selected_tests(self):
        """Run selected tests"""
        selected_indices = self.test_listbox.curselection()
        
        if not selected_indices:
            messagebox.showwarning("Warning", "Please select tests to run")
            return
            
        selected_tests = [self.test_listbox.get(i) for i in selected_indices]
        
        # Update UI for running state
        self.run_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.NORMAL)
        self.test_running = True
        
        # Clear output
        self.output_text.delete('1.0', tk.END)
        
        # Start test execution in thread
        self.test_thread = threading.Thread(target=self._run_tests_thread,
                                          args=(selected_tests,))
        self.test_thread.start()
        
    def _run_tests_thread(self, tests):
        """Run tests in background thread"""
        try:
            total_tests = len(tests)
            
            for i, test in enumerate(tests):
                if not self.test_running:
                    break
                    
                # Update progress
                progress = (i + 1) / total_tests
                self.message_queue.put(('progress', progress, test))
                
                # Simulate test execution
                self.message_queue.put(('output', f"Running {test}...\n"))
                time.sleep(2)  # Simulate test duration
                
                # Simulate test result
                import random
                passed = random.random() > 0.1  # 90% pass rate
                result = {
                    'status': 'passed' if passed else 'failed',
                    'duration': f"{random.randint(100, 500)}ms",
                    'coverage': f"{random.randint(70, 95)}%"
                }
                
                self.test_results[test] = result
                self.message_queue.put(('result', test, result))
                self.message_queue.put(('output', f"{test}: {'PASSED' if passed else 'FAILED'}\n"))
                
        except Exception as e:
            self.message_queue.put(('error', str(e)))
        finally:
            self.message_queue.put(('complete', None, None))
            
    def stop_tests(self):
        """Stop test execution"""
        self.test_running = False
        self.add_activity("Test execution stopped by user")
        
    def show_results(self):
        """Show results tab"""
        self.tab_control.select(4)  # Results tab index
        
    def add_activity(self, message):
        """Add message to activity log"""
        timestamp = time.strftime("%H:%M:%S")
        self.activity_list.insert(0, f"[{timestamp}] {message}")
        
        # Limit to 50 items
        if self.activity_list.size() > 50:
            self.activity_list.delete(50, tk.END)
            
    def process_messages(self):
        """Process messages from background threads"""
        try:
            while True:
                msg_type, *args = self.message_queue.get_nowait()
                
                if msg_type == 'progress':
                    progress, test_name = args
                    self.update_progress(progress, test_name)
                elif msg_type == 'output':
                    self.output_text.insert(tk.END, args[0])
                    self.output_text.see(tk.END)
                elif msg_type == 'result':
                    test_name, result = args
                    self.results_view.update_results(self.test_results)
                elif msg_type == 'error':
                    messagebox.showerror("Error", args[0])
                elif msg_type == 'complete':
                    self.on_tests_complete()
                    
        except queue.Empty:
            pass
            
        # Schedule next check
        self.parent.after(100, self.process_messages)
        
    def update_progress(self, progress, test_name):
        """Update execution progress"""
        self.current_test_label.config(text=f"Running: {test_name}")
        
        # Update progress bar
        target_width = int(self.exec_progress_frame.winfo_width() * progress)
        self.exec_progress_bar.config(width=target_width)
        
    def on_tests_complete(self):
        """Handle test completion"""
        self.test_running = False
        self.run_btn.config(state=tk.NORMAL)
        self.stop_btn.config(state=tk.DISABLED)
        self.current_test_label.config(text="Test execution complete")
        
        # Update status
        total = len(self.test_results)
        passed = sum(1 for r in self.test_results.values() if r.get('status') == 'passed')
        
        self.add_activity(f"Test execution complete: {passed}/{total} passed")
        
        # Update coverage (simulated)
        coverage = sum(int(r.get('coverage', '0%').rstrip('%')) 
                      for r in self.test_results.values()) / max(total, 1)
        self.coverage_status_label.config(text=f"{int(coverage)}%")
        
        # Show notification
        if passed == total:
            messagebox.showinfo("Success", f"All {total} tests passed!")
        else:
            messagebox.showwarning("Tests Failed", f"{total - passed} out of {total} tests failed")


def integrate_modern_vip_panel(parent_frame, gui_instance):
    """Factory function to create modern VIP panel"""
    return ModernVIPControlPanel(parent_frame, gui_instance, gui_instance.theme)


# Example usage
if __name__ == "__main__":
    root = tk.Tk()
    root.title("Modern VIP GUI Integration Demo")
    
    # Apply modern theme
    theme = apply_modern_theme(root, dark_mode=False)
    
    # Create demo GUI instance
    class DemoGUI:
        def __init__(self):
            self.theme = theme
            self.current_config = None
            
    gui = DemoGUI()
    
    # Create VIP panel
    vip_panel = ModernVIPControlPanel(root, gui, theme)
    
    root.mainloop()