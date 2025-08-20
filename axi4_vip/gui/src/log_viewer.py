#!/usr/bin/env python3
"""
Log Viewer and Batch Management GUI Components
Provides real-time log display and batch processing controls
"""

import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog
import threading
import queue
import time
from datetime import datetime
from pathlib import Path
import logging

from logger import get_logger, get_recent_logs, setup_gui_logging
from batch_processor import get_batch_processor, BatchTask, BatchResult
from bus_config import Project


class LogViewer(ttk.Frame):
    """Real-time log viewer widget"""
    
    def __init__(self, parent, **kwargs):
        super().__init__(parent, **kwargs)
        
        self.logger = get_logger("log_viewer")
        self.log_queue = queue.Queue()
        self.running = False
        
        self.create_widgets()
        self.setup_logging()
    
    def create_widgets(self):
        """Create log viewer widgets"""
        # Controls frame
        controls_frame = ttk.Frame(self)
        controls_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # Log level filter
        ttk.Label(controls_frame, text="Level:").pack(side=tk.LEFT, padx=5)
        self.level_var = tk.StringVar(value="INFO")
        level_combo = ttk.Combobox(controls_frame, textvariable=self.level_var,
                                   values=["DEBUG", "INFO", "WARNING", "ERROR"],
                                   state="readonly", width=10)
        level_combo.pack(side=tk.LEFT, padx=5)
        level_combo.bind('<<ComboboxSelected>>', self.on_level_changed)
        
        # Auto-scroll checkbox
        self.auto_scroll_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(controls_frame, text="Auto-scroll", 
                       variable=self.auto_scroll_var).pack(side=tk.LEFT, padx=10)
        
        # Clear button
        ttk.Button(controls_frame, text="Clear", 
                  command=self.clear_logs).pack(side=tk.RIGHT, padx=5)
        
        # Save button
        ttk.Button(controls_frame, text="Save Log", 
                  command=self.save_log).pack(side=tk.RIGHT, padx=5)
        
        # Log text widget with scrollbar
        text_frame = ttk.Frame(self)
        text_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        self.log_text = scrolledtext.ScrolledText(text_frame, height=20, width=80,
                                                  font=('Consolas', 9),
                                                  wrap=tk.WORD)
        self.log_text.pack(fill=tk.BOTH, expand=True)
        
        # Configure text tags for different log levels
        self.log_text.tag_config("DEBUG", foreground="gray")
        self.log_text.tag_config("INFO", foreground="black")
        self.log_text.tag_config("WARNING", foreground="orange")
        self.log_text.tag_config("ERROR", foreground="red")
        self.log_text.tag_config("CRITICAL", foreground="red", background="yellow")
        
        # Status bar
        self.status_var = tk.StringVar(value="Log viewer ready")
        status_bar = ttk.Label(self, textvariable=self.status_var, relief=tk.SUNKEN)
        status_bar.pack(fill=tk.X, side=tk.BOTTOM)
    
    def setup_logging(self):
        """Setup logging callback"""
        def log_callback(level, message, timestamp):
            try:
                self.log_queue.put((level, message, timestamp))
            except Exception:
                pass  # Ignore queue errors
        
        setup_gui_logging(log_callback)
        
        # Start log processing thread
        self.running = True
        self.log_thread = threading.Thread(target=self._process_logs, daemon=True)
        self.log_thread.start()
        
        # Load recent logs
        self.load_recent_logs()
    
    def _process_logs(self):
        """Process log messages from queue"""
        while self.running:
            try:
                level, message, timestamp = self.log_queue.get(timeout=0.1)
                self.after(0, self._add_log_message, level, message, timestamp)
            except queue.Empty:
                continue
            except Exception as e:
                print(f"Error processing logs: {e}")
    
    def _add_log_message(self, level, message, timestamp):
        """Add log message to text widget"""
        # Check level filter
        min_level = getattr(logging, self.level_var.get())
        if level < min_level:
            return
        
        # Format timestamp
        dt = datetime.fromtimestamp(timestamp)
        time_str = dt.strftime("%H:%M:%S.%f")[:-3]  # Include milliseconds
        
        # Format level name
        level_name = logging.getLevelName(level)
        
        # Create formatted message
        formatted_msg = f"{time_str} {level_name:8} {message}\n"
        
        # Insert message with appropriate tag
        self.log_text.insert(tk.END, formatted_msg, level_name)
        
        # Auto-scroll if enabled
        if self.auto_scroll_var.get():
            self.log_text.see(tk.END)
        
        # Update status
        total_lines = int(self.log_text.index(tk.END).split('.')[0]) - 1
        self.status_var.set(f"Log lines: {total_lines}")
    
    def load_recent_logs(self):
        """Load recent logs from logger"""
        try:
            recent_logs = get_recent_logs(100)
            for level, message, timestamp in recent_logs:
                self._add_log_message(level, message, timestamp)
        except Exception as e:
            self.logger.exception(f"Error loading recent logs: {e}")
    
    def on_level_changed(self, event=None):
        """Handle log level filter change"""
        # Could implement re-filtering existing messages here
        self.logger.info(f"Log level filter changed to {self.level_var.get()}")
    
    def clear_logs(self):
        """Clear log display"""
        self.log_text.delete(1.0, tk.END)
        self.status_var.set("Log cleared")
        self.logger.info("Log display cleared")
    
    def save_log(self):
        """Save current log to file"""
        try:
            filename = filedialog.asksaveasfilename(
                title="Save Log File",
                defaultextension=".log",
                filetypes=[("Log files", "*.log"), ("Text files", "*.txt"), ("All files", "*.*")]
            )
            
            if filename:
                content = self.log_text.get(1.0, tk.END)
                with open(filename, 'w') as f:
                    f.write(content)
                
                self.logger.info(f"Log saved to {filename}")
                messagebox.showinfo("Success", f"Log saved to {filename}")
        
        except Exception as e:
            self.logger.exception(f"Error saving log: {e}")
            messagebox.showerror("Error", f"Failed to save log: {e}")
    
    def destroy(self):
        """Cleanup when widget is destroyed"""
        self.running = False
        if hasattr(self, 'log_thread'):
            self.log_thread.join(timeout=1)
        super().destroy()


class BatchManager(ttk.Frame):
    """Batch processing management interface"""
    
    def __init__(self, parent, **kwargs):
        super().__init__(parent, **kwargs)
        
        self.logger = get_logger("batch_manager")
        self.batch_processor = get_batch_processor()
        self.task_results = {}
        
        self.create_widgets()
        self.setup_batch_processor()
    
    def create_widgets(self):
        """Create batch management widgets"""
        # Control buttons frame
        control_frame = ttk.LabelFrame(self, text="Batch Controls", padding=10)
        control_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(control_frame, text="Start Processor", 
                  command=self.start_processor).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Stop Processor", 
                  command=self.stop_processor).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Create Template Batch", 
                  command=self.create_template_batch).pack(side=tk.LEFT, padx=10)
        
        # Status frame
        status_frame = ttk.LabelFrame(self, text="Status", padding=10)
        status_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.status_text = tk.Text(status_frame, height=4, width=60,
                                   font=('Consolas', 9))
        self.status_text.pack(fill=tk.X)
        
        # Task list frame
        task_frame = ttk.LabelFrame(self, text="Tasks", padding=10)
        task_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Task treeview
        columns = ("Task ID", "Type", "Status", "Duration", "Files", "Progress")
        self.task_tree = ttk.Treeview(task_frame, columns=columns, show="headings", height=10)
        
        for col in columns:
            self.task_tree.heading(col, text=col)
            self.task_tree.column(col, width=100)
        
        # Scrollbars for treeview
        tree_scrolly = ttk.Scrollbar(task_frame, orient=tk.VERTICAL, command=self.task_tree.yview)
        tree_scrollx = ttk.Scrollbar(task_frame, orient=tk.HORIZONTAL, command=self.task_tree.xview)
        self.task_tree.configure(yscrollcommand=tree_scrolly.set, xscrollcommand=tree_scrollx.set)
        
        # Pack treeview and scrollbars
        self.task_tree.grid(row=0, column=0, sticky="nsew")
        tree_scrolly.grid(row=0, column=1, sticky="ns")
        tree_scrollx.grid(row=1, column=0, sticky="ew")
        
        task_frame.grid_rowconfigure(0, weight=1)
        task_frame.grid_columnconfigure(0, weight=1)
        
        # Task details frame
        details_frame = ttk.LabelFrame(self, text="Task Details", padding=10)
        details_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.details_text = tk.Text(details_frame, height=6, width=60,
                                   font=('Consolas', 9))
        self.details_text.pack(fill=tk.X)
        
        # Bind treeview selection
        self.task_tree.bind("<<TreeviewSelect>>", self.on_task_selected)
        
        # Auto-refresh timer
        self.auto_refresh()
    
    def setup_batch_processor(self):
        """Setup batch processor callbacks"""
        def task_completed_callback(task_id, result):
            self.task_results[task_id] = result
            self.after(0, self.refresh_task_list)
        
        self.batch_processor.add_status_callback(task_completed_callback)
    
    def start_processor(self):
        """Start batch processor"""
        try:
            self.batch_processor.start()
            self.logger.info("Batch processor started")
            messagebox.showinfo("Success", "Batch processor started")
        except Exception as e:
            self.logger.exception(f"Error starting batch processor: {e}")
            messagebox.showerror("Error", f"Failed to start batch processor: {e}")
    
    def stop_processor(self):
        """Stop batch processor"""
        try:
            self.batch_processor.stop()
            self.logger.info("Batch processor stopped")
            messagebox.showinfo("Success", "Batch processor stopped")
        except Exception as e:
            self.logger.exception(f"Error stopping batch processor: {e}")
            messagebox.showerror("Error", f"Failed to stop batch processor: {e}")
    
    def create_template_batch(self):
        """Create batch from templates dialog"""
        dialog = TemplateBatchDialog(self)
        if dialog.result:
            templates = dialog.result
            try:
                tasks = self.batch_processor.create_batch_from_templates(templates)
                self.logger.info(f"Created batch with {len(tasks)} tasks")
                messagebox.showinfo("Success", f"Created batch with {len(tasks)} tasks")
                self.refresh_task_list()
            except Exception as e:
                self.logger.exception(f"Error creating template batch: {e}")
                messagebox.showerror("Error", f"Failed to create batch: {e}")
    
    def refresh_status(self):
        """Refresh processor status display"""
        try:
            status = self.batch_processor.get_status()
            
            status_text = f"Running: {status['running']}\n"
            status_text += f"Workers: {status['workers']}\n"
            
            if status['uptime']:
                status_text += f"Uptime: {status['uptime']:.0f}s\n"
            
            queue_status = status['queue']
            status_text += f"Queue: {queue_status['pending']} pending, "
            status_text += f"{queue_status['active']} active, "
            status_text += f"{queue_status['completed']} completed, "
            status_text += f"{queue_status['failed']} failed"
            
            self.status_text.delete(1.0, tk.END)
            self.status_text.insert(1.0, status_text)
            
        except Exception as e:
            self.logger.exception(f"Error refreshing status: {e}")
    
    def refresh_task_list(self):
        """Refresh task list display"""
        try:
            # Clear existing items
            for item in self.task_tree.get_children():
                self.task_tree.delete(item)
            
            # Get task results
            results = self.batch_processor.get_task_results()
            all_results = {**results['completed'], **results['failed']}
            
            # Add completed and failed tasks
            for task_id, result in all_results.items():
                status = "COMPLETED" if result.success else "FAILED"
                duration = f"{result.duration:.1f}s"
                file_count = len(result.output_files)
                progress = "100%" if result.success else "Error"
                
                self.task_tree.insert("", tk.END, values=(
                    task_id, "Unknown", status, duration, file_count, progress
                ))
            
            # Get active tasks from queue status
            queue_status = self.batch_processor.batch_queue.get_task_list()
            for task_id in queue_status['active']:
                self.task_tree.insert("", tk.END, values=(
                    task_id, "Unknown", "RUNNING", "-", "-", "In Progress"
                ))
                
        except Exception as e:
            self.logger.exception(f"Error refreshing task list: {e}")
    
    def on_task_selected(self, event):
        """Handle task selection in treeview"""
        selection = self.task_tree.selection()
        if selection:
            item = selection[0]
            task_id = self.task_tree.item(item)['values'][0]
            
            # Show task details
            if task_id in self.task_results:
                result = self.task_results[task_id]
                details = f"Task ID: {task_id}\n"
                details += f"Success: {result.success}\n"
                details += f"Duration: {result.duration:.2f}s\n"
                details += f"Output Files: {len(result.output_files)}\n"
                
                if result.error_message:
                    details += f"Error: {result.error_message}\n"
                
                if result.warnings:
                    details += f"Warnings: {len(result.warnings)}\n"
                
                if result.log_file:
                    details += f"Log File: {result.log_file}\n"
                
                self.details_text.delete(1.0, tk.END)
                self.details_text.insert(1.0, details)
    
    def auto_refresh(self):
        """Auto-refresh status and task list"""
        self.refresh_status()
        self.refresh_task_list()
        self.after(2000, self.auto_refresh)  # Refresh every 2 seconds


class TemplateBatchDialog:
    """Dialog for creating batch from templates"""
    
    def __init__(self, parent):
        self.result = None
        
        # Create dialog window
        self.dialog = tk.Toplevel(parent)
        self.dialog.title("Create Template Batch")
        self.dialog.geometry("400x300")
        self.dialog.transient(parent)
        self.dialog.grab_set()
        
        # Center dialog
        self.dialog.update_idletasks()
        x = (self.dialog.winfo_screenwidth() // 2) - 200
        y = (self.dialog.winfo_screenheight() // 2) - 150
        self.dialog.geometry(f"400x300+{x}+{y}")
        
        self.create_widgets()
    
    def create_widgets(self):
        """Create dialog widgets"""
        # Instructions
        ttk.Label(self.dialog, text="Select templates to include in batch:",
                 font=('Arial', 10, 'bold')).pack(pady=10)
        
        # Template checkboxes
        self.template_vars = {}
        templates = [
            ("AXI 8×8", "axi_8x8"),
            ("AXI 16×16", "axi_16x16"),
            ("AXI 32×32", "axi_32x32"),
            ("AHB-Lite", "ahb_lite")
        ]
        
        for display_name, template_id in templates:
            var = tk.BooleanVar()
            self.template_vars[template_id] = var
            ttk.Checkbutton(self.dialog, text=display_name, variable=var).pack(anchor=tk.W, padx=20)
        
        # Buttons
        button_frame = ttk.Frame(self.dialog)
        button_frame.pack(pady=20)
        
        ttk.Button(button_frame, text="Create Batch", 
                  command=self.create_batch).pack(side=tk.LEFT, padx=10)
        ttk.Button(button_frame, text="Cancel", 
                  command=self.cancel).pack(side=tk.LEFT, padx=10)
    
    def create_batch(self):
        """Create batch with selected templates"""
        selected = [template_id for template_id, var in self.template_vars.items() if var.get()]
        
        if not selected:
            messagebox.showwarning("Warning", "Please select at least one template")
            return
        
        self.result = selected
        self.dialog.destroy()
    
    def cancel(self):
        """Cancel dialog"""
        self.result = None
        self.dialog.destroy()


# Example usage
if __name__ == "__main__":
    root = tk.Tk()
    root.title("Log Viewer and Batch Manager Test")
    
    # Create notebook
    notebook = ttk.Notebook(root)
    notebook.pack(fill=tk.BOTH, expand=True)
    
    # Add log viewer tab
    log_frame = ttk.Frame(notebook)
    notebook.add(log_frame, text="Logs")
    log_viewer = LogViewer(log_frame)
    log_viewer.pack(fill=tk.BOTH, expand=True)
    
    # Add batch manager tab
    batch_frame = ttk.Frame(notebook)
    notebook.add(batch_frame, text="Batch")
    batch_manager = BatchManager(batch_frame)
    batch_manager.pack(fill=tk.BOTH, expand=True)
    
    # Test logging
    logger = get_logger("test")
    logger.info("Test application started")
    logger.warning("This is a test warning")
    logger.error("This is a test error")
    
    root.mainloop()