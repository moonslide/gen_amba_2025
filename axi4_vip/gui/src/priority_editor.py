#!/usr/bin/env python3
"""
Priority Editor with Drag-and-Drop UI
For configuring fixed priority arbitration per slave
Based on gui_build.md specification
"""

import tkinter as tk
from tkinter import ttk
from typing import List, Optional
from bus_config import SlaveNode, Project

class PriorityEditor:
    """
    Drag-and-drop priority editor for fixed arbitration
    Allows ordering masters by priority for each slave
    """
    
    def __init__(self, parent, slave: SlaveNode, project: Project):
        self.parent = parent
        self.slave = slave
        self.project = project
        self.result = None
        
        # Create dialog
        self.dialog = tk.Toplevel(parent)
        self.dialog.title(f"Edit Priority — Slave: S{slave.s_index}·{slave.name}")
        self.dialog.geometry("600x500")
        self.dialog.transient(parent)
        self.dialog.grab_set()
        
        # Center dialog
        self.dialog.update_idletasks()
        x = (self.dialog.winfo_screenwidth() // 2) - 300
        y = (self.dialog.winfo_screenheight() // 2) - 250
        self.dialog.geometry(f"600x500+{x}+{y}")
        
        # Priority lists
        self.assigned_masters = []
        self.unassigned_masters = []
        
        # Initialize from slave priority
        if slave.priority and "order" in slave.priority:
            self.assigned_masters = slave.priority["order"].copy()
            # Add any missing masters to unassigned
            for master in self.project.masters:
                master_id = f"M{master.m_index}"
                if master_id not in self.assigned_masters:
                    self.unassigned_masters.append(master_id)
        else:
            # All masters unassigned initially
            self.unassigned_masters = [f"M{m.m_index}" for m in self.project.masters]
        
        self.create_ui()
    
    def create_ui(self):
        """Create the priority editor UI"""
        # Top controls
        control_frame = ttk.Frame(self.dialog)
        control_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # Search entry
        ttk.Label(control_frame, text="Search:").pack(side=tk.LEFT, padx=5)
        self.search_var = tk.StringVar()
        self.search_entry = ttk.Entry(control_frame, textvariable=self.search_var, width=20)
        self.search_entry.pack(side=tk.LEFT, padx=5)
        self.search_var.trace('w', self.on_search)
        
        # Reset button
        ttk.Button(control_frame, text="Reset", command=self.reset_priority).pack(side=tk.RIGHT, padx=5)
        
        # Main content frame
        content_frame = ttk.Frame(self.dialog)
        content_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # Assigned masters (left)
        assigned_frame = ttk.LabelFrame(content_frame, text="Assigned (highest first)", padding=10)
        assigned_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        # Assigned listbox
        self.assigned_listbox = tk.Listbox(assigned_frame, height=15, width=25)
        self.assigned_listbox.pack(fill=tk.BOTH, expand=True)
        
        # Populate assigned list
        self.refresh_assigned_list()
        
        # Bind drag events for assigned list
        self.assigned_listbox.bind('<Button-1>', self.on_assigned_click)
        self.assigned_listbox.bind('<B1-Motion>', self.on_assigned_drag)
        self.assigned_listbox.bind('<ButtonRelease-1>', self.on_assigned_release)
        
        # Middle buttons
        middle_frame = ttk.Frame(content_frame)
        middle_frame.pack(side=tk.LEFT, padx=10)
        
        ttk.Button(middle_frame, text="→", width=3,
                  command=self.move_to_unassigned).pack(pady=5)
        ttk.Button(middle_frame, text="←", width=3,
                  command=self.move_to_assigned).pack(pady=5)
        ttk.Button(middle_frame, text="↑", width=3,
                  command=self.move_up).pack(pady=20)
        ttk.Button(middle_frame, text="↓", width=3,
                  command=self.move_down).pack(pady=5)
        
        # Unassigned masters (right)
        unassigned_frame = ttk.LabelFrame(content_frame, text="Unassigned", padding=10)
        unassigned_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5)
        
        # Unassigned listbox
        self.unassigned_listbox = tk.Listbox(unassigned_frame, height=15, width=25)
        self.unassigned_listbox.pack(fill=tk.BOTH, expand=True)
        
        # Populate unassigned list
        self.refresh_unassigned_list()
        
        # Bind events for unassigned list
        self.unassigned_listbox.bind('<Double-Button-1>', lambda e: self.move_to_assigned())
        
        # Help text
        help_frame = ttk.Frame(self.dialog)
        help_frame.pack(fill=tk.X, padx=10, pady=5)
        
        help_text = "• Drag items to reorder priority\n• Double-click to move between lists\n• Use arrows to adjust position"
        ttk.Label(help_frame, text=help_text, font=('Arial', 9), foreground='gray').pack()
        
        # Bottom buttons
        button_frame = ttk.Frame(self.dialog)
        button_frame.pack(fill=tk.X, padx=10, pady=10)
        
        ttk.Button(button_frame, text="Cancel", command=self.cancel).pack(side=tk.RIGHT, padx=5)
        ttk.Button(button_frame, text="Apply", command=self.apply).pack(side=tk.RIGHT)
        
        # Drag state
        self.drag_start_index = None
        self.drag_current_index = None
    
    def refresh_assigned_list(self):
        """Refresh the assigned masters list"""
        self.assigned_listbox.delete(0, tk.END)
        
        search_term = self.search_var.get().lower()
        
        for i, master_id in enumerate(self.assigned_masters):
            # Get master name
            master_name = self.get_master_name(master_id)
            display_text = f"☰ {master_id}·{master_name}"
            
            # Apply search filter
            if search_term and search_term not in display_text.lower():
                continue
            
            self.assigned_listbox.insert(tk.END, display_text)
            
            # Color code by priority level
            if i == 0:
                self.assigned_listbox.itemconfig(tk.END, fg='darkgreen')  # Highest
            elif i < 3:
                self.assigned_listbox.itemconfig(tk.END, fg='green')  # High
    
    def refresh_unassigned_list(self):
        """Refresh the unassigned masters list"""
        self.unassigned_listbox.delete(0, tk.END)
        
        search_term = self.search_var.get().lower()
        
        for master_id in self.unassigned_masters:
            # Get master name
            master_name = self.get_master_name(master_id)
            display_text = f"{master_id}·{master_name}"
            
            # Apply search filter
            if search_term and search_term not in display_text.lower():
                continue
            
            self.unassigned_listbox.insert(tk.END, display_text)
    
    def get_master_name(self, master_id: str) -> str:
        """Get master name from ID"""
        if master_id.startswith('M'):
            idx = int(master_id[1:])
            if 0 <= idx < len(self.project.masters):
                return self.project.masters[idx].name
        return "Unknown"
    
    def on_search(self, *args):
        """Handle search text change"""
        self.refresh_assigned_list()
        self.refresh_unassigned_list()
    
    def on_assigned_click(self, event):
        """Handle click on assigned list - start drag"""
        index = self.assigned_listbox.nearest(event.y)
        if index >= 0:
            self.drag_start_index = index
            self.drag_current_index = index
            self.assigned_listbox.selection_clear(0, tk.END)
            self.assigned_listbox.selection_set(index)
    
    def on_assigned_drag(self, event):
        """Handle drag in assigned list"""
        if self.drag_start_index is not None:
            index = self.assigned_listbox.nearest(event.y)
            if index != self.drag_current_index and 0 <= index < len(self.assigned_masters):
                # Move item in list
                item = self.assigned_masters.pop(self.drag_current_index)
                self.assigned_masters.insert(index, item)
                
                # Update display
                self.refresh_assigned_list()
                self.assigned_listbox.selection_set(index)
                
                self.drag_current_index = index
    
    def on_assigned_release(self, event):
        """Handle release after drag"""
        self.drag_start_index = None
        self.drag_current_index = None
    
    def move_to_assigned(self):
        """Move selected item from unassigned to assigned"""
        selection = self.unassigned_listbox.curselection()
        if selection:
            index = selection[0]
            text = self.unassigned_listbox.get(index)
            # Extract master ID
            master_id = text.split('·')[0]
            
            if master_id in self.unassigned_masters:
                self.unassigned_masters.remove(master_id)
                self.assigned_masters.append(master_id)
                
                self.refresh_assigned_list()
                self.refresh_unassigned_list()
    
    def move_to_unassigned(self):
        """Move selected item from assigned to unassigned"""
        selection = self.assigned_listbox.curselection()
        if selection:
            index = selection[0]
            if 0 <= index < len(self.assigned_masters):
                master_id = self.assigned_masters.pop(index)
                self.unassigned_masters.append(master_id)
                
                self.refresh_assigned_list()
                self.refresh_unassigned_list()
    
    def move_up(self):
        """Move selected item up in priority"""
        selection = self.assigned_listbox.curselection()
        if selection:
            index = selection[0]
            if index > 0:
                # Swap with previous item
                self.assigned_masters[index], self.assigned_masters[index-1] = \
                    self.assigned_masters[index-1], self.assigned_masters[index]
                
                self.refresh_assigned_list()
                self.assigned_listbox.selection_set(index-1)
    
    def move_down(self):
        """Move selected item down in priority"""
        selection = self.assigned_listbox.curselection()
        if selection:
            index = selection[0]
            if index < len(self.assigned_masters) - 1:
                # Swap with next item
                self.assigned_masters[index], self.assigned_masters[index+1] = \
                    self.assigned_masters[index+1], self.assigned_masters[index]
                
                self.refresh_assigned_list()
                self.assigned_listbox.selection_set(index+1)
    
    def reset_priority(self):
        """Reset to default priority order"""
        # Move all to unassigned
        self.unassigned_masters = [f"M{m.m_index}" for m in self.project.masters]
        self.assigned_masters = []
        
        # Then assign in index order
        for master_id in sorted(self.unassigned_masters, key=lambda x: int(x[1:])):
            self.assigned_masters.append(master_id)
        self.unassigned_masters = []
        
        self.refresh_assigned_list()
        self.refresh_unassigned_list()
    
    def apply(self):
        """Apply the priority configuration"""
        # Update slave priority
        self.slave.priority = {
            "type": "fixed",
            "order": self.assigned_masters.copy()
        }
        
        self.result = self.assigned_masters
        self.dialog.destroy()
    
    def cancel(self):
        """Cancel without applying changes"""
        self.result = None
        self.dialog.destroy()
    
    def wait(self):
        """Wait for dialog to close and return result"""
        self.dialog.wait_window()
        return self.result