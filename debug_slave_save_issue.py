#!/usr/bin/env python3

"""
DEBUG SLAVE SAVE ISSUE
Comprehensive debugging for slave not appearing after Save button click
"""

import os
import sys
import tkinter as tk
from tkinter import messagebox
import traceback

# Add src directory to path
current_dir = os.path.dirname(os.path.abspath(__file__))
src_dir = os.path.join(current_dir, 'axi4_vip', 'gui', 'src')
sys.path.insert(0, src_dir)

# Import with debugging
print(f"DEBUG: Importing from {src_dir}")
try:
    from bus_config import Slave, BusConfig
    print("✅ Successfully imported bus_config")
except Exception as e:
    print(f"❌ Failed to import bus_config: {e}")
    traceback.print_exc()

try:
    from bus_matrix_gui import BusMatrixGUI, SlaveDialog
    print("✅ Successfully imported bus_matrix_gui")
except Exception as e:
    print(f"❌ Failed to import bus_matrix_gui: {e}")
    traceback.print_exc()

def monkey_patch_slave_dialog():
    """Add extensive debugging to SlaveDialog"""
    
    # Save original methods
    original_init = SlaveDialog.__init__
    original_ok_clicked = SlaveDialog.ok_clicked
    
    def debug_init(self, parent, config=None, default_name="Slave0", default_address=0, available_masters=None, main_gui=None):
        print("\n" + "="*60)
        print("🔍 DEBUG: SlaveDialog.__init__ called")
        print(f"  default_name: {default_name}")
        print(f"  default_address: 0x{default_address:08X}")
        print(f"  available_masters: {available_masters}")
        print(f"  main_gui: {main_gui}")
        
        # Call original init
        original_init(self, parent, config, default_name, default_address, available_masters, main_gui)
        
        print("  Dialog created successfully")
        print("="*60 + "\n")
    
    def debug_ok_clicked(self):
        """Debug version of ok_clicked"""
        print("\n" + "="*60)
        print("🔍 DEBUG: SlaveDialog.ok_clicked called")
        
        try:
            # Get all the values
            print(f"  Name: {self.name_var.get()}")
            print(f"  Address: {self.addr_var.get()}")
            print(f"  Size: {self.size_value_var.get()} {self.size_unit_var.get()}")
            print(f"  Type: {self.type_var.get()}")
            print(f"  Priority: {self.priority_var.get()}")
            print(f"  Read Latency: {self.read_lat_var.get()}")
            print(f"  Write Latency: {self.write_lat_var.get()}")
            
            # Parse address
            addr_str = self.addr_var.get()
            if addr_str.startswith("0x") or addr_str.startswith("0X"):
                base_addr = int(addr_str, 16)
            else:
                base_addr = int(addr_str)
            print(f"  Parsed address: 0x{base_addr:08X}")
            
            # Convert size to KB
            size_value = int(self.size_value_var.get())
            size_unit = self.size_unit_var.get()
            
            if size_unit == "GB":
                size_kb = size_value * 1048576
            elif size_unit == "MB":
                size_kb = size_value * 1024
            else:
                size_kb = size_value
            print(f"  Size in KB: {size_kb}")
            
            # Get allowed masters
            allowed_masters = [name for name, var in self.master_vars.items() if var.get()]
            print(f"  Selected masters: {allowed_masters}")
            
            # If all masters are selected, use None (default = all allowed)
            if len(allowed_masters) == len(self.available_masters):
                final_allowed_masters = None  # All allowed (default)
                print("  Using None (all masters allowed)")
            elif len(allowed_masters) == 0:
                final_allowed_masters = None  # None selected = all allowed (default)
                print("  No masters selected - using None (all allowed)")
            else:
                final_allowed_masters = allowed_masters  # Specific restrictions
                print(f"  Specific restrictions: {final_allowed_masters}")
            
            # Try to create Slave object
            print("\n  Creating Slave object...")
            self.result = Slave(
                name=self.name_var.get(),
                base_address=base_addr,
                size=size_kb,
                memory_type=self.type_var.get(),
                read_latency=int(self.read_lat_var.get()),
                write_latency=int(self.write_lat_var.get()),
                priority=int(self.priority_var.get()),
                num_regions=int(self.num_regions_var.get()),
                secure_only=self.secure_only_var.get(),
                privileged_only=self.privileged_only_var.get(),
                allowed_masters=final_allowed_masters
            )
            print("  ✅ Slave object created successfully")
            print(f"  self.result = {self.result}")
            
            # Destroy dialog
            print("  Destroying dialog...")
            self.dialog.destroy()
            print("  ✅ Dialog destroyed")
            
        except Exception as e:
            print(f"  ❌ ERROR in ok_clicked: {e}")
            traceback.print_exc()
            messagebox.showerror("Invalid Input", f"Error: {str(e)}")
        
        print("="*60 + "\n")
    
    # Apply patches
    SlaveDialog.__init__ = debug_init
    SlaveDialog.ok_clicked = debug_ok_clicked

def monkey_patch_gui_add_slave():
    """Add debugging to GUI add_slave method"""
    
    original_method = BusMatrixGUI.add_slave
    
    def debug_add_slave(self):
        print("\n🎯 DEBUG: BusMatrixGUI.add_slave called")
        print(f"  Current slaves before: {len(self.current_config.slaves)}")
        print(f"  Slave names: {[s.name for s in self.current_config.slaves]}")
        
        # Add try-except around entire method
        try:
            # Generate unique name
            existing_names = [s.name for s in self.current_config.slaves]
            slave_num = 0
            while f"Slave{slave_num}" in existing_names:
                slave_num += 1
            default_name = f"Slave{slave_num}"
            print(f"  Generated default name: {default_name}")
            
            # Calculate next available address
            default_address = 0
            if self.current_config.slaves:
                # Find the highest end address
                max_end_addr = 0
                for slave in self.current_config.slaves:
                    end_addr = slave.base_address + (slave.size * 1024)  # Convert KB to bytes
                    if end_addr > max_end_addr:
                        max_end_addr = end_addr
                # Align to next power-of-2 boundary (at least 1MB)
                import math
                if max_end_addr == 0:
                    default_address = 0
                else:
                    # Round up to next power of 2
                    next_pow2 = 2 ** math.ceil(math.log2(max_end_addr + 1))
                    default_address = next_pow2
            print(f"  Calculated default address: 0x{default_address:08X}")
            
            # Get list of available masters
            available_masters = [m.name for m in self.current_config.masters]
            print(f"  Available masters: {available_masters}")
            
            print("\n  Creating SlaveDialog...")
            dialog = SlaveDialog(self.root, default_name=default_name, default_address=default_address,
                               available_masters=available_masters, main_gui=self)
            
            print("  Waiting for dialog to close...")
            self.root.wait_window(dialog.dialog)
            
            print(f"\n  Dialog closed, checking result...")
            print(f"  dialog.result = {dialog.result}")
            
            if dialog.result:
                config = dialog.result
                print(f"  ✅ Got slave config: {config}")
                print(f"     Name: {config.name}")
                print(f"     Address: 0x{config.base_address:08X}")
                print(f"     Size: {config.size}KB")
                
                # Validate address alignment
                is_valid, error_msg = self.validate_address_alignment(config.base_address, config.size)
                print(f"  Address alignment valid: {is_valid}")
                if not is_valid:
                    print(f"  Alignment error: {error_msg}")
                    result = messagebox.askyesno("Address Alignment Warning",
                                               f"{error_msg}\n\nDo you want to continue anyway?")
                    if not result:
                        print("  User cancelled due to alignment warning")
                        return
                
                # Check for address conflicts
                print("  Checking for address conflicts...")
                for slave in self.current_config.slaves:
                    if self.check_address_overlap(config, slave):
                        print(f"  ❌ Conflict with {slave.name}")
                        messagebox.showerror("Address Conflict", 
                                           f"Address range overlaps with {slave.name}")
                        return
                print("  ✅ No address conflicts")
                        
                print("\n  Adding slave to configuration...")
                self.current_config.slaves.append(config)
                print(f"  Total slaves now: {len(self.current_config.slaves)}")
                
                print("  Adding to listbox...")
                self.slave_listbox.insert(tk.END, 
                                        f"{config.name} (0x{config.base_address:08X})")
                print(f"  Listbox now has {self.slave_listbox.size()} items")
                
                print("\n  Adding slave to canvas...")
                # Add to canvas - Slaves on bottom in rows
                zoom = self.canvas.zoom_level
                col = len(self.canvas.slaves) % 4
                row = len(self.canvas.slaves) // 4
                x_pos = (50 + col * 200) * zoom
                y_pos = (400 + row * 120) * zoom
                
                print(f"  Canvas position: x={int(x_pos)}, y={int(y_pos)}, zoom={zoom}")
                print(f"  Canvas slaves before: {len(self.canvas.slaves)}")
                
                self.canvas.add_slave(config, x=int(x_pos), y=int(y_pos))
                print(f"  Canvas slaves after: {len(self.canvas.slaves)}")
                
                self.canvas.draw_interconnect()
                self.canvas.raise_all_blocks()
                self.update_canvas_scroll_region()
                
                # Auto-scroll to show the newly added slave
                self.canvas.update_idletasks()
                if len(self.canvas.slaves) == 1:
                    # First slave - scroll to show slave area
                    self.canvas.yview_moveto(0.4)
                    print("  Scrolled to show first slave")
                else:
                    # Ensure the new slave is visible
                    bbox = self.canvas.bbox("all")
                    if bbox:
                        self.canvas.config(scrollregion=bbox)
                        print(f"  Updated scroll region to: {bbox}")
                
                print("  ✅ Slave added successfully to canvas")
                self.update_status(f"Added slave: {config.name}")
                
            else:
                print("  ❌ Dialog cancelled - no result")
                self.update_status("Slave creation cancelled")
                
        except Exception as e:
            error_msg = f"Failed to add slave: {str(e)}"
            print(f"  ❌ EXCEPTION: {error_msg}")
            traceback.print_exc()
            messagebox.showerror("Error", error_msg)
    
    BusMatrixGUI.add_slave = debug_add_slave

def run_debug_gui():
    """Run GUI with debugging patches"""
    
    print("🚀 Starting GUI with slave save debugging")
    print("="*60)
    
    # Apply monkey patches
    monkey_patch_slave_dialog()
    monkey_patch_gui_add_slave()
    
    # Create and run GUI
    root = tk.Tk()
    gui = BusMatrixGUI(root)
    
    # Add a debug menu
    debug_menu = tk.Menu(gui.menubar, tearoff=0)
    debug_menu.add_command(label="Check Slave List", 
                          command=lambda: print(f"\nSlave list: {[s.name for s in gui.current_config.slaves]}"))
    debug_menu.add_command(label="Check Canvas Slaves", 
                          command=lambda: print(f"\nCanvas slaves: {len(gui.canvas.slaves)}"))
    debug_menu.add_command(label="Check Listbox Items",
                          command=lambda: print(f"\nListbox items: {gui.slave_listbox.size()}"))
    gui.menubar.add_cascade(label="Debug", menu=debug_menu)
    
    print("\n📋 Debug Instructions:")
    print("1. Click 'Add Slave' button")
    print("2. Configure the slave and click 'Save' (OK)")
    print("3. Watch console for detailed debug output")
    print("4. Use Debug menu to check state")
    
    root.mainloop()

if __name__ == "__main__":
    run_debug_gui()