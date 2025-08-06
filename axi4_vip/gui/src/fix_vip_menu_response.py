#!/usr/bin/env python3
"""
Fix VIP menu commands that don't respond when clicked
"""

import os

def fix_vip_menu_response():
    """Fix VIP menu commands to always provide feedback"""
    
    gui_file = os.path.join(os.path.dirname(__file__), 'bus_matrix_gui.py')
    
    print("🔧 Fixing VIP menu command responses...")
    print("="*50)
    
    # Read the file
    with open(gui_file, 'r') as f:
        content = f.read()
    
    # Fix 1: Add VIP command handlers that provide feedback
    vip_handlers = '''
    def vip_create_environment(self):
        """Handle Create VIP Environment command"""
        if hasattr(self, 'vip_panel') and self.vip_panel:
            try:
                self.vip_panel.create_vip_environment()
            except Exception as e:
                messagebox.showerror("VIP Error", f"Failed to create VIP environment:\\n{str(e)}")
        else:
            messagebox.showwarning("VIP Not Ready", 
                                 "VIP panel is not initialized.\\n\\n"
                                 "This can happen if:\\n"
                                 "1. VIP modules failed to import\\n"
                                 "2. GUI is still loading\\n\\n"
                                 "Try: Tools → Check VIP Status for details")
    
    def vip_reset_environment(self):
        """Handle Reset Environment command"""
        if hasattr(self, 'vip_panel') and self.vip_panel:
            try:
                self.vip_panel.reset_vip_environment()
            except Exception as e:
                messagebox.showerror("VIP Error", f"Failed to reset environment:\\n{str(e)}")
        else:
            messagebox.showwarning("VIP Not Ready", "VIP panel is not initialized")
    
    def vip_export_config(self):
        """Handle Export VIP Config command"""
        if hasattr(self, 'vip_panel') and self.vip_panel:
            try:
                self.vip_panel.export_vip_config()
            except Exception as e:
                messagebox.showerror("VIP Error", f"Failed to export config:\\n{str(e)}")
        else:
            messagebox.showwarning("VIP Not Ready", "VIP panel is not initialized")
    
    def vip_generate_test_suite(self):
        """Handle Generate Test Suite command"""
        if hasattr(self, 'vip_panel') and self.vip_panel:
            try:
                self.vip_panel.generate_test_suite()
            except Exception as e:
                messagebox.showerror("VIP Error", f"Failed to generate test suite:\\n{str(e)}")
        else:
            messagebox.showwarning("VIP Not Ready", "VIP panel is not initialized")
    
    def vip_run_tests(self):
        """Handle Run Tests command"""
        if hasattr(self, 'vip_panel') and self.vip_panel:
            try:
                self.vip_panel.run_tests()
            except Exception as e:
                messagebox.showerror("VIP Error", f"Failed to run tests:\\n{str(e)}")
        else:
            messagebox.showwarning("VIP Not Ready", "VIP panel is not initialized")
    
    def vip_stop_tests(self):
        """Handle Stop Tests command"""
        if hasattr(self, 'vip_panel') and self.vip_panel:
            try:
                self.vip_panel.stop_tests()
            except Exception as e:
                messagebox.showerror("VIP Error", f"Failed to stop tests:\\n{str(e)}")
        else:
            messagebox.showwarning("VIP Not Ready", "VIP panel is not initialized")
    
    def vip_export_results(self):
        """Handle Export Results command"""
        if hasattr(self, 'vip_panel') and self.vip_panel:
            try:
                self.vip_panel.export_results()
            except Exception as e:
                messagebox.showerror("VIP Error", f"Failed to export results:\\n{str(e)}")
        else:
            messagebox.showwarning("VIP Not Ready", "VIP panel is not initialized")
    
    def vip_generate_report(self):
        """Handle Generate Report command"""
        if hasattr(self, 'vip_panel') and self.vip_panel:
            try:
                self.vip_panel.generate_report()
            except Exception as e:
                messagebox.showerror("VIP Error", f"Failed to generate report:\\n{str(e)}")
        else:
            messagebox.showwarning("VIP Not Ready", "VIP panel is not initialized")
'''
    
    # Find where to insert the handlers (after show_vip_about)
    insert_pos = content.find("        messagebox.showinfo(\"About AXI4 VIP\", about_text)")
    if insert_pos > 0:
        # Find the end of the method
        end_pos = content.find("\n    \n    def ", insert_pos)
        if end_pos > 0:
            # Insert the handlers
            content = content[:end_pos] + "\n" + vip_handlers + content[end_pos:]
            print("✓ Added VIP command handlers")
        else:
            # Insert at the end of class
            end_pos = content.rfind("\n\nif __name__")
            if end_pos > 0:
                content = content[:end_pos] + "\n" + vip_handlers + content[end_pos:]
                print("✓ Added VIP command handlers at end of class")
    
    # Fix 2: Update menu commands to use the new handlers
    menu_replacements = [
        ('command=lambda: self.vip_panel.create_vip_environment() if hasattr(self, \'vip_panel\') else None',
         'command=self.vip_create_environment'),
        ('command=lambda: self.vip_panel.reset_vip_environment() if hasattr(self, \'vip_panel\') else None',
         'command=self.vip_reset_environment'),
        ('command=lambda: self.vip_panel.export_vip_config() if hasattr(self, \'vip_panel\') else None',
         'command=self.vip_export_config'),
        ('command=lambda: self.vip_panel.generate_test_suite() if hasattr(self, \'vip_panel\') else None',
         'command=self.vip_generate_test_suite'),
        ('command=lambda: self.vip_panel.run_tests() if hasattr(self, \'vip_panel\') else None',
         'command=self.vip_run_tests'),
        ('command=lambda: self.vip_panel.stop_tests() if hasattr(self, \'vip_panel\') else None',
         'command=self.vip_stop_tests'),
        ('command=lambda: self.vip_panel.export_results() if hasattr(self, \'vip_panel\') else None',
         'command=self.vip_export_results'),
        ('command=lambda: self.vip_panel.generate_report() if hasattr(self, \'vip_panel\') else None',
         'command=self.vip_generate_report'),
    ]
    
    for old, new in menu_replacements:
        if old in content:
            content = content.replace(old, new)
            print(f"✓ Updated menu command: {new.split('=')[1]}")
    
    # Fix 3: Initialize vip_panel to None in __init__
    init_pattern = "        self.current_config = BusMatrixConfig()"
    if init_pattern in content and "self.vip_panel = None" not in content:
        content = content.replace(init_pattern, 
                                 init_pattern + "\n        self.vip_panel = None  # Initialize VIP panel to None")
        print("✓ Added vip_panel initialization in __init__")
    
    # Write back
    with open(gui_file, 'w') as f:
        f.write(content)
    
    print("\n✅ VIP menu commands fixed!")
    print("\nWhat was fixed:")
    print("1. Added proper command handlers with error messages")
    print("2. Menu commands now always provide feedback")
    print("3. Clear error messages when VIP panel is not ready")
    print("4. Helpful suggestions on what to do")
    
    return True

if __name__ == "__main__":
    if fix_vip_menu_response():
        print("\n🎉 VIP menu response fix complete!")
    else:
        print("\n❌ Failed to fix VIP menu response")