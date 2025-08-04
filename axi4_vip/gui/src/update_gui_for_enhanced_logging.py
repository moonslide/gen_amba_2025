#!/usr/bin/env python3
"""
Update script to integrate enhanced VIP generator into existing GUI
"""

import os
import shutil
from datetime import datetime

def update_bus_matrix_gui():
    """Update the bus_matrix_gui.py to use enhanced VIP generator"""
    
    gui_files = [
        'bus_matrix_gui.py',
        'bus_matrix_gui_modern.py',
        'vip_gui_integration.py',
        'vip_gui_integration_modern.py'
    ]
    
    for gui_file in gui_files:
        if os.path.exists(gui_file):
            print(f"Updating {gui_file}...")
            
            # Read the file
            with open(gui_file, 'r') as f:
                content = f.read()
            
            # Backup the original
            backup_file = f"{gui_file}.backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
            shutil.copy(gui_file, backup_file)
            print(f"  Created backup: {backup_file}")
            
            # Replace imports
            if 'from vip_environment_generator import VIPEnvironmentGenerator' in content:
                content = content.replace(
                    'from vip_environment_generator import VIPEnvironmentGenerator',
                    'from vip_environment_generator import VIPEnvironmentGenerator\nfrom vip_environment_generator_enhanced import VIPEnvironmentGeneratorEnhanced'
                )
                
            # Replace generator instantiation
            if 'vip_gen = VIPEnvironmentGenerator(' in content:
                content = content.replace(
                    'vip_gen = VIPEnvironmentGenerator(',
                    'vip_gen = VIPEnvironmentGeneratorEnhanced('
                )
            
            # Add enhanced logging option to GUI
            if 'self.vip_options_frame = ttk.LabelFrame' in content:
                # Find the VIP options frame section and add checkbox
                insert_pos = content.find('# VIP Generation Mode')
                if insert_pos > 0:
                    insert_text = '''
        # Enhanced Logging Option
        self.enable_enhanced_logging = tk.BooleanVar(value=True)
        ttk.Checkbutton(self.vip_options_frame, 
                       text="Enable Enhanced Logging (BFM debug, UVM_INFO)",
                       variable=self.enable_enhanced_logging).grid(
            row=10, column=0, columnspan=3, sticky='w', padx=5, pady=2)
        '''
                    content = content[:insert_pos] + insert_text + content[insert_pos:]
            
            # Update generate_vip method to use enhanced generator
            if 'def generate_vip(self):' in content:
                # Find the method and update it
                method_start = content.find('def generate_vip(self):')
                if method_start > 0:
                    # Look for VIPEnvironmentGenerator instantiation
                    gen_start = content.find('vip_gen = VIPEnvironmentGenerator(', method_start)
                    if gen_start > 0:
                        content = content.replace(
                            'vip_gen = VIPEnvironmentGenerator(',
                            'vip_gen = VIPEnvironmentGeneratorEnhanced(' if hasattr(self, 'enable_enhanced_logging') and self.enable_enhanced_logging.get() else 'vip_gen = VIPEnvironmentGenerator('
                        )
            
            # Write the updated file
            with open(gui_file, 'w') as f:
                f.write(content)
            
            print(f"  Updated {gui_file} successfully")
            
def create_enhanced_gui_launcher():
    """Create a launcher script for the enhanced GUI"""
    
    launcher_content = '''#!/usr/bin/env python3
"""
AMBA Bus Matrix Configuration Tool - Enhanced GUI with Comprehensive Logging
This version includes enhanced VIP generation with BFM integration and debugging features
"""

import sys
import os

# Add the source directory to Python path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

# Import the enhanced generator
from vip_environment_generator_enhanced import VIPEnvironmentGeneratorEnhanced

# Import and patch the GUI
def patch_gui_for_enhanced_mode():
    """Monkey patch the GUI to use enhanced generator"""
    import bus_matrix_gui
    
    # Save original generator class
    original_generator = getattr(bus_matrix_gui, 'VIPEnvironmentGenerator', None)
    
    # Replace with enhanced version
    bus_matrix_gui.VIPEnvironmentGenerator = VIPEnvironmentGeneratorEnhanced
    
    # Also patch any module-level imports
    if hasattr(bus_matrix_gui, 'vip_environment_generator'):
        bus_matrix_gui.vip_environment_generator.VIPEnvironmentGenerator = VIPEnvironmentGeneratorEnhanced

# Apply the patch
patch_gui_for_enhanced_mode()

# Now import and run the GUI
from bus_matrix_gui import main

if __name__ == "__main__":
    print("Starting AMBA Bus Matrix Configuration Tool - Enhanced Edition")
    print("Features:")
    print("- Comprehensive BFM integration with logging")
    print("- Enhanced UVM_INFO messages throughout VIP")
    print("- Interface signal monitoring and debugging")
    print("- Protocol assertion checking")
    print("- Timeout detection on all handshakes")
    print("")
    main()
'''
    
    with open('bus_matrix_gui_enhanced.py', 'w') as f:
        f.write(launcher_content)
    
    # Make it executable
    os.chmod('bus_matrix_gui_enhanced.py', 0o755)
    
    print("Created enhanced GUI launcher: bus_matrix_gui_enhanced.py")

def create_simple_patch():
    """Create a simple patch that can be applied to any GUI version"""
    
    patch_content = '''#!/usr/bin/env python3
"""
Simple patch to enable enhanced VIP generation in existing GUI
"""

def apply_enhanced_vip_patch():
    """Apply patch to use enhanced VIP generator"""
    
    # Import both generators
    try:
        from vip_environment_generator import VIPEnvironmentGenerator
        from vip_environment_generator_enhanced import VIPEnvironmentGeneratorEnhanced
    except ImportError as e:
        print(f"Error importing generators: {e}")
        return False
    
    # Monkey patch all GUI modules
    import sys
    
    # List of modules that might use VIPEnvironmentGenerator
    gui_modules = [
        'bus_matrix_gui',
        'bus_matrix_gui_modern', 
        'vip_gui_integration',
        'vip_gui_integration_modern'
    ]
    
    patched_count = 0
    
    for module_name in gui_modules:
        if module_name in sys.modules:
            module = sys.modules[module_name]
            if hasattr(module, 'VIPEnvironmentGenerator'):
                # Replace the class
                module.VIPEnvironmentGenerator = VIPEnvironmentGeneratorEnhanced
                patched_count += 1
                print(f"Patched {module_name}")
            
            # Also check for any instances
            for attr_name in dir(module):
                attr = getattr(module, attr_name)
                if isinstance(attr, type) and issubclass(attr, VIPEnvironmentGenerator):
                    setattr(module, attr_name, VIPEnvironmentGeneratorEnhanced)
                    patched_count += 1
                    print(f"Patched {module_name}.{attr_name}")
    
    # Global replacement
    import builtins
    if hasattr(builtins, 'VIPEnvironmentGenerator'):
        builtins.VIPEnvironmentGenerator = VIPEnvironmentGeneratorEnhanced
        patched_count += 1
        print("Patched global VIPEnvironmentGenerator")
    
    print(f"Enhanced VIP patch applied successfully ({patched_count} replacements)")
    return True

# Auto-apply when imported
if __name__ != "__main__":
    apply_enhanced_vip_patch()
'''
    
    with open('enhanced_vip_patch.py', 'w') as f:
        f.write(patch_content)
    
    print("Created enhanced VIP patch: enhanced_vip_patch.py")

def create_readme():
    """Create README for enhanced logging features"""
    
    readme_content = '''# Enhanced VIP Generation with Comprehensive Logging

This enhanced version of the VIP generator includes comprehensive debugging features to help trace VIP activity in waveforms and logs.

## Features Added

### 1. BFM Integration
- Full Bus Functional Model implementation
- Task-based transaction APIs
- Timeout detection on all handshakes
- Protocol-compliant signal generation

### 2. Enhanced Logging
- Transaction-level UVM_INFO messages
- Driver transaction counters
- Monitor channel activity tracking
- BFM operation timestamps
- Interface signal debugging

### 3. Protocol Checking
- Valid signal stability assertions
- Ready signal monitoring
- 4KB boundary crossing detection
- Response timeout detection

### 4. Debug Visibility
- Configurable verbosity levels
- Timestamp correlation with waveforms
- Ready/valid handshake tracking
- Transaction completion status

## Usage

### Method 1: Enhanced GUI Launcher
```bash
python3 bus_matrix_gui_enhanced.py
```

### Method 2: Patch Existing GUI
```python
import enhanced_vip_patch  # This auto-applies the patch
from bus_matrix_gui import main
main()
```

### Method 3: Direct Import
```python
from vip_environment_generator_enhanced import VIPEnvironmentGeneratorEnhanced

# Use instead of VIPEnvironmentGenerator
vip_gen = VIPEnvironmentGeneratorEnhanced(config, mode)
vip_gen.generate_environment_enhanced(output_path)
```

## Debugging with Enhanced VIP

### Console Output
Look for these log patterns:
- `[BFM]` - BFM operation messages
- `[MONITOR]` - Monitor observations
- `[axi4_master_driver]` - Driver transactions
- `[BFM_CONNECTOR]` - Signal connections

### Waveform Signals
Key signals to observe:
- `master_bfm[n].master_driver_bfm_h.*` - BFM driver signals
- `master_bfm[n].master_monitor_bfm_h.*` - BFM monitor signals
- `axi_if[n].*` - AXI interface signals
- `bfm_connector.* ` - Connection debugging

### Common Issues
1. **No ready signal**: Check "Waiting for AWREADY" messages
2. **Timeout**: Look for "ERROR - timeout" in BFM messages
3. **Protocol violation**: Check assertion failures
4. **Missing handshake**: Verify ready/valid in logs

## Configuration

Set these options in generated tests:
- `+UVM_VERBOSITY=UVM_HIGH` - Maximum debug visibility
- `+fsdb_file=debug.fsdb` - Waveform output file
- `+UVM_TESTNAME=debug_bfm_test` - Run debug test

## Integration

The enhanced generator is backward compatible and can be used as a drop-in replacement for the standard VIPEnvironmentGenerator.
'''
    
    with open('ENHANCED_VIP_README.md', 'w') as f:
        f.write(readme_content)
    
    print("Created documentation: ENHANCED_VIP_README.md")

def main():
    """Main update function"""
    print("Updating GUI for Enhanced VIP Generation")
    print("=" * 50)
    
    # Check if enhanced generator exists
    if not os.path.exists('vip_environment_generator_enhanced.py'):
        print("ERROR: vip_environment_generator_enhanced.py not found!")
        print("Please ensure the enhanced generator is in the current directory")
        return
    
    # Create the enhanced launcher
    create_enhanced_gui_launcher()
    
    # Create the patch
    create_simple_patch()
    
    # Create documentation
    create_readme()
    
    # Optionally update existing GUI files
    response = input("\nDo you want to update existing GUI files? (y/n): ")
    if response.lower() == 'y':
        update_bus_matrix_gui()
    
    print("\nEnhanced VIP integration complete!")
    print("\nTo use the enhanced GUI:")
    print("  python3 bus_matrix_gui_enhanced.py")
    print("\nOr import the patch in your existing code:")
    print("  import enhanced_vip_patch")

if __name__ == "__main__":
    main()