#!/usr/bin/env python3
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
