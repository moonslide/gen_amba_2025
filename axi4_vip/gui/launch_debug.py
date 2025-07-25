#!/usr/bin/env python3
"""Debug launcher for GUI"""

import sys
import os

print("Debug: Starting GUI launch process...")

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

print("Debug: Importing modules...")
try:
    from bus_matrix_gui import BusMatrixGUI
    print("Debug: BusMatrixGUI imported successfully")
    
    print("Debug: Creating GUI instance...")
    gui = BusMatrixGUI()
    print("Debug: GUI instance created")
    
    print("Debug: Starting mainloop...")
    gui.root.mainloop()
    print("Debug: Mainloop exited normally")
    
except Exception as e:
    print(f"Debug: Error occurred: {e}")
    import traceback
    traceback.print_exc()