#!/bin/bash

echo "Launching AMBA Bus Matrix Configuration GUI (Minimal Mode)..."
echo "Python version: $(python3 --version | cut -d' ' -f2)"

cd "$(dirname "$0")"

# Run the GUI with minimal VIP integration
python3 -c "
import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), 'src'))

# Import with error handling
try:
    from bus_matrix_gui import BusMatrixGUI
    import tkinter as tk
    
    # Create and run GUI
    root = tk.Tk()
    app = BusMatrixGUI(root)
    
    print('✅ GUI loaded successfully')
    print('Note: VIP features available through Settings menu')
    
    root.mainloop()
    
except ImportError as e:
    print(f'❌ Import error: {e}')
    print('Trying fallback mode...')
    
    # Fallback without VIP
    try:
        import tkinter as tk
        root = tk.Tk()
        root.title('AMBA Bus Matrix Configuration Tool')
        root.geometry('800x600')
        
        label = tk.Label(root, text='AMBA Bus Matrix GUI\\nVIP integration loading...', 
                        font=('Arial', 16), pady=50)
        label.pack()
        
        root.mainloop()
    except Exception as fallback_error:
        print(f'❌ Complete fallback failed: {fallback_error}')

except Exception as e:
    print(f'❌ GUI error: {e}')
    import traceback
    traceback.print_exc()
"