#!/bin/bash
#==============================================================================
# Script to Help Capture Real GUI Screenshots
# This script attempts to launch the actual GUI and provides instructions
#==============================================================================

echo "============================================="
echo "🎯 REAL GUI SCREENSHOT CAPTURE HELPER"
echo "============================================="
echo ""

# Check if we're in the right directory
if [ ! -f "src/bus_matrix_gui.py" ]; then
    echo "❌ Error: Must run from the GUI directory containing src/bus_matrix_gui.py"
    echo "   Navigate to: /home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/"
    exit 1
fi

echo "📍 Current directory: $(pwd)"
echo "✅ Found GUI application: src/bus_matrix_gui.py"
echo ""

# Check display environment
if [ -z "$DISPLAY" ]; then
    echo "⚠️  WARNING: DISPLAY environment variable not set"
    echo "   This suggests no GUI environment is available"
    echo "   You may need to:"
    echo "   - Run from a desktop environment (not SSH without X11)"
    echo "   - Use X11 forwarding: ssh -X username@hostname"
    echo "   - Use VNC or remote desktop"
    echo ""
else
    echo "✅ DISPLAY environment: $DISPLAY"
fi

# Check Python and tkinter
echo "🐍 Checking Python environment..."
if ! command -v python3 &> /dev/null; then
    echo "❌ Python 3 not found"
    exit 1
fi

PYTHON_VERSION=$(python3 -c 'import sys; print(".".join(map(str, sys.version_info[:2])))')
echo "✅ Python version: $PYTHON_VERSION"

if ! python3 -c "import tkinter" 2>/dev/null; then
    echo "❌ tkinter not available"
    echo "   Install with: sudo yum install python3-tkinter"
    exit 1
fi
echo "✅ tkinter available"

echo ""
echo "🚀 ATTEMPTING TO LAUNCH GUI..."
echo "============================================="

# Try to launch the GUI
echo "Running: ./launch_gui.sh"
echo ""

if [ ! -x "launch_gui.sh" ]; then
    chmod +x launch_gui.sh
fi

# Launch GUI in background so we can provide instructions
./launch_gui.sh &
GUI_PID=$!

echo ""
echo "📸 SCREENSHOT CAPTURE INSTRUCTIONS:"
echo "============================================="
echo ""
echo "If the GUI launched successfully, follow these steps:"
echo ""
echo "1️⃣  MAIN WINDOW SCREENSHOT:"
echo "   - Wait for GUI to fully load"
echo "   - Take screenshot of entire window"
echo "   - Save as: real_gui_main_window.png"
echo ""
echo "2️⃣  ADD MASTER DIALOG:"
echo "   - Click 'Add Master' button in toolbar"
echo "   - Screenshot the configuration dialog"
echo "   - Save as: real_gui_add_master.png"
echo ""
echo "3️⃣  DESIGN CANVAS WITH COMPONENTS:"
echo "   - Add 2 masters (CPU_0, DMA_0)"
echo "   - Add 3 slaves (DDR_Memory, SRAM_Cache, Peripherals)"
echo "   - Screenshot the canvas with components"
echo "   - Save as: real_gui_design_canvas.png"
echo ""
echo "4️⃣  RTL GENERATION DIALOG:"
echo "   - Click 'Generate RTL' button"
echo "   - Screenshot the generation dialog"
echo "   - Save as: real_gui_rtl_generation.png"
echo ""
echo "5️⃣  FILE OUTPUT BROWSER:"
echo "   - Open file manager to output directory"
echo "   - Screenshot showing generated files"
echo "   - Save as: real_gui_file_output.png"
echo ""
echo "6️⃣  VIP GENERATION:"
echo "   - Click 'Generate VIP' button"
echo "   - Screenshot the VIP process"
echo "   - Save as: real_gui_vip_generation.png"
echo ""
echo "💾 SAVE LOCATION:"
echo "   Save all screenshots in: $(pwd)/"
echo ""
echo "🔄 AFTER CAPTURING:"
echo "   Run: python3 update_pdfs_with_real_screenshots.py"
echo ""

# Wait a moment for GUI to potentially load
sleep 3

# Check if GUI process is still running
if kill -0 $GUI_PID 2>/dev/null; then
    echo "✅ GUI appears to be running (PID: $GUI_PID)"
    echo "   Capture screenshots now!"
    echo ""
    echo "   Press Ctrl+C to stop this script after capturing screenshots"
    echo ""
    
    # Wait for user to finish
    wait $GUI_PID
    echo ""
    echo "🏁 GUI closed. Check if screenshots were captured."
else
    echo ""
    echo "❌ GUI may have failed to launch or closed immediately"
    echo ""
    echo "📋 TROUBLESHOOTING:"
    echo "   - Check if you're in a GUI environment (not headless server)"
    echo "   - Verify X11 forwarding if using SSH"
    echo "   - Check error messages above"
    echo "   - Try running manually: python3 src/bus_matrix_gui.py"
fi

echo ""
echo "📝 NEXT STEPS:"
echo "============================================="
echo "1. If screenshots captured successfully:"
echo "   - Replace mockup images with real screenshots"
echo "   - Regenerate PDFs with updated images"
echo ""
echo "2. If GUI didn't launch:"
echo "   - Document the limitation in PDFs"
echo "   - Keep honest disclaimers about mockup nature"
echo "   - Provide instructions for future screenshot capture"
echo ""
echo "3. Update documentation generators to use real images when available"
echo ""

exit 0