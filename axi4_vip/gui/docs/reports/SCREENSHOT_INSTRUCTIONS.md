# Real GUI Screenshot Instructions

## Issue Identified
The current PDF documentation contains **mockup drawings** created with matplotlib, not actual screenshots from the running GUI application.

## Required Actions

### 1. Launch Actual GUI Application
```bash
# Navigate to GUI directory
cd /home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui

# Try to launch the actual GUI
./launch_gui.sh
# OR
python3 src/bus_matrix_gui.py
```

### 2. Capture Real Screenshots
Once the GUI is running, capture screenshots of:

#### Step 1: Main Window
- **File needed**: `real_gui_main_window.png`
- **What to capture**: Full main window showing toolbar, canvas, properties panel
- **Action**: Take screenshot immediately after GUI launches

#### Step 2: Add Master Dialog
- **File needed**: `real_gui_add_master.png`
- **What to capture**: Add Master dialog box with configuration fields
- **Action**: Click "Add Master" button, then screenshot the dialog

#### Step 3: Design Canvas with Components
- **File needed**: `real_gui_design_canvas.png`
- **What to capture**: Canvas showing actual masters and slaves with connections
- **Action**: After adding 2 masters and 3 slaves, screenshot the design

#### Step 4: RTL Generation Dialog
- **File needed**: `real_gui_rtl_generation.png`
- **What to capture**: RTL generation dialog with actual file list
- **Action**: Click "Generate RTL", screenshot the generation dialog

#### Step 5: File Output Browser
- **File needed**: `real_gui_file_output.png`
- **What to capture**: File browser showing generated RTL files
- **Action**: Open output directory in file manager, screenshot

#### Step 6: VIP Generation Process
- **File needed**: `real_gui_vip_generation.png`
- **What to capture**: VIP generation dialog or output
- **Action**: Click "Generate VIP", screenshot the process

### 3. Screenshot Guidelines
- **Resolution**: At least 1024x768 for clarity
- **Format**: PNG with transparency if possible
- **Content**: Full dialogs/windows, not cropped
- **Quality**: High DPI for PDF embedding

### 4. Alternative if GUI Not Available
If the actual GUI application is not functional:

1. Create a note in the PDF stating "GUI mockups shown for demonstration"
2. Provide clear indication that these are not real screenshots
3. Update documentation to request real screenshots from users
4. Create placeholder text indicating where real screenshots should go

## Current Status
- ❌ Current images are matplotlib-generated mockups
- ❌ PDFs present mockups as real screenshots  
- ✅ Need actual running GUI application screenshots
- ✅ This instruction file created to guide real screenshot capture