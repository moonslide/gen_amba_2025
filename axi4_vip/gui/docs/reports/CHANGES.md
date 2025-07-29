# Bus Matrix GUI Improvements

## Summary of Changes

### 1. Fixed Priority Label Display
- **Issue**: Priority labels were always showing "P:0" regardless of actual priority value
- **Fix**: Changed line 192 to use `getattr(master['config'], 'priority', 0)` instead of direct attribute access
- **Result**: Priority labels now correctly display the configured priority value for each master

### 2. Added Proper Spacing for Many Components
- **Issue**: Components would overlap when many masters/slaves were added
- **Changes**:
  - Added scrollbars to the canvas (vertical and horizontal)
  - Changed layout from 2 columns to 3 columns for both masters and slaves
  - Increased spacing between components (140px horizontal, 120px/140px vertical)
  - Added `update_canvas_scroll_region()` method to dynamically adjust scroll area
  - Canvas now has a larger virtual size (1400x1200) to accommodate more components
- **Result**: Can now add many masters/slaves without overlap, with scrolling when needed

### 3. Added CSV Export Features
- **New Menu Items**:
  - "Export Memory Map CSV..." - Exports slave memory map information
  - "Export Master/Slave Table CSV..." - Exports complete configuration
- **Memory Map CSV includes**:
  - Slave Name, Base Address, End Address, Size, Type
  - Priority, Read/Write Latency, Security settings, Number of regions
- **Master/Slave Table CSV includes**:
  - Bus configuration (type, widths, arbitration)
  - Master details (ID width, priority, QoS support, etc.)
  - Slave details (address, size, type, latency, etc.)
- **Result**: Easy export of configuration data for documentation or analysis

### 4. Added Address Alignment Validation
- **New validation method**: `validate_address_alignment()`
  - Checks that slave size is power of 2
  - Checks that base address is aligned to size boundary
- **Integration**:
  - Validation runs when adding/editing slaves
  - Warning dialog shows suggested values if alignment is incorrect
  - User can choose to continue anyway or fix the values
  - Validation also runs before Verilog generation (blocks if invalid)
- **UI improvements**:
  - SlaveDialog now shows real-time alignment status
  - Help text explains alignment requirements
  - Visual indicators (✓ or ⚠️) show alignment status
- **Result**: Ensures proper address alignment for hardware implementation

## Testing

A test script `test_bus_matrix_gui.py` has been created to verify:
1. Priority labels display correctly
2. Address validation logic works properly
3. Layout handles many components without overlap

## Usage Examples

### CSV Export
1. Configure your bus matrix with masters and slaves
2. Go to File menu → "Export Memory Map CSV..." or "Export Master/Slave Table CSV..."
3. Choose location and filename
4. CSV file will be created with all configuration details

### Address Alignment
- When adding a slave, use power-of-2 sizes (1KB, 2KB, 4KB, 8KB, 16KB, etc.)
- Base addresses must be aligned to size boundary
  - Example: 1MB slave must start at 0x00100000, 0x00200000, etc.
  - Example: 64KB slave must start at 0x00010000, 0x00020000, etc.
- The dialog shows real-time validation status
- If alignment is wrong, a warning suggests the correct values

### Many Components
- The canvas now supports up to 3 columns for masters and slaves
- Scrollbars appear automatically when content exceeds visible area
- No manual positioning needed - components are automatically laid out

## Technical Details

### Files Modified
- `/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/bus_matrix_gui.py`

### Key Changes
1. Added `import csv` for CSV export functionality
2. Modified canvas creation to include scrollbars and scroll region
3. Changed layout algorithm from 2 to 3 columns
4. Added methods: `export_memory_map_csv()`, `export_master_slave_csv()`, `validate_address_alignment()`, `update_canvas_scroll_region()`
5. Enhanced SlaveDialog with alignment validation display
6. Fixed priority label access in `draw_interconnect()` method