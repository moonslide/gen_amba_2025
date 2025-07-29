# Right-Click Configuration and Zoom Features

## 1. Right-Click Configuration

### Problem Fixed
Right-clicking on blocks was not showing the configuration dialog.

### Solution
- Fixed the canvas-to-GUI reference connection
- Added `self.canvas.gui = self` when creating canvas
- Simplified callback methods to use direct reference

### How to Use
1. **Right-click any master block** → Context menu appears
   - "Configure Master_X" - Opens configuration dialog
   - "Delete Master" - Removes the block
   
2. **Right-click any slave block** → Context menu appears
   - "Configure Slave_X" - Opens configuration dialog
   - "Delete Slave" - Removes the block

### Features
- Edit all properties (name, priority, addresses, etc.)
- Changes apply immediately
- Visual updates after configuration

## 2. Zoom In/Out Functionality

### UI Controls
Located at the top of the visualization panel:
- **➖ button**: Zoom out (decreases by 25%)
- **Zoom %**: Shows current zoom level
- **➕ button**: Zoom in (increases by 25%)
- **Reset button**: Returns to 100% zoom

### Keyboard Shortcuts
- `Ctrl + (+)` or `Ctrl + (=)`: Zoom in
- `Ctrl + (-)`: Zoom out
- `Ctrl + 0`: Reset to 100%
- Numpad `+` and `-` also work with Ctrl

### Zoom Behavior
- **Range**: 25% to 400%
- **Step**: 25% increments
- **Scaling**: Blocks, text, and spacing all scale
- **Font sizes**: Minimum 6pt to maintain readability
- **Scroll region**: Updates automatically

### Technical Details
1. **Block Scaling**
   - Master blocks: 100×60 pixels (at 100%)
   - Slave blocks: 150×100 pixels (at 100%)
   - All dimensions multiply by zoom level

2. **Text Scaling**
   - Font sizes scale with zoom
   - Minimum font size enforced for readability
   - Labels maintain relative positions

3. **Line Routing**
   - Collision detection accounts for zoom
   - Routes recalculate at new scale
   - Maintains clean appearance

### Implementation
```python
# Zoom levels
zoom_level = 1.0    # Current zoom (1.0 = 100%)
zoom_min = 0.25     # Minimum 25%
zoom_max = 4.0      # Maximum 400%
zoom_step = 0.25    # 25% increments
```

## Benefits
1. **Configuration**: Easy access to block properties without navigating menus
2. **Zoom**: Better visibility for large designs or detailed inspection
3. **Professional**: Standard UI patterns users expect
4. **Accessibility**: Keyboard shortcuts for power users
5. **Flexibility**: Work at any scale from 25% to 400%

## Testing
Run `test_rightclick_zoom.py` for interactive testing of both features.