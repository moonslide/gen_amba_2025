# Lines Z-Order and Flash Effect Features

## 1. Lines Under Blocks (Z-Order)

### Problem
Lines were appearing on top of blocks, obscuring text and creating unprofessional appearance.

### Solution
Implemented proper z-order layering:
- Lines are drawn first (bottom layer)
- All blocks are raised above lines
- Z-order maintained during all operations

### Implementation
1. **Drawing Order**:
   - `draw_interconnect()` called first
   - `raise_all_blocks()` brings all blocks to top

2. **raise_all_blocks() Method**:
   ```python
   def raise_all_blocks(self):
       # Raises all master and slave blocks above lines
       for master in self.masters:
           self.tag_raise(master['id'])
           # ... raise all components
       for slave in self.slaves:
           self.tag_raise(slave['id'])
           # ... raise all components
   ```

3. **Maintained During**:
   - Adding new blocks
   - Dragging blocks
   - Grid snapping
   - Zoom operations

### Visual Result
- Clean, professional appearance
- Block text always visible
- Lines provide clear connections without interference

## 2. Flash Effect on Click

### Purpose
Provides visual feedback when a block is clicked/selected.

### Flash Sequence
1. **Yellow** (highlight)
2. **Original color** 
3. **White** (bright flash)
4. **Original color** (restored)

Total duration: 400ms

### Implementation
```python
def flash_block(self, block_id, original_color):
    flash_colors = ['#FFFF00', original_color, '#FFFFFF', original_color]
    flash_duration = 100  # milliseconds per color
    
    def flash_step(color_index):
        if color_index < len(flash_colors):
            self.itemconfig(block_id, fill=flash_colors[color_index])
            self.after(flash_duration, lambda: flash_step(color_index + 1))
        else:
            self.itemconfig(block_id, fill=original_color)
```

### Triggered When
- Left-clicking any master block
- Left-clicking any slave block
- Before starting drag operation

### Benefits
1. **User Feedback**: Clear indication of selection
2. **Visual Confirmation**: Shows which block is active
3. **Professional**: Standard UI pattern
4. **Non-intrusive**: Quick flash doesn't interrupt workflow

## Technical Details

### Z-Order Tags
- Lines use tag: `'interconnect'`
- Blocks have individual IDs
- `tag_raise()` moves items to top

### Flash Colors
- Masters flash: Yellow → Green → White → Green
- Slaves flash: Yellow → Blue → White → Blue

### Performance
- Flash uses non-blocking animation
- Z-order operations are efficient
- No impact on drag/zoom performance

## Testing
Run `test_lines_flash.py` to see both features in action.