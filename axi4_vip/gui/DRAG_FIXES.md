# Drag Functionality Fixes

## Issues Fixed

### 1. Labels Not Moving During Drag
**Problem**: When dragging blocks, the M:x P:x labels (master index and priority) and S:x labels (slave index) were not moving with the blocks.

**Root Cause**: These labels were being created in the `draw_interconnect()` method instead of being part of the block itself.

**Solution**: 
- Added labels as permanent components of master/slave blocks
- Master blocks now include:
  - `idx_id`: M0, M1, etc. label
  - `priority_id`: P:0, P:1, etc. label
- Slave blocks now include:
  - `idx_id`: S0, S1, etc. label  
  - `priority_id`: P:0 label
- All drag operations now move these labels with the blocks

### 2. Lines Overlapping Blocks
**Problem**: The simplified routing was causing lines to pass through/overlap other blocks.

**Root Cause**: The simplified routing removed collision detection to make lines clearer, but this caused overlap issues.

**Solution**:
- Re-implemented collision detection using `path_intersects_blocks()`
- Added smart routing that:
  1. Tries direct path first
  2. If blocked, uses L-shaped routing with clearance
  3. If still blocked, finds clear horizontal path
- Maintains color coding and smooth curves
- Avoids all blocks with 5px safety margin

## Implementation Details

### Master Block Structure
```python
{
    'id': rectangle_id,
    'text_id': name_text_id,
    'priority_id': priority_label_id,  # NEW
    'idx_id': index_label_id,          # NEW
    'config': config,
    'x': x,
    'y': y
}
```

### Slave Block Structure  
```python
{
    'id': rectangle_id,
    'text_id': name_text_id,
    'addr_id': address_text_id,
    'size_id': size_text_id,
    'idx_id': index_label_id,          # NEW
    'priority_id': priority_label_id,  # NEW
    'config': config,
    'x': x,
    'y': y
}
```

### Updated Methods
1. `add_master()` - Creates all labels as part of block
2. `add_slave()` - Creates all labels as part of block (100px height)
3. `on_click()` - Handles all component IDs for dragging
4. `on_drag()` - Moves all components together
5. `snap_blocks_to_grid()` - Snaps all components
6. `draw_interconnect()` - Removed label creation, added collision avoidance

## Visual Improvements
- Master blocks show M0, M1... in top-left corner
- Priority shown below name as P:0, P:1...
- Slave blocks show S0, S1... in top-left corner
- All labels use appropriate colors (darkgreen for masters, darkblue for slaves)
- Lines intelligently route around obstacles
- Professional appearance maintained

## Testing
Run `test_drag_fixes.py` to verify:
- All labels move with blocks during drag
- Lines avoid overlapping blocks
- Grid snapping works for all components
- Professional appearance is maintained