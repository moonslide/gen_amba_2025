# Drag and Drop Implementation

## Overview
Full drag-and-drop functionality has been implemented for master and slave blocks with automatic line reconnection.

## Features

### 1. Interactive Drag
- Click and hold any master or slave block
- Drag to new position
- Release to drop

### 2. Automatic Line Reconnection
- Lines update in real-time during drag
- Smooth visual feedback
- Maintains color-coded connections

### 3. Grid Snapping
- **Default**: Enabled with 20px grid
- Ensures clean, aligned layouts
- Professional appearance

### 4. Settings Menu
- **Grid Snapping**: Toggle on/off
- **Grid Size**: Choose from 10, 20, 25, 40, 50px

## Implementation Details

### Mouse Events
```python
self.bind('<Button-1>', self.on_click)      # Start drag
self.bind('<B1-Motion>', self.on_drag)      # During drag
self.bind('<ButtonRelease-1>', self.on_release)  # End drag
```

### Drag State Tracking
```python
self.dragging = False
self.drag_data = {"x": 0, "y": 0, "item": None}
```

### Real-time Updates
- Delta-based movement calculation
- Continuous interconnect redraw
- Efficient position updates

### Grid Snapping Algorithm
```python
new_x = round(block['x'] / grid_size) * grid_size
new_y = round(block['y'] / grid_size) * grid_size
```

## User Guide

### Basic Usage
1. **Move a Block**: Click and drag any master/slave block
2. **Drop**: Release mouse button at desired location
3. **Auto-snap**: Block snaps to nearest grid point

### Settings
1. **Toggle Grid**: Settings → Grid Snapping
2. **Change Grid Size**: Settings → Grid Size → Select size

### Tips
- Drag blocks to organize by function
- Use grid snapping for clean layouts
- Disable grid for free positioning
- Lines automatically avoid overlaps

## Technical Benefits
1. **User-friendly**: Intuitive drag-and-drop interface
2. **Professional**: Grid-aligned layouts
3. **Flexible**: Customizable grid settings
4. **Responsive**: Real-time visual feedback
5. **Maintainable**: Clean implementation

## Visual Quality
- Dragged blocks move to front layer
- Smooth line updates during drag
- Color-coded connections maintained
- Professional grid-aligned results