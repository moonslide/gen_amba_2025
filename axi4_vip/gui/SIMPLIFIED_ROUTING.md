# Simplified Routing Implementation

## Overview
The line routing has been completely simplified to provide clear, independent connections that are easy to understand and follow visually.

## Key Changes

### 1. Removed Complex Routing Strategies
- **Before**: 3-strategy routing with collision detection, unique Y-levels, and safe routing
- **After**: Simple direct or L-shaped routing only

### 2. Color-Coded Connections
- Each master-slave pair uses the same color
- 8 distinct colors for visual differentiation
- Colors: Blue, Indigo, Purple, Deep Purple, Pink, Red, Orange, Amber

### 3. Simplified Routing Algorithm
```python
if abs(start_x - conn_x) < 30:  # Nearly vertical
    # Direct connection
    draw_direct_line()
else:
    # Simple L-shaped routing with smooth curves
    mid_y = start_y + (end_y - start_y) * 0.4  # or 0.6 for slaves
    draw_smooth_l_shape()
```

### 4. Visual Improvements
- **Line Width**: Increased to 3px for better visibility
- **Spacing**: Wider connection point spacing (100px margins)
- **Smooth Curves**: Using spline interpolation for rounded corners
- **Clear Labels**: Connection labels with matching colors

## Benefits

### User Experience
1. **Clarity**: Each line is independent and easy to trace
2. **Simplicity**: No complex routing logic to understand
3. **Visual Appeal**: Clean, professional appearance
4. **Documentation Ready**: Suitable for technical documents

### Technical Benefits
1. **Maintainable**: Simple code that's easy to modify
2. **Performance**: Faster rendering without collision detection
3. **Predictable**: Consistent routing behavior
4. **Scalable**: Works well with many connections

## Visual Example

### Before (Complex Routing):
```
Master0 ──┐
         ├──[Complex paths with multiple segments]
Master1 ──┼──[Overlapping routing channels]
         │
Master2 ──┘
```

### After (Simplified Routing):
```
Master0 ━━━━┓    (Blue)
            ┃
Master1 ━━━━╋━━━ (Indigo)
            ┃
Master2 ━━━━┛    (Purple)
```

## Implementation Details

### Master Connections
- Start: Center bottom of master block
- End: Top of interconnect
- Routing: Direct if aligned, L-shape with 40% midpoint otherwise

### Slave Connections
- Start: Bottom of interconnect
- End: Center top of slave block
- Routing: Direct if aligned, L-shape with 60% midpoint otherwise

### Color Assignment
- Colors cycle through 8 predefined values
- Master i gets colors[i % 8]
- Slave i gets same color as Master i

## Testing
Run `test_simplified_routing.py` to see the new routing in action with the Complex AXI4 template.