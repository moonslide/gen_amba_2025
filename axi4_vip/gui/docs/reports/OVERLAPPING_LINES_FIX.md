# Overlapping Lines Fix - Technical Documentation

## Problem
Multiple connection lines were overlapping each other, creating a messy, unprofessional appearance where lines would follow the exact same path.

## Solution: Unique Routing Channels

### 1. Pre-calculated Routing Levels
Each connection gets a unique Y-level in the routing zone:

```
Masters (top) → Routing Zone → Interconnect → Routing Zone → Slaves (bottom)
     ↓              ↓                              ↓              ↓
   Y=50-190    Y=205-285        Y=300         Y=315-485      Y=500-690
```

### 2. Routing Level Calculation
```python
# For masters (example with 8 masters)
routing_zone_height = 80px
routing_levels = [205, 215, 225, 235, 245, 255, 265, 275]  # Each master gets unique Y

# For slaves (example with 8 slaves)  
routing_zone_height = 170px
slave_routing_levels = [315, 336, 357, 378, 399, 420, 441, 462]  # Each slave gets unique Y
```

### 3. X-Offset Application
To prevent vertical segment overlaps:
```python
x_offset = 3 * (i % 3) - 3  # Results in: -3, 0, +3, -3, 0, +3...
```

### 4. Interconnect Point Distribution
Connection points on the interconnect are evenly distributed:
```python
conn_x = interconnect_left + 20 + (i + 1) * spacing  # Uses original index, not sorted
```

## Implementation Details

### Strategy 1: Direct Lines (with offsets)
- Direct connections now include small X-offsets
- Prevents multiple direct lines from perfectly overlapping

### Strategy 2: L-Shaped Routing (unique levels)
- Each connection uses its pre-assigned routing level
- No two connections share the same horizontal routing Y-coordinate

### Strategy 3: Safe Routing (with spacing)
- Fallback routing also uses unique levels
- Additional spacing ensures no overlaps even in complex scenarios

## Visual Result

### Before Fix:
```
Master0 ─┐
Master1 ─┼─────────── [Multiple lines on same path]
Master2 ─┘
```

### After Fix:
```
Master0 ─────┐
              ├───── [Each line has unique path]
Master1 ──────┼─────
              │
Master2 ───────┘
```

## Benefits
1. **Clean Appearance**: No tangled or overlapping lines
2. **Professional Layout**: Suitable for documentation
3. **Clear Traceability**: Each connection can be visually followed
4. **Scalable**: Works with many connections (tested with 8×8)

## Testing
The fix has been verified with the Complex AXI4 template (8 masters × 8 slaves = 16 connections) and shows clean, non-overlapping routing for all connections.