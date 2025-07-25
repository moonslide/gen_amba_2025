# Output Directory Configuration Guide

## Overview

The AMBA Bus Matrix GUI now supports customizable output directories for both VIP configuration files and generated Verilog RTL. This allows you to organize your outputs by project, version, or any structure that suits your workflow.

## Main GUI - Verilog Output

### Location
- Above the "Generate Verilog" button
- Section labeled "Output Directory"

### Default Directory
- `output/rtl`

### How to Change
1. Click the "Browse" button next to the directory path
2. Select your desired output directory
3. The directory will be created if it doesn't exist

### What Gets Generated Here
- Main interconnect Verilog file (e.g., `axi4_interconnect.v`)
- Any additional RTL files
- Generation scripts

## VIP Panel - Dual Output Directories

### Location
- In the VIP panel (bottom of main GUI)
- Section labeled "Output Directories"

### Two Separate Directories

#### 1. VIP Output Directory
**Default:** `../axi4_vip_sim/output`

**Contents:**
- `configs/` - JSON configuration files
- `scripts/` - Test execution scripts  
- `reports/` - Configuration summary reports
- `logs/` - Placeholder for simulation logs
- `waves/` - Placeholder for waveform files
- `coverage/` - Placeholder for coverage reports

#### 2. Verilog Output Directory
**Default:** `output/rtl`

**Contents:**
- Generated RTL when using "Generate RTL First" button in VIP panel
- Same as main GUI Verilog output

### How to Change
1. Enter paths directly in the text fields
2. Use "Browse..." buttons to select directories
3. Click "Create Output Directories" to create the structure

## Workflow Examples

### Example 1: Project-Based Organization
```
projects/
├── project_alpha/
│   ├── vip_configs/
│   └── rtl/
├── project_beta/
│   ├── vip_configs/
│   └── rtl/
```

### Example 2: Version-Based Organization
```
outputs/
├── v1.0/
│   ├── vip/
│   └── rtl/
├── v1.1/
│   ├── vip/
│   └── rtl/
```

### Example 3: Date-Based Organization
```
outputs/
├── 2025-07-24/
│   ├── vip/
│   └── rtl/
├── 2025-07-25/
│   ├── vip/
│   └── rtl/
```

## Best Practices

1. **Use Absolute Paths**: For clarity and to avoid confusion
2. **Create Directory Structure First**: Use "Create Output Directories" button
3. **Consistent Naming**: Use a naming convention for your projects
4. **Separate VIP and RTL**: Keep configuration and implementation separate
5. **Version Control**: Add generated directories to `.gitignore` if needed

## Quick Reference

| Output Type | Default Location | Contains |
|------------|------------------|----------|
| Main GUI Verilog | `output/rtl` | Generated RTL files |
| VIP Configs | `../axi4_vip_sim/output` | JSON, scripts, reports |
| VIP Panel Verilog | `output/rtl` | RTL for VIP integration |

## Tips

- The GUI remembers your directory selections during the session
- Directories are created automatically when you generate/export
- Use relative paths for portability, absolute paths for clarity
- The "Create Output Directories" button pre-creates the entire structure