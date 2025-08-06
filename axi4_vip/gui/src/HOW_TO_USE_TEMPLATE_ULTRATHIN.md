# How to Use Complex AXI4 Template with Complete 12/12 Steps

## Current Issue
Your screenshot shows **8/12 (67%)** with **[SUCCESS] Done** - this is **WRONG**!
You should see **12/12 (100%)** before SUCCESS.

**Missing Steps**: 9, 10, 11, 12 are not executing.

## Solution: Use Ultrathin Mode

### Method 1: Launch with Ultrathin Script (Recommended)

1. **Navigate to GUI directory**:
   ```bash
   cd /home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/scripts
   ```

2. **Launch GUI with ultrathin mode**:
   ```bash
   ./launch_gui_ultrathin.sh
   ```

3. **Load Complex AXI4 template**:
   - Go to Templates menu → "Complex AXI4 System"

4. **Generate VIP Environment**:
   - Select VIP → Generate VIP Environment
   - Choose RTL Integration Mode
   - Click Generate VIP Environment

5. **Expected Result**:
   - Progress: **1/12 → 2/12 → 3/12 → ... → 12/12**
   - Success shown only at **12/12 (100%)**

### Method 2: Manual Environment Setup

If launch script doesn't work, set environment variables manually:

```bash
export VIP_DEFER_IMPORTS=true
export VIP_USE_FINAL=true  
export VIP_FAST_GEN=true
export VIP_LAZY_LOAD=true
export VIP_SKIP_COMPONENT_INIT=true

# Then launch GUI
cd /home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/scripts
./launch_gui.sh
```

### Method 3: Re-apply Smart Patches (If Above Fails)

If you want the automatic detection back without breaking VIP:

```bash
cd /home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src

# Apply only the safe template detection
python3 fix_template_detection_safe.py
```

## Complete Step-by-Step Process

### Step 1: Verify Environment
```bash
echo $VIP_DEFER_IMPORTS  # Should show "true"
echo $VIP_USE_FINAL      # Should show "true"  
echo $VIP_FAST_GEN       # Should show "true"
```

### Step 2: Launch GUI
```bash
cd /home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/scripts
./launch_gui_ultrathin.sh
```

### Step 3: Load Template
- Templates menu → "Complex AXI4 System"
- Should see: 8 Masters, 8 Slaves, 128-bit data, 40-bit addr

### Step 4: Generate VIP
- VIP menu → Generate VIP Environment  
- Select RTL Integration Mode
- Generate RTL from current configuration
- Target Simulator: VCS
- Click "Generate VIP Environment"

### Step 5: Watch Progress
You should see ALL these steps:
```
Step 1/12: Starting VIP generation (8%)
Step 2/12: Generating RTL from configuration (17%)
Step 3/12: Validating RTL generation (25%)
Step 4/12: Completing RTL generation (33%)
Step 5/12: Creating RTL integration environment (42%)
Step 6/12: Loading VIP environment generator (50%)
Step 7/12: Generating environment files (58%)
Step 8/12: Generating test files (67%)
Step 9/12: Generating top files (75%)          ← YOU'RE MISSING THESE
Step 10/12: Generating simulation files (83%)   ← YOU'RE MISSING THESE  
Step 11/12: Generating documentation (92%)      ← YOU'RE MISSING THESE
Step 12/12: Finalizing environment (100%)      ← YOU'RE MISSING THESE
```

### Step 6: Verify Success
- Progress bar should show **12/12 (100%)**
- Button should show **[SUCCESS] Done** only after 12/12
- Status should show full path to generated environment

## Troubleshooting

### If Still Shows 8/12:
1. **Check Environment Variables**:
   ```bash
   env | grep VIP_
   ```

2. **Restart GUI Completely**:
   - Close current GUI
   - Launch with ultrathin script

3. **Check Console Output**:
   Look for:
   ```
   [INFO] VIP components loaded successfully
   [DEBUG WRAPPER FINAL] Starting VIP generation: mode=rtl_integration
   [DEBUG WRAPPER FINAL] Will execute steps 1 to 12
   ```

### If VIP Button Missing:
The ultrathin mode should preserve VIP functionality. If button is missing:
```bash
# Check VIP integration status
cd /home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src
python3 debug_vip_flow.py
```

## What Each Missing Step Does

**Step 9: Generating top files**
- Creates testbench top module
- Sets up simulation hierarchy

**Step 10: Generating simulation files**  
- Creates Makefile for simulation
- Generates compile scripts
- Sets up simulator configurations

**Step 11: Generating documentation**
- Creates README.md
- Generates integration guide
- Documents configuration

**Step 12: Finalizing environment**
- Creates completion marker
- Finalizes file permissions
- Generates summary report

## Expected File Structure After 12/12

After complete generation, you should see:
```
axi4_vip_env_rtl_integration/
├── README.md                    ← From step 11
├── INTEGRATION_GUIDE.md         ← From step 11  
├── generation_complete.txt      ← From step 12
├── top/axi4_tb_top.sv          ← From step 9
├── sim/Makefile                ← From step 10
├── sim/axi4_compile.f          ← From step 10
└── ... (other files)
```

## Summary

**Your 8/12 is incomplete!** Use the ultrathin mode to get all 12 steps:

```bash
cd /home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/scripts
./launch_gui_ultrathin.sh
```

Then load Complex AXI4 template and generate - you should see **12/12 (100%)** completion.