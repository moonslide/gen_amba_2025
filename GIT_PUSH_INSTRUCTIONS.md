# Git Push Instructions for AXI4 VIP Compilation Fixes

Please run the following commands in your terminal to push the changes to both main and a feature branch:

## 1. Navigate to the project directory
```bash
cd /home/timtim01/eda_test/project/gen_amba_2025
```

## 2. Check current git status
```bash
git status
```

## 3. Create a feature branch
```bash
git checkout -b fix/axi4-vip-compilation-issues
```

## 4. Add all changes
```bash
git add -A
```

## 5. Commit with descriptive message
```bash
git commit -m "Fix AXI4 VIP compilation issues - TFIPC-L and PCWM-L warnings

- Fixed module instantiation: amba_axi_m8s8 -> axi4_interconnect_m8s8
- Fixed parameter names: WIDTH_DA->DATA_WIDTH, WIDTH_AD->ADDR_WIDTH, WIDTH_ID->ID_WIDTH
- Fixed port name case sensitivity (uppercase to lowercase)
- Fixed slave ID width: WIDTH_SID -> ID_WIDTH for all slave signals
- Added missing AXI4 protocol signals (awcache, awprot, awqos, arcache, arprot, arqos)
- Updated VIP environment generator to include AXI4 protocol signals
- All compilation warnings and errors resolved

🤖 Generated with [Claude Code](https://claude.ai/code)

Co-Authored-By: Claude <noreply@anthropic.com>"
```

## 6. Push to feature branch
```bash
git push -u origin fix/axi4-vip-compilation-issues
```

## 7. Switch to main branch
```bash
git checkout main
```

## 8. Merge feature branch
```bash
git merge fix/axi4-vip-compilation-issues
```

## 9. Push to main
```bash
git push origin main
```

## Summary of Changes

### Files Modified:
- `8x8_vip/axi4_vip_env_rtl_integration/rtl_wrapper/dut_wrapper.sv` - Fixed all compilation issues
- `axi4_vip/gui/src/vip_environment_generator.py` - Updated to generate correct AXI4 signals

### Files Created (helper scripts):
- `8x8_vip/fix_*.py` - Various Python scripts used to fix the issues
- `8x8_vip/update_generator_axi4_signals.py` - Script to update the generator

### Issues Fixed:
1. **Module instantiation error** - Changed from `amba_axi_m8s8` to `axi4_interconnect_m8s8`
2. **Parameter naming** - Updated to match expected names (DATA_WIDTH, ADDR_WIDTH, ID_WIDTH)
3. **Port case sensitivity** - Changed all port names from uppercase to lowercase
4. **Width mismatches** - Fixed slave ID signals to use ID_WIDTH instead of WIDTH_SID
5. **Missing AXI4 signals** - Added awcache, awprot, awqos, arcache, arprot, arqos for all masters and slaves

The compilation now completes successfully without any errors or warnings.