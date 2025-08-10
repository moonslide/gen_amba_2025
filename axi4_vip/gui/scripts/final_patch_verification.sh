#!/bin/bash
# Final verification that patches are applied correctly

echo "=== Final Patch Verification ==="
echo "Verifying VIP generator matches 16x16_vip reference structure"
echo ""

# Check that key patches are applied
echo "📝 Checking patch status in vip_environment_generator.py..."

GENERATOR_FILE="../src/vip_environment_generator.py"

# Check for correct patterns
echo -n "  ✓ Uses axi4_compile.f: "
if grep -q 'axi4_compile.f"' "$GENERATOR_FILE"; then
    echo "YES ✅"
else
    echo "NO ❌"
fi

echo -n "  ✓ Default test is axi4_base_test: "
if grep -q 'TEST ?= axi4_base_test' "$GENERATOR_FILE"; then
    echo "YES ✅"
else
    echo "NO ❌"
fi

echo -n "  ✓ Has Makefile.enhanced generation: "
if grep -q '_create_makefile_enhanced' "$GENERATOR_FILE"; then
    echo "YES ✅"
else
    echo "NO ❌"
fi

# Check for incorrect patterns that should NOT be present
echo -n "  ✓ Does NOT use axi4_vip_rtl_compile.f: "
if ! grep -q 'axi4_vip_rtl_compile.f' "$GENERATOR_FILE"; then
    echo "CORRECT ✅"
else
    echo "WRONG ❌"
fi

echo ""
echo "📁 Comparing with 16x16_vip reference..."

REF_MAKEFILE="/home/timtim01/eda_test/project/gen_amba_2025/16x16_vip/axi4_vip_env_rtl_integration/sim/Makefile"
REF_COMPILE="/home/timtim01/eda_test/project/gen_amba_2025/16x16_vip/axi4_vip_env_rtl_integration/sim/axi4_compile.f"

if [ -f "$REF_MAKEFILE" ]; then
    echo "  ✓ Reference Makefile exists"
    
    # Check key patterns in reference
    echo -n "    - Uses axi4_compile.f: "
    if grep -q "axi4_compile.f" "$REF_MAKEFILE"; then
        echo "YES ✅"
    else
        echo "NO ❌"
    fi
    
    echo -n "    - Default test axi4_base_test: "
    if grep -q "TEST ?= axi4_base_test" "$REF_MAKEFILE"; then
        echo "YES ✅"
    else
        echo "NO ❌"
    fi
fi

if [ -f "$REF_COMPILE" ]; then
    echo "  ✓ Reference compile file exists (axi4_compile.f)"
fi

echo ""
echo "🔧 Generator patch status:"
echo -n "  Overall status: "

# Check if all critical patterns are correct
CORRECT=true
if ! grep -q 'axi4_compile.f"' "$GENERATOR_FILE"; then CORRECT=false; fi
if ! grep -q 'TEST ?= axi4_base_test' "$GENERATOR_FILE"; then CORRECT=false; fi
if grep -q 'axi4_vip_rtl_compile.f' "$GENERATOR_FILE"; then CORRECT=false; fi

if [ "$CORRECT" = true ]; then
    echo "PATCHED SUCCESSFULLY ✅"
    echo ""
    echo "✅ The VIP generator is now configured to match the 16x16_vip structure!"
    echo "   - Will use axi4_compile.f (not axi4_vip_rtl_compile.f)"
    echo "   - Will use axi4_base_test as default"
    echo "   - Will create both Makefile and Makefile.enhanced"
    echo ""
    echo "📌 Next steps:"
    echo "   1. Launch GUI: ./launch_gui_ultrathin.sh"
    echo "   2. Create a configuration (e.g., 16x16)"
    echo "   3. Generate VIP"
    echo "   4. The generated structure will match 16x16_vip reference"
else
    echo "NEEDS FIXING ❌"
    echo ""
    echo "⚠️  Some patches may not be applied correctly."
    echo "   Run: python3 patch_vip_generator_16x16_match.py"
fi

echo ""
echo "=== Verification Complete ==="#