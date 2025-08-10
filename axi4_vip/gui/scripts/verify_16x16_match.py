#!/usr/bin/env python3
"""
Verify that the patched VIP generator creates the same structure as 16x16_vip reference
"""

import os
import sys
import difflib
import filecmp
from pathlib import Path

def compare_file_content(file1, file2, ignore_timestamps=True):
    """Compare two files, optionally ignoring timestamp differences"""
    try:
        with open(file1, 'r') as f1:
            content1 = f1.readlines()
        with open(file2, 'r') as f2:
            content2 = f2.readlines()
        
        if ignore_timestamps:
            # Filter out lines with dates/timestamps
            content1 = [line for line in content1 if 'Date:' not in line and 'timestamp' not in line.lower()]
            content2 = [line for line in content2 if 'Date:' not in line and 'timestamp' not in line.lower()]
        
        # Compare filtered content
        diff = list(difflib.unified_diff(content1, content2, lineterm=''))
        return len(diff) == 0, diff
    except Exception as e:
        return False, [str(e)]

def verify_structure_match(reference_dir, generated_dir):
    """Verify that generated structure matches reference"""
    
    reference_path = Path(reference_dir)
    generated_path = Path(generated_dir)
    
    if not reference_path.exists():
        print(f"❌ Reference directory not found: {reference_dir}")
        return False
    
    if not generated_path.exists():
        print(f"❌ Generated directory not found: {generated_dir}")
        print("   Please generate a VIP using the GUI first")
        return False
    
    print(f"📁 Comparing structures:")
    print(f"   Reference: {reference_dir}")
    print(f"   Generated: {generated_dir}")
    print()
    
    # Key files to check in sim directory
    sim_files_to_check = [
        "sim/Makefile",
        "sim/Makefile.enhanced",
        "sim/axi4_compile.f"
    ]
    
    results = []
    all_match = True
    
    for file_path in sim_files_to_check:
        ref_file = reference_path / file_path
        gen_file = generated_path / file_path
        
        # Check if file exists in both places
        ref_exists = ref_file.exists()
        gen_exists = gen_file.exists()
        
        if ref_exists and gen_exists:
            # Compare content
            match, diff = compare_file_content(ref_file, gen_file, ignore_timestamps=True)
            if match:
                results.append(f"✅ {file_path}: Matches (ignoring timestamps)")
            else:
                results.append(f"⚠️  {file_path}: Content differs")
                all_match = False
                # Show first few differences
                if len(diff) > 0 and len(diff) < 20:
                    print(f"\n   Differences in {file_path}:")
                    for line in diff[:10]:
                        print(f"     {line}")
        elif ref_exists and not gen_exists:
            results.append(f"❌ {file_path}: Missing in generated")
            all_match = False
        elif not ref_exists and gen_exists:
            results.append(f"ℹ️  {file_path}: Extra file (not in reference)")
    
    # Check directory structure
    ref_dirs = set()
    gen_dirs = set()
    
    for root, dirs, files in os.walk(reference_path):
        rel_path = Path(root).relative_to(reference_path)
        ref_dirs.add(str(rel_path))
    
    for root, dirs, files in os.walk(generated_path):
        rel_path = Path(root).relative_to(generated_path)
        gen_dirs.add(str(rel_path))
    
    # Key directories to verify
    key_dirs = [
        "sim", "sim/logs", "sim/waves", "sim/coverage", "sim/scripts",
        "agent", "agent/master_agent_bfm", "agent/slave_agent_bfm",
        "env", "test", "seq", "seq/master_sequences", "seq/slave_sequences",
        "virtual_seq", "virtual_seqr", "pkg", "intf", "intf/axi4_interface",
        "top", "rtl_wrapper", "master", "slave"
    ]
    
    print("\n📂 Directory Structure Check:")
    for dir_name in key_dirs:
        if dir_name in ref_dirs and dir_name in gen_dirs:
            results.append(f"✅ Directory: {dir_name}")
        elif dir_name in ref_dirs and dir_name not in gen_dirs:
            results.append(f"❌ Directory missing: {dir_name}")
            all_match = False
        # Don't report extra directories as errors
    
    # Print results
    print("\n📊 Verification Results:")
    for result in results:
        print(f"   {result}")
    
    return all_match

def check_makefile_consistency(generated_dir):
    """Check specific Makefile settings match 16x16 reference"""
    makefile_path = Path(generated_dir) / "sim" / "Makefile"
    
    if not makefile_path.exists():
        print(f"❌ Makefile not found at {makefile_path}")
        return False
    
    with open(makefile_path, 'r') as f:
        content = f.read()
    
    # Check for key patterns that should match 16x16
    checks = [
        ("TEST ?= axi4_base_test", "Default test name"),
        ("axi4_compile.f", "Compile file name"),
        ("VIP_ROOT = ..", "VIP root setting"),
        ("vcs $(VCS_COMP_OPTS) -f $(VIP_ROOT)/sim/axi4_compile.f", "Compile command"),
    ]
    
    print("\n🔍 Makefile Consistency Check:")
    all_good = True
    for pattern, description in checks:
        if pattern in content:
            print(f"   ✅ {description}: Found '{pattern}'")
        else:
            print(f"   ❌ {description}: Missing '{pattern}'")
            all_good = False
    
    # Check that wrong patterns are NOT present
    bad_patterns = [
        ("axi4_vip_rtl_compile.f", "Should not use vip_rtl compile file"),
        ("axi4_rtl_integration_test", "Should not use rtl_integration test name"),
    ]
    
    for pattern, description in bad_patterns:
        if pattern not in content:
            print(f"   ✅ {description}: Correctly absent")
        else:
            print(f"   ❌ {description}: Found unwanted '{pattern}'")
            all_good = False
    
    return all_good

def main():
    """Main verification function"""
    print("=== VIP Structure Verification Tool ===")
    print("Verifies generated VIP matches 16x16_vip reference structure\n")
    
    # Reference directory
    reference_dir = "/home/timtim01/eda_test/project/gen_amba_2025/16x16_vip/axi4_vip_env_rtl_integration"
    
    # You would need to generate a test VIP first using the GUI
    # For now, we'll check if a test directory exists
    test_dirs = [
        "/tmp/test_16x16_vip",
        "/home/timtim01/eda_test/project/gen_amba_2025/test_16x16_vip"
    ]
    
    generated_dir = None
    for test_dir in test_dirs:
        if os.path.exists(test_dir):
            generated_dir = test_dir
            break
    
    if not generated_dir:
        print("ℹ️  No test VIP found. To verify:")
        print("   1. Launch the GUI using launch_gui_ultrathin.sh")
        print("   2. Create a 16x16 configuration")
        print("   3. Generate VIP to /tmp/test_16x16_vip")
        print("   4. Run this verification script again")
        print()
        print("Checking reference structure exists...")
        if os.path.exists(reference_dir):
            print(f"✅ Reference found: {reference_dir}")
            # Just check the reference Makefile
            check_makefile_consistency(reference_dir)
        return
    
    # Perform verification
    print("=" * 60)
    structure_match = verify_structure_match(reference_dir, generated_dir)
    
    print("\n" + "=" * 60)
    makefile_ok = check_makefile_consistency(generated_dir)
    
    print("\n" + "=" * 60)
    if structure_match and makefile_ok:
        print("\n✅ SUCCESS: Generated VIP structure matches 16x16_vip reference!")
    else:
        print("\n⚠️  Some differences found. Review the details above.")
    
    return structure_match and makefile_ok

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)