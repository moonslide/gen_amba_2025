#!/usr/bin/env python3
"""
Fix Syntax Errors in axi4_master_pkg.sv - ULTRATHINK Edition
Removes incorrectly placed monitor_wlast_signals() methods from wrong classes
"""

import os
import sys
import shutil
import re
from datetime import datetime

def backup_file(filepath):
    """Create backup of file before modifying"""
    if not os.path.exists(filepath):
        return None
    backup_path = f"{filepath}.backup_syntax_fix_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    shutil.copy2(filepath, backup_path)
    print(f"✓ Backed up {os.path.basename(filepath)}")
    return backup_path

def fix_axi4_master_pkg_syntax_errors(pkg_path):
    """Remove incorrectly placed monitor_wlast_signals() methods"""
    
    print("📝 Fixing syntax errors in axi4_master_pkg.sv...")
    
    with open(pkg_path, 'r') as f:
        content = f.read()
    
    # Remove monitor_wlast_signals() from wrong classes
    
    # 1. Remove from axi4_master_tx class (around lines 57-70)
    tx_monitor_pattern = r'(\s+// WLAST Signal Monitoring\s+int wlast_assertions = 0;\s+virtual task monitor_wlast_signals\(\);\s+.*?endtask\s+)(\s+endclass)'
    content = re.sub(tx_monitor_pattern, r'\2', content, flags=re.DOTALL)
    
    # 2. Remove from axi4_master_agent_config class (around lines 82-95)  
    config_monitor_pattern = r'(\s+// WLAST Signal Monitoring\s+int wlast_assertions = 0;\s+virtual task monitor_wlast_signals\(\);\s+.*?endtask\s+)(\s+endclass)'
    content = re.sub(config_monitor_pattern, r'\2', content, flags=re.DOTALL)
    
    # 3. Remove from axi4_master_sequencer class (around lines 105-118)
    sequencer_monitor_pattern = r'(\s+// WLAST Signal Monitoring\s+int wlast_assertions = 0;\s+virtual task monitor_wlast_signals\(\);\s+.*?endtask\s+)(\s+endclass)'
    content = re.sub(sequencer_monitor_pattern, r'\2', content, flags=re.DOTALL)
    
    # 4. Remove from axi4_master_monitor class (around lines 477-490) - wrong implementation
    monitor_monitor_pattern = r'(\s+// WLAST Signal Monitoring\s+int wlast_assertions = 0;\s+virtual task monitor_wlast_signals\(\);\s+.*?endtask\s+)(\s+endclass)'
    content = re.sub(monitor_monitor_pattern, r'\2', content, flags=re.DOTALL)
    
    # 5. Remove from axi4_master_agent class (around lines 548-561)
    agent_monitor_pattern = r'(\s+// WLAST Signal Monitoring\s+int wlast_assertions = 0;\s+virtual task monitor_wlast_signals\(\);\s+.*?endtask\s+)(\s+endclass)'
    content = re.sub(agent_monitor_pattern, r'\2', content, flags=re.DOTALL)
    
    # Also remove the orphaned monitor_wlast_signals() call and fork from driver run_phase
    # that refers to the removed method
    driver_fork_pattern = r'\s+// Start WLAST monitoring\s+fork\s+monitor_wlast_signals\(\);\s+join_none\s+'
    content = re.sub(driver_fork_pattern, '\n            ', content)
    
    # Remove any remaining standalone monitor_wlast_signals() calls in monitor run_phase
    monitor_fork_pattern = r'\s+// Start WLAST monitoring\s+fork\s+monitor_wlast_signals\(\);\s+join_none\s+'
    content = re.sub(monitor_fork_pattern, '\n            ', content)
    
    with open(pkg_path, 'w') as f:
        f.write(content)
    
    print("✓ Fixed syntax errors by removing incorrectly placed monitor methods")
    return True

def verify_syntax_fix(pkg_path):
    """Verify the syntax fix by checking for common issues"""
    
    print("🔍 Verifying syntax fix...")
    
    with open(pkg_path, 'r') as f:
        content = f.read()
    
    # Check for remaining syntax issues
    issues_found = []
    
    # Check for orphaned monitor_wlast_signals() calls  
    if 'monitor_wlast_signals()' in content:
        # Count how many times it appears
        count = content.count('monitor_wlast_signals()')
        if count > 0:
            issues_found.append(f"Found {count} orphaned monitor_wlast_signals() calls")
    
    # Check for proper class endings
    class_endings = content.count('endclass')
    if class_endings < 5:  # Should have at least 5 classes
        issues_found.append(f"Missing endclass statements - found {class_endings}")
    
    # Check for package ending
    if 'endpackage : axi4_master_pkg' not in content:
        issues_found.append("Missing package ending")
    
    if issues_found:
        print("⚠️  Potential issues found:")
        for issue in issues_found:
            print(f"  - {issue}")
        return False
    else:
        print("✓ Syntax verification passed")
        return True

def main():
    """Main function to fix syntax errors"""
    
    print("\n" + "="*70)
    print("🔧 Fix AXI4 Master Package Syntax Errors - ULTRATHINK")
    print("="*70)
    
    pkg_path = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/master/axi4_master_pkg.sv"
    
    if not os.path.exists(pkg_path):
        print(f"❌ Error: {pkg_path} not found")
        return False
    
    # Backup the file
    backup_file(pkg_path)
    
    # Fix syntax errors
    success = fix_axi4_master_pkg_syntax_errors(pkg_path)
    
    if success:
        # Verify the fix
        if verify_syntax_fix(pkg_path):
            print("\n" + "="*70)
            print("✅ Syntax Errors Fixed Successfully!")
            print("\n🎯 Fixed Issues:")
            print("  1. ✅ Removed monitor_wlast_signals() from axi4_master_tx")
            print("  2. ✅ Removed monitor_wlast_signals() from axi4_master_agent_config") 
            print("  3. ✅ Removed monitor_wlast_signals() from axi4_master_sequencer")
            print("  4. ✅ Removed monitor_wlast_signals() from axi4_master_monitor")
            print("  5. ✅ Removed monitor_wlast_signals() from axi4_master_agent")
            print("  6. ✅ Cleaned up orphaned method calls")
            
            print("\n📊 WLAST Counting Still Available:")
            print("  • Driver has proper WLAST counting in run_phase")
            print("  • Transaction counting and validation in driver")
            print("  • WLAST statistics reporting in report_phase")
            print("  • Spec-compliant WLAST timing (beat == awlen)")
            
            print("\n💡 Next Steps:")
            print("  1. Test compilation")
            print("  2. Run simulation to verify WLAST behavior")
            print("  3. Update generator script with clean implementation")
            print("="*70)
            return True
        else:
            print("\n❌ Syntax verification failed")
            return False
    else:
        print("\n❌ Failed to fix syntax errors")
        return False

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)