#!/usr/bin/env python3
"""
Script to apply VIP environment fixes to existing VIP environments
This fixes the issue where slave agents are not responding properly
"""

import os
import sys
import argparse
import json

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src'))

from vip_environment_generator_enhanced_fix import VIPEnvironmentGeneratorEnhancedFix

def load_config(vip_path):
    """Load configuration from VIP directory"""
    config_file = os.path.join(vip_path, "config.json")
    
    if os.path.exists(config_file):
        with open(config_file, 'r') as f:
            return json.load(f)
    else:
        # Try to infer from existing files
        print(f"[INFO] No config.json found, inferring configuration...")
        
        # Count masters and slaves from environment file
        env_file = os.path.join(vip_path, "env/axi4_env.sv")
        if os.path.exists(env_file):
            with open(env_file, 'r') as f:
                content = f.read()
                
            # Look for master_agent and slave_agent arrays
            import re
            master_match = re.search(r'axi4_master_agent master_agent\[(\d+)\]', content)
            slave_match = re.search(r'axi4_slave_agent slave_agent\[(\d+)\]', content)
            
            if master_match and slave_match:
                num_masters = int(master_match.group(1))
                num_slaves = int(slave_match.group(1))
                
                # Create dummy config
                class DummyConfig:
                    def __init__(self):
                        self.masters = [{"id": i} for i in range(num_masters)]
                        self.slaves = [{"id": i} for i in range(num_slaves)]
                        
                return DummyConfig()
        
        # Default configuration
        class DefaultConfig:
            def __init__(self):
                self.masters = [{"id": 0}, {"id": 1}]
                self.slaves = [{"id": 0}, {"id": 1}]
                
        return DefaultConfig()

def main():
    parser = argparse.ArgumentParser(description='Apply VIP environment fixes')
    parser.add_argument('vip_path', help='Path to VIP environment to fix')
    parser.add_argument('--backup', action='store_true', help='Create backup of original files')
    
    args = parser.parse_args()
    
    # Validate VIP path
    if not os.path.exists(args.vip_path):
        print(f"Error: VIP path does not exist: {args.vip_path}")
        sys.exit(1)
        
    # Check if it's a valid VIP environment
    required_dirs = ['env', 'test', 'virtual_seq', 'seq/slave_sequences']
    for dir_name in required_dirs:
        dir_path = os.path.join(args.vip_path, dir_name)
        if not os.path.exists(dir_path):
            print(f"Error: Required directory not found: {dir_path}")
            print("This doesn't appear to be a valid VIP environment")
            sys.exit(1)
    
    # Load configuration
    config = load_config(args.vip_path)
    
    # Create backup if requested
    if args.backup:
        import shutil
        import datetime
        
        backup_suffix = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        files_to_backup = [
            "virtual_seq/axi4_virtual_write_seq.sv",
            "virtual_seq/axi4_virtual_read_seq.sv",
            "virtual_seq/axi4_virtual_write_read_seq.sv",
            "virtual_seq/axi4_virtual_stress_seq.sv",
            "test/axi4_base_test.sv",
            "test/axi4_basic_rw_test.sv",
            "test/axi4_stress_test.sv",
            "seq/slave_sequences/axi4_slave_mem_seq.sv"
        ]
        
        print(f"[BACKUP] Creating backups with suffix: {backup_suffix}")
        for file_path in files_to_backup:
            full_path = os.path.join(args.vip_path, file_path)
            if os.path.exists(full_path):
                backup_path = f"{full_path}.backup_{backup_suffix}"
                shutil.copy2(full_path, backup_path)
                print(f"[BACKUP] Created: {backup_path}")
    
    # Apply fixes
    print(f"\n[FIX] Applying VIP environment fixes to: {args.vip_path}")
    
    # Create dummy base generator
    class DummyGenerator:
        def __init__(self, config):
            self.config = config
            
    base_gen = DummyGenerator(config)
    fixer = VIPEnvironmentGeneratorEnhancedFix(base_gen)
    
    try:
        fixer.apply_fixes(args.vip_path)
        print("\n[SUCCESS] VIP environment fixes applied successfully!")
        print("\nThe following improvements have been made:")
        print("1. Virtual sequences now properly start slave memory sequences")
        print("2. Test base class includes timeout mechanism (default: 10ms)")
        print("3. Enhanced debug logging throughout the environment")
        print("4. Slave sequences properly respond to master requests")
        print("\nYou can now run your tests without hanging issues!")
        
    except Exception as e:
        print(f"\n[ERROR] Failed to apply fixes: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()