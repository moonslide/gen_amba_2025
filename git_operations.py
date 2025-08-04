#!/usr/bin/env python3
"""
Git operations to commit and push AXI4 VIP compilation fixes
"""

import subprocess
import os

def run_git_command(cmd, cwd=None):
    """Run a git command and return output"""
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True, cwd=cwd)
        print(f"Command: {cmd}")
        if result.stdout:
            print(f"Output: {result.stdout}")
        if result.stderr:
            print(f"Error: {result.stderr}")
        return result.returncode == 0
    except Exception as e:
        print(f"Exception: {e}")
        return False

def main():
    # Change to project directory
    project_dir = "/home/timtim01/eda_test/project/gen_amba_2025"
    os.chdir(project_dir)
    
    print("=== Git Operations for AXI4 VIP Compilation Fixes ===\n")
    
    # Check current status
    print("1. Checking git status...")
    run_git_command("git status")
    
    # Create feature branch
    branch_name = "fix/axi4-vip-compilation-issues"
    print(f"\n2. Creating feature branch: {branch_name}")
    run_git_command(f"git checkout -b {branch_name}")
    
    # Add all changes
    print("\n3. Adding all changes...")
    run_git_command("git add -A")
    
    # Commit changes
    print("\n4. Committing changes...")
    commit_message = """Fix AXI4 VIP compilation issues - TFIPC-L and PCWM-L warnings

- Fixed module instantiation: amba_axi_m8s8 -> axi4_interconnect_m8s8
- Fixed parameter names: WIDTH_DA->DATA_WIDTH, WIDTH_AD->ADDR_WIDTH, WIDTH_ID->ID_WIDTH
- Fixed port name case sensitivity (uppercase to lowercase)
- Fixed slave ID width: WIDTH_SID -> ID_WIDTH for all slave signals
- Added missing AXI4 protocol signals (awcache, awprot, awqos, arcache, arprot, arqos)
- Updated VIP environment generator to include AXI4 protocol signals
- All compilation warnings and errors resolved

🤖 Generated with [Claude Code](https://claude.ai/code)

Co-Authored-By: Claude <noreply@anthropic.com>"""
    
    run_git_command(f'git commit -m "{commit_message}"')
    
    # Push to feature branch
    print(f"\n5. Pushing to feature branch {branch_name}...")
    run_git_command(f"git push -u origin {branch_name}")
    
    # Switch to main
    print("\n6. Switching to main branch...")
    run_git_command("git checkout main")
    
    # Merge feature branch
    print(f"\n7. Merging {branch_name} into main...")
    run_git_command(f"git merge {branch_name}")
    
    # Push to main
    print("\n8. Pushing to main...")
    run_git_command("git push origin main")
    
    print("\n=== Git operations completed ===")
    print(f"Changes have been pushed to both '{branch_name}' and 'main' branches")

if __name__ == "__main__":
    main()