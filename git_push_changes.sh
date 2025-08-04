#!/bin/bash

# Script to commit and push changes to both main and feature branch
# For fixing AXI4 VIP compilation issues

cd /home/timtim01/eda_test/project/gen_amba_2025

# First, check git status
echo "=== Checking git status ==="
git status

# Create a feature branch for these fixes
BRANCH_NAME="fix/axi4-vip-compilation-issues"
echo -e "\n=== Creating feature branch: $BRANCH_NAME ==="
git checkout -b $BRANCH_NAME

# Add all the changes
echo -e "\n=== Adding changes ==="
git add -A

# Commit with descriptive message
echo -e "\n=== Committing changes ==="
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

# Push to feature branch
echo -e "\n=== Pushing to feature branch ==="
git push -u origin $BRANCH_NAME

# Checkout main branch
echo -e "\n=== Switching to main branch ==="
git checkout main

# Merge feature branch to main
echo -e "\n=== Merging feature branch to main ==="
git merge $BRANCH_NAME

# Push to main
echo -e "\n=== Pushing to main ==="
git push origin main

echo -e "\n=== Git operations completed ==="
echo "Changes have been pushed to both '$BRANCH_NAME' and 'main' branches"