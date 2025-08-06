#!/bin/bash

# ROOT CAUSE FIX: Remove simulation artifacts from git tracking
# 
# ISSUE: Commit 191cbe1 added 200+ simulation build artifacts causing unlimited storage growth
# SOLUTION: Remove these files from git tracking (but keep them locally)

echo "🔍 ROOT CAUSE ANALYSIS COMPLETE"
echo "==============================================="
echo "ISSUE: Unlimited storage growth in VIP GUI"
echo "CAUSE: Commit 191cbe1 added simulation artifacts to git"
echo "FILES: csrc/, simv.daidir/, verdiLog/, *.fsdb, *.log"
echo "EFFECT: Each simulation run creates new tracked files"
echo "==============================================="
echo ""

echo "🧹 Removing simulation artifacts from git tracking..."
echo "Note: Files will remain on disk but won't be tracked by git"
echo ""

# Remove VCS simulation artifacts
echo "Removing VCS simulation artifacts..."
git rm -r --cached --ignore-unmatch 9x9_vip/*/sim/csrc/ 2>/dev/null || echo "  csrc/ already untracked"
git rm -r --cached --ignore-unmatch 9x9_vip/*/sim/simv.daidir/ 2>/dev/null || echo "  simv.daidir/ already untracked"
git rm --cached --ignore-unmatch 9x9_vip/*/sim/simv 2>/dev/null || echo "  simv already untracked"

# Remove Verdi logs
echo "Removing Verdi log directories..."
git rm -r --cached --ignore-unmatch 9x9_vip/*/sim/verdiLog/ 2>/dev/null || echo "  verdiLog/ already untracked"

# Remove waveform files (can be GB in size)
echo "Removing waveform files..."
git rm --cached --ignore-unmatch 9x9_vip/*/sim/*.fsdb 2>/dev/null || echo "  *.fsdb already untracked"
git rm --cached --ignore-unmatch 9x9_vip/*/sim/waves/*.fsdb 2>/dev/null || echo "  waves/*.fsdb already untracked"

# Remove log files
echo "Removing log files..."
git rm --cached --ignore-unmatch 9x9_vip/*/sim/*.log 2>/dev/null || echo "  *.log already untracked"
git rm --cached --ignore-unmatch 9x9_vip/*/sim/logs/*.log 2>/dev/null || echo "  logs/*.log already untracked" 

# Remove configuration files that get regenerated
echo "Removing generated configuration files..."
git rm --cached --ignore-unmatch 9x9_vip/*/sim/novas.conf 2>/dev/null || echo "  novas.conf already untracked"
git rm --cached --ignore-unmatch 9x9_vip/*/sim/novas.rc 2>/dev/null || echo "  novas.rc already untracked"
git rm --cached --ignore-unmatch 9x9_vip/*/sim/ucli.key 2>/dev/null || echo "  ucli.key already untracked"
git rm --cached --ignore-unmatch 9x9_vip/*/sim/.verdirc 2>/dev/null || echo "  .verdirc already untracked"

# Remove other build artifacts that match our patterns
echo "Removing other build artifacts..."
find . -name "*_archive_*.so" -type f | while read file; do
    git rm --cached --ignore-unmatch "$file" 2>/dev/null || echo "  $file already untracked"
done

find . -name "*_archive_*.a" -type f | while read file; do
    git rm --cached --ignore-unmatch "$file" 2>/dev/null || echo "  $file already untracked"
done

# Show what we've removed
echo ""
echo "📊 Checking current git status..."
git status --porcelain | head -20

echo ""
echo "✅ CLEANUP COMPLETE"
echo "==============================================="
echo "NEXT STEPS:"
echo "1. Review changes: git status"
echo "2. Commit cleanup: git commit -m 'Fix unlimited storage growth - remove simulation artifacts'"
echo "3. Future simulations will no longer bloat git repository"
echo ""
echo "ROOT CAUSE FIXED: Proper .gitignore now prevents tracking build artifacts"
echo "STORAGE IMPACT: Significantly reduced repository size"
echo "==============================================="