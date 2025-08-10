#!/usr/bin/env python3
"""Verify ULTRATHINK updates were applied correctly"""

import os

generator_path = "/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_environment_generator.py"

with open(generator_path, 'r') as f:
    content = f.read()

checks = [
    ("ULTRATHINK slave BFM", "ULTRATHINK: Always ready, immediate response"),
    ("ULTRATHINK test timeout", "ULTRATHINK: 1us timeout for guaranteed completion"),
    ("ULTRATHINK mode flag", "ULTRATHINK_MODE"),
    ("ULTRATHINK info messages", "ULTRATHINK Mode: Enabled"),
]

print("\nVerifying ULTRATHINK updates...")
all_found = True
for name, pattern in checks:
    if pattern in content:
        print(f"  ✓ {name}")
    else:
        print(f"  ✗ {name}")
        all_found = False

if all_found:
    print("\n✅ All ULTRATHINK updates verified successfully!")
else:
    print("\n⚠️  Some updates may be missing")
