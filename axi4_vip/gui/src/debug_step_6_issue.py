#!/usr/bin/env python3
"""
Debug why generation stops at step 6
"""

import os
import sys

# Set ultrathin environment
os.environ['VIP_DEFER_IMPORTS'] = 'true'
os.environ['VIP_USE_FINAL'] = 'true'

sys.path.insert(0, '/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src')

print("=== DEBUGGING STEP 6 ISSUE ===\n")

# Check the parent's run method
print("1. Checking parent VIPGenerationThread.run() flow:")
from vip_gui_integration import VIPGenerationThread

# Get the source of run method
import inspect
run_source = inspect.getsource(VIPGenerationThread.run)

# Find key lines
lines = run_source.split('\n')
for i, line in enumerate(lines):
    if 'update_progress' in line and ('completed' in line or 'successfully' in line):
        print(f"   Line {i}: {line.strip()}")
    if 'self.completed = True' in line:
        print(f"   Line {i}: {line.strip()} <- MARKS THREAD AS COMPLETE")

print("\n2. The issue:")
print("   - Parent run() executes RTL generation (steps 1-6)")  
print("   - Parent sends 'RTL integration environment completed' at step 6")
print("   - Parent sends 'VIP generation completed successfully!' ")
print("   - Parent sets self.completed = True")
print("   - Thread terminates before wrapper can do steps 7-12")

print("\n3. Solution:")
print("   The ultrathin run() method should NOT use parent's RTL generation")
print("   Instead, let the wrapper handle ALL steps 1-12")

print("\n4. Testing message detection:")
from vip_gui_integration_ultrathin_final import patched_update_progress

# Create mock thread
class MockThread:
    def __init__(self):
        self.current_step = 6
        
mock = MockThread()

# Test messages at step 6
test_msgs = [
    "RTL integration environment completed",
    "VIP generation completed successfully!",
    "Generating environment files"  # This should be step 7
]

print("\nMessages at step 6:")
for msg in test_msgs:
    # Check if would be skipped
    premature_messages = [
        "VIP generation completed successfully!",
        "RTL integration environment completed", 
        "VIP environment generation completed",
        "Environment generation completed"
    ]
    
    if any(pmsg in msg for pmsg in premature_messages) and mock.current_step < 12:
        print(f"  '{msg}' -> SKIPPED (premature)")
    else:
        print(f"  '{msg}' -> PROCESSED")

print("\n" + "="*50)