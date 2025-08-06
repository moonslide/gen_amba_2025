#!/usr/bin/env python3
"""
Debug why Complex AXI4 template stops at 6/12 steps
"""

import os
import sys
import json

print("=== Complex AXI4 Template Debug ===\n")

# 1. Check template contents
template_path = "/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/templates/complex_axi4_system.json"
print(f"[1] Template Analysis: {template_path}")

with open(template_path, 'r') as f:
    template_data = json.load(f)

print(f"  Bus Type: {template_data['bus_type']}")
print(f"  Data Width: {template_data['data_width']}")
print(f"  Address Width: {template_data['addr_width']}")
print(f"  Masters: {len(template_data['masters'])}")
print(f"  Slaves: {len(template_data['slaves'])}")
print(f"  Arbitration: {template_data.get('arbitration', 'N/A')}")

print("\n  Master Details:")
for i, master in enumerate(template_data['masters']):
    print(f"    {i+1}. {master['name']} (ID:{master['id_width']}, QoS:{master['qos_support']}, User:{master.get('user_width', 'N/A')})")

print("\n  Slave Details:")
for i, slave in enumerate(template_data['slaves']):
    print(f"    {i+1}. {slave['name']} (Addr:0x{slave['base_address']:X}, Size:{slave['size']}KB, Type:{slave['memory_type']})")

# 2. Check if ultrathin mode is being used
print(f"\n[2] Environment Check:")
print(f"  VIP_DEFER_IMPORTS: {os.environ.get('VIP_DEFER_IMPORTS', 'not set')}")
print(f"  VIP_USE_FINAL: {os.environ.get('VIP_USE_FINAL', 'not set')}")
print(f"  VIP_FAST_GEN: {os.environ.get('VIP_FAST_GEN', 'not set')}")

# 3. Potential issues analysis
print(f"\n[3] Potential Issues Analysis:")

# Check for high complexity that might trigger different behavior
total_complexity = len(template_data['masters']) * len(template_data['slaves'])
print(f"  Complexity Score (M*S): {total_complexity}")
if total_complexity > 32:
    print(f"    WARNING: High complexity ({total_complexity}) might trigger different code path")

# Check for wide data/address paths that might cause memory issues
if template_data['data_width'] > 64:
    print(f"    WARNING: Wide data width ({template_data['data_width']}) might cause issues")
    
if template_data['addr_width'] > 32:
    print(f"    WARNING: Wide address width ({template_data['addr_width']}) might cause issues")

# Check for QoS usage which might affect generation
qos_masters = [m for m in template_data['masters'] if m.get('qos_support', False)]
print(f"  QoS-enabled masters: {len(qos_masters)}/{len(template_data['masters'])}")
if len(qos_masters) > 4:
    print(f"    WARNING: Many QoS masters ({len(qos_masters)}) might affect generation")

# Check for USER signal complexity
user_widths = [m.get('user_width', 0) for m in template_data['masters']]
max_user_width = max(user_widths) if user_widths else 0
print(f"  Max USER width: {max_user_width}")
if max_user_width > 8:
    print(f"    WARNING: Wide USER signals ({max_user_width}) might cause issues")

# 4. Check if this triggers non-ultrathin mode
print(f"\n[4] Code Path Analysis:")
print("When template is loaded, the VIP generation might use different paths:")
print("- Template loading calls load_template() which sets current_config")
print("- If ultrathin mode is not properly activated, original heavy VIP generator is used")
print("- Original generator might stop at step 6 due to complexity or errors")

print(f"\n[5] Recommendations:")
print("1. Ensure ultrathin mode is active when using complex templates")
print("2. Check if original VIP generator has limits on master/slave count")
print("3. Look for error messages or exceptions that cause early termination")
print("4. Test with simpler template to confirm issue is complexity-related")

print(f"\n=== Debug Complete ===")