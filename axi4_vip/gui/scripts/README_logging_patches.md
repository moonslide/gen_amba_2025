# Detailed Logging Patches for VIP

## Overview
The `apply_detailed_logging.sh` script adds comprehensive UVM_INFO logging to generated VIP components.

## Features Added
1. **BFM Initialization Messages**
   - Master BFM: "Master BFM signals initialized"
   - Slave BFM: "Slave BFM signals initialized"

2. **Transaction Monitoring**
   - Monitor counts transactions and reports every 100
   - Driver logs transaction details (address, type, size, length)

3. **Throughput Analysis**
   - Scoreboard reports total read/write transactions in report_phase

4. **Configurable Verbosity**
   - Makefile supports UVM_VERBOSITY parameter
   - Default set to UVM_MEDIUM

## Usage
```bash
# Apply patches to a generated VIP
./apply_detailed_logging.sh /path/to/vip/axi4_vip_env_rtl_integration

# Run test with custom verbosity
make run_fsdb TEST=axi4_stress_test UVM_VERBOSITY=UVM_HIGH
```

## Integration
Add to VIP generation workflow:
```python

# Add this to the VIP generation workflow in vip_gui_integration.py

def apply_detailed_logging_patches(vip_dir):
    """Apply detailed logging patches to generated VIP"""
    patch_script = os.path.join(os.path.dirname(__file__), "..", "scripts", "apply_detailed_logging.sh")
    if os.path.exists(patch_script):
        subprocess.run([patch_script, vip_dir], check=True)
        print("✅ Applied detailed logging patches")

```
