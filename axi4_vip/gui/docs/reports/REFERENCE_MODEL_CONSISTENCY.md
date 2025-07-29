# Bus Matrix Reference Model - 100% GUI Consistency

## Overview

The AXI4 VIP GUI now generates a bus matrix reference model that is **100% consistent** with the GUI settings. This reference model serves as a golden model for verification, ensuring that the RTL behavior matches the expected behavior defined by the GUI configuration.

## How Consistency is Achieved

### 1. Single Source of Truth
The GUI configuration is the **single source of truth**. All parameters are extracted directly from the GUI and used to generate both:
- RTL code (via gen_amba_axi)
- Reference model (via VIPBusMatrixReferenceModel)

### 2. Configuration Hash Verification
```python
# Configuration is hashed to ensure consistency
config_hash = hashlib.sha256(config_str.encode()).hexdigest()[:16]
```
- Both RTL and reference model store this hash
- Verification can compare hashes to ensure they match
- Any configuration mismatch is immediately detected

### 3. Key Configuration Parameters

The following parameters are synchronized between GUI and reference model:

#### Bus Configuration
- `num_masters`: Number of master interfaces
- `num_slaves`: Number of slave interfaces  
- `data_width`: Data bus width (32, 64, 128, 256, 512, 1024 bits)
- `addr_width`: Address bus width
- `id_width`: Transaction ID width
- `user_width`: User-defined signal width

#### Memory Map
Each slave has:
- `base_addr`: Starting address
- `end_addr`: Ending address
- `size`: Address range size
- `type`: memory/peripheral
- `access`: read_write/read_only/write_only
- `secure`: Security attribute
- `cacheable`: Cache attribute
- `executable`: Execute permission

#### Features
- `support_qos`: Quality of Service enable
- `support_region`: Region identifier enable
- `support_exclusive`: Exclusive access enable
- `support_user`: User signals enable
- `support_axi3`: AXI3 compatibility mode
- `support_ace_lite`: ACE-Lite coherency

#### Arbitration
- `arbitration_scheme`: round_robin/fixed_priority/qos_based/weighted
- `qos_enable`: QoS-based arbitration
- `qos_scheme`: QoS implementation method

### 4. Reference Model Components

The reference model includes these SystemVerilog components that mirror RTL behavior:

1. **axi4_bus_matrix_model.sv**
   - Main transaction-level model
   - Routes transactions based on address decoding
   - Applies ID mapping identical to RTL
   - Tracks outstanding transactions

2. **axi4_routing_model.sv**
   - Models connectivity between masters and slaves
   - Tracks active routes
   - Enforces route availability

3. **axi4_arbitration_model.sv**
   - Implements same arbitration as RTL
   - Calculates arbitration delays
   - Supports all arbitration schemes

4. **axi4_id_mapping_model.sv**
   - Maps IDs exactly as RTL does
   - Uses same ID base and mask calculation
   - Provides reverse mapping for responses

5. **axi4_address_decoder_model.sv**
   - Decodes addresses to slaves
   - Uses exact same memory map as RTL
   - Generates DECERR for unmapped addresses

6. **axi4_exclusive_monitor_model.sv**
   - Tracks exclusive reservations
   - Implements same timeout behavior
   - Predicts EXOKAY/OKAY responses

## Usage Example

### 1. GUI Configuration
```python
# In GUI, set configuration
gui.num_masters = 4
gui.num_slaves = 4
gui.data_width = 128
gui.arbitration_scheme = "qos_based"
```

### 2. Generate Reference Model
```python
# Extract configuration from GUI
integration = VIPGUIReferenceModelIntegration(gui)
config = integration.extract_gui_configuration()

# Generate reference model
integration.generate_reference_model("output_dir")
```

### 3. Generated Files
```
output_dir/
├── gui_configuration.json         # GUI settings
├── reference_model_config.json    # Reference model config
├── configuration_report.txt       # Human-readable report
├── axi4_bus_matrix_model.sv     # Main model
├── axi4_routing_model.sv         # Routing logic
├── axi4_arbitration_model.sv     # Arbitration
├── axi4_id_mapping_model.sv      # ID mapping
├── axi4_address_decoder_model.sv # Address decode
├── axi4_exclusive_monitor_model.sv # Exclusive access
├── axi4_transaction_predictor.sv  # Transaction prediction
└── axi4_reference_scoreboard.sv   # Comparison scoreboard
```

### 4. Verification Testbench
```systemverilog
// The generated testbench ensures configuration matches
if (!ref_model.verify_configuration(bus_cfg)) begin
    $fatal("Reference model configuration mismatch!");
end
```

## Configuration Verification Flow

1. **GUI Setting** → Configuration extracted with hash
2. **RTL Generation** → Same configuration used for RTL
3. **Reference Model** → Same configuration used for model
4. **Runtime Check** → Testbench verifies hashes match
5. **Transaction Check** → Scoreboard compares RTL vs Model

## Key Benefits

1. **Guaranteed Consistency**: Configuration hash ensures exact match
2. **Early Error Detection**: Mismatches caught at simulation start
3. **Accurate Prediction**: Model predicts exact RTL behavior
4. **Complete Coverage**: All bus matrix features modeled
5. **Easy Debugging**: Clear reports show any differences

## Example Configuration Report

```
Bus Matrix Configuration Report
============================================================

Generated: 2024-01-15 10:30:45
Configuration Hash: a3f2b1c8d9e4f5a6

Bus Configuration:
  Masters: 4
  Slaves: 4
  Data Width: 128 bits
  Address Width: 64 bits
  ID Width: 8 bits
  User Width: 32 bits

Memory Map:
  Slave[0] - ddr0:
    Base Address: 0x0000000000000000
    End Address:  0x00000000FFFFFFFF
    Size: 4096.0 MB
    Type: memory
    Access: read_write
    Cacheable: True

  Slave[1] - ddr1:
    Base Address: 0x0000000100000000
    End Address:  0x00000001FFFFFFFF
    Size: 4096.0 MB
    Type: memory
    Access: read_write
    Cacheable: True

Features:
  QoS Support: True
  REGION Support: True
  Exclusive Access: True
  USER Signals: True
  AXI3 Mode: False

Arbitration:
  Scheme: round_robin
  QoS Enabled: True
  QoS Scheme: weighted

This configuration is used for both RTL generation and reference model.
The reference model will predict behavior based on these exact parameters.
```

## Troubleshooting

### Configuration Mismatch
If you see "Configuration mismatch detected!":
1. Check the configuration hashes in error message
2. Ensure GUI settings haven't changed after RTL generation
3. Regenerate either RTL or reference model

### Missing Parameters
If reference model behaves differently:
1. Check all parameters are extracted from GUI
2. Verify memory map is complete
3. Ensure feature enables match

## Conclusion

The bus matrix reference model provides a reliable golden model that is guaranteed to match the GUI configuration. This ensures that verification can confidently compare RTL behavior against expected behavior, with any differences indicating real RTL issues rather than configuration mismatches.