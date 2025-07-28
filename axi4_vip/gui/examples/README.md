# AMBA Bus Matrix Configuration Tool - Examples

This directory contains example scripts demonstrating various features and use cases of the AMBA Bus Matrix Configuration Tool.

## Example Scripts

### 1. create_simple_system.py
**Purpose**: Basic introduction to the tool's API
- Creates a simple 2 master × 3 slave AXI4 system
- Demonstrates basic master/slave configuration
- Shows how to generate RTL and save configurations
- Good starting point for new users

**Run**: `python3 create_simple_system.py`

### 2. create_mixed_protocol.py
**Purpose**: Advanced hierarchical bus design
- Creates a high-performance AXI4 main bus
- Adds APB peripheral bus via bridge
- Demonstrates protocol conversion
- Shows how to organize complex SoC architectures

**Run**: `python3 create_mixed_protocol.py`

### 3. create_secure_system.py
**Purpose**: Security-aware system design
- Implements ARM TrustZone security features
- Configures secure/non-secure masters
- Sets up access control for slaves
- Demonstrates AxPROT signal usage
- Creates access control matrix

**Run**: `python3 create_secure_system.py`

### 4. batch_generation.py
**Purpose**: Automated generation of multiple variants
- Generates 7 different system configurations
- Varies masters (2-16), slaves (3-8), and data width (32-512 bits)
- Useful for design space exploration
- Includes comparison script generation

**Run**: `python3 batch_generation.py`

### 5. performance_analysis.py
**Purpose**: System performance analysis and optimization
- Calculates theoretical bandwidth for each component
- Analyzes worst-case latency scenarios
- Identifies system bottlenecks
- Provides optimization recommendations
- Generates detailed performance report

**Run**: `python3 performance_analysis.py`

## Common Patterns

### Creating a Basic Configuration
```python
from bus_config import BusConfig, Master, Slave

config = BusConfig()
config.bus_type = "AXI4"
config.data_width = 64
config.addr_width = 32

# Add a master
master = Master("CPU")
master.id_width = 4
master.priority = 1
config.masters.append(master)

# Add a slave
slave = Slave("Memory", base_address=0x0, size=1048576)  # 1GB
slave.memory_type = "Memory"
slave.read_latency = 5
config.slaves.append(slave)
```

### Generating RTL
```python
from axi_verilog_generator import AXIVerilogGenerator

rtl_gen = AXIVerilogGenerator(config)
rtl_gen.output_dir = "output/rtl"
rtl_gen.generate()
```

### Saving Configuration
```python
import json

config_dict = {
    "bus_type": config.bus_type,
    "data_width": config.data_width,
    "masters": [{"name": m.name, "id_width": m.id_width} 
                for m in config.masters],
    "slaves": [{"name": s.name, "base_address": hex(s.base_address)} 
               for s in config.slaves]
}

with open("my_config.json", 'w') as f:
    json.dump(config_dict, f, indent=2)
```

## Output Files

Each example generates different outputs:

- **JSON Configuration Files**: Can be loaded in the GUI
- **RTL Verilog Files**: Synthesizable interconnect modules
- **Analysis Reports**: Performance metrics and recommendations
- **Batch Results**: Comparison data for multiple variants

## Integration with GUI

All generated configurations can be loaded in the GUI:
```bash
../launch_gui.sh --config <generated_config>.json
```

## Tips

1. **Start Simple**: Begin with `create_simple_system.py`
2. **Check Constraints**: Ensure base addresses are aligned
3. **Validate Access**: Use security examples for access control
4. **Analyze Performance**: Run performance analysis before synthesis
5. **Explore Variants**: Use batch generation for design exploration

## Extending Examples

Feel free to modify these examples for your specific needs:
- Change bus parameters (width, arbitration)
- Add custom masters/slaves
- Implement specific address maps
- Create domain-specific configurations

## Questions?

See the main [README.md](../README.md) for complete documentation.