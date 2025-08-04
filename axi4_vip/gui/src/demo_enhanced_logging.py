#!/usr/bin/env python3
"""
Demo script showing enhanced UVM_INFO logging in generated VIP
This helps users understand how to use the enhanced debugging features
"""

import os
import sys

# Add path to import modules
sys.path.insert(0, os.path.dirname(__file__))

from bus_config import BusConfig, Master, Slave
from vip_environment_generator import VIPEnvironmentGenerator

def demo_enhanced_logging():
    """Demonstrate the enhanced logging features"""
    
    print("AXI4 VIP Enhanced Logging Demo")
    print("=" * 40)
    print("\nThis demo shows the enhanced UVM_INFO logging added to help debug VIP activity.\n")
    
    # Create simple 2x2 configuration for demo
    config = BusConfig()
    config.data_width = 32
    config.addr_width = 32
    config.id_width = 4
    
    # Add 2 masters
    cpu = Master("CPU")
    cpu.qos_support = True
    config.masters.append(cpu)
    
    dma = Master("DMA") 
    dma.qos_support = True
    config.masters.append(dma)
    
    # Add 2 slaves
    config.slaves.append(Slave("Memory", 0x00000000, 1048576))  # 1MB
    config.slaves.append(Slave("Peripheral", 0x10000000, 65536))  # 64KB
    
    # Generate VIP
    gen = VIPEnvironmentGenerator(config, "rtl_integration", "vcs")
    output_path = "./demo_enhanced_logging_vip"
    
    print("Generating VIP with enhanced logging...")
    result = gen.generate_environment(output_path)
    print(f"✓ Generated at: {result}")
    
    # Create example test with logging demonstration
    test_file = os.path.join(result, "test/demo_logging_test.sv")
    with open(test_file, 'w') as f:
        f.write("""//==============================================================================
// Demo Test - Shows Enhanced UVM_INFO Logging
//==============================================================================

class demo_logging_test extends axi4_base_test;
    
    `uvm_component_utils(demo_logging_test)
    
    function new(string name = "demo_logging_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_virtual_write_seq write_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "====================================", UVM_LOW)
        `uvm_info(get_type_name(), "Starting Enhanced Logging Demo Test", UVM_LOW)
        `uvm_info(get_type_name(), "====================================", UVM_LOW)
        
        `uvm_info(get_type_name(), "The following log messages will help you debug:", UVM_LOW)
        `uvm_info(get_type_name(), "1. Agent build/connect phases", UVM_LOW)
        `uvm_info(get_type_name(), "2. Driver transaction details", UVM_LOW)
        `uvm_info(get_type_name(), "3. Monitor activity status", UVM_LOW)
        `uvm_info(get_type_name(), "4. Sequence execution flow", UVM_LOW)
        
        // Run a simple write sequence
        write_seq = axi4_virtual_write_seq::type_id::create("write_seq");
        write_seq.start(env.virtual_seqr);
        
        #1000ns;
        
        `uvm_info(get_type_name(), "Test completed - check log for enhanced debug messages", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : demo_logging_test
""")
    
    # Create run script showing verbosity control
    run_script = os.path.join(result, "sim/run_with_logging.sh")
    os.makedirs(os.path.dirname(run_script), exist_ok=True)
    
    with open(run_script, 'w') as f:
        f.write("""#!/bin/bash
# Demo script showing how to control UVM verbosity for enhanced logging

echo "======================================"
echo "AXI4 VIP Enhanced Logging Demo"
echo "======================================"
echo ""
echo "The VIP now includes comprehensive UVM_INFO logging at three levels:"
echo "  - UVM_LOW    : Key phase transitions and major events"
echo "  - UVM_MEDIUM : Transaction details and important operations"  
echo "  - UVM_HIGH   : Detailed debug information and periodic status"
echo ""
echo "To control verbosity, use the +UVM_VERBOSITY flag:"
echo ""
echo "1. Show only LOW messages (minimal):"
echo "   ./simv +UVM_TESTNAME=demo_logging_test +UVM_VERBOSITY=UVM_LOW"
echo ""
echo "2. Show LOW and MEDIUM messages (recommended for debug):"
echo "   ./simv +UVM_TESTNAME=demo_logging_test +UVM_VERBOSITY=UVM_MEDIUM"
echo ""
echo "3. Show all messages including HIGH (maximum detail):"
echo "   ./simv +UVM_TESTNAME=demo_logging_test +UVM_VERBOSITY=UVM_HIGH"
echo ""
echo "You can also filter by component:"
echo "   ./simv +uvm_set_verbosity=*master_driver*,UVM_HIGH,UVM_HIGH"
echo ""
echo "To correlate with waveforms:"
echo "1. Note the timestamp in UVM_INFO messages"
echo "2. Navigate to that time in your waveform viewer"
echo "3. The enhanced logging helps identify what the VIP is doing"
echo ""
echo "Example enhanced log output:"
echo "-------------------------------------"
echo "UVM_INFO @ 0: reporter [axi4_master_agent] Building master agent components"
echo "UVM_INFO @ 0: reporter [axi4_master_agent] Master agent mode: ACTIVE"
echo "UVM_INFO @ 100: reporter [axi4_master_driver] Starting master driver run_phase"
echo "UVM_INFO @ 200: reporter [axi4_master_driver] Waiting for next transaction"
echo "UVM_INFO @ 300: reporter [axi4_master_driver] Got WRITE transaction - addr=0x1000"
echo "UVM_INFO @ 300: reporter [axi4_master_driver] Transaction details - id=2, qos=0"
echo "UVM_INFO @ 400: reporter [axi4_master_monitor] Monitor active - checking"
echo "-------------------------------------"
""")
    os.chmod(run_script, 0o755)
    
    print(f"\n✓ Created demo test: {test_file}")
    print(f"✓ Created run script: {run_script}")
    
    print("\n" + "=" * 60)
    print("ENHANCED LOGGING FEATURES:")
    print("=" * 60)
    print("\n1. DRIVER LOGGING:")
    print("   - Transaction type (READ/WRITE)")
    print("   - Address, length, size, burst details")
    print("   - QoS, region, cache, protection attributes")
    print("   - Transaction completion status")
    
    print("\n2. AGENT LOGGING:")
    print("   - Component creation in build_phase")
    print("   - Active/passive mode detection")
    print("   - Component connections in connect_phase")
    
    print("\n3. MONITOR LOGGING:")
    print("   - Periodic activity status (every 100ns)")
    print("   - No direct interface access (compilation safe)")
    
    print("\n4. VERBOSITY CONTROL:")
    print("   - UVM_LOW: Major events only")
    print("   - UVM_MEDIUM: + Transaction details")
    print("   - UVM_HIGH: + Periodic status updates")
    
    print("\n5. WAVEFORM CORRELATION:")
    print("   - Match UVM_INFO timestamps with waveform time")
    print("   - Use component names to identify sources")
    print("   - Filter by verbosity to reduce noise")
    
    print("\n" + "=" * 60)
    print("Run the demo script to see enhanced logging in action!")
    print("=" * 60)

if __name__ == "__main__":
    demo_enhanced_logging()