#!/bin/bash
# Patch script to add detailed UVM_INFO logging to generated VIP

echo "=== Applying detailed logging patches to VIP ==="

# Function to add UVM_INFO to master driver BFM
patch_master_driver_bfm() {
    local file="$1/agent/master_agent_bfm/axi4_master_driver_bfm.sv"
    if [ -f "$file" ]; then
        # Add UVM_INFO after reset
        sed -i '/aresetn <= 1.b1;/a\        `uvm_info("AXI_MASTER_DRIVER_BFM", "Master BFM signals initialized", UVM_LOW)\n        `uvm_info("AXI_MASTER_DRIVER_BFM", "Enabling BFM driving for signal visibility", UVM_LOW)' "$file"
        
        # Add transaction generation message
        sed -i '/@(posedge aclk);/a\        `uvm_info("AXI_MASTER_DRIVER_BFM", "Starting AXI transaction generation for waveform visibility", UVM_LOW)' "$file"
        
        echo "✅ Patched master driver BFM"
    fi
}

# Function to add UVM_INFO to slave driver BFM
patch_slave_driver_bfm() {
    local file="$1/agent/slave_agent_bfm/axi4_slave_driver_bfm.sv"
    if [ -f "$file" ]; then
        # Add UVM_INFO after reset
        sed -i '/aresetn <= 1.b1;/a\        `uvm_info("AXI_SLAVE_DRIVER_BFM", "Slave BFM signals initialized", UVM_LOW)' "$file"
        
        echo "✅ Patched slave driver BFM"
    fi
}

# Function to add transaction counting to monitor
patch_monitor() {
    local file="$1/master/axi4_master_monitor.sv"
    if [ -f "$file" ]; then
        # Add counter declaration
        sed -i '/class axi4_master_monitor extends uvm_monitor;/a\    int unsigned trans_count = 0;' "$file"
        
        # Add counting logic
        sed -i '/trans_collected++;/a\            trans_count++;\n            if (trans_count % 100 == 0) begin\n                `uvm_info(get_type_name(), $sformatf("Master Monitor: Collected %0d transactions", trans_count), UVM_MEDIUM)\n            end' "$file"
        
        echo "✅ Patched master monitor"
    fi
}

# Function to add transaction details to driver
patch_driver() {
    local file="$1/master/axi4_master_driver.sv"
    if [ -f "$file" ]; then
        # Add transaction logging
        sed -i '/task drive_item(axi4_master_tx tx);/a\        `uvm_info(get_type_name(), $sformatf("Driving transaction: ADDR=0x%0h, TYPE=%s, SIZE=%0d, LEN=%0d", tx.addr, tx.burst_type.name(), tx.burst_size, tx.burst_length), UVM_HIGH)' "$file"
        
        echo "✅ Patched master driver"
    fi
}

# Function to add throughput analysis to scoreboard
patch_scoreboard() {
    local file="$1/env/axi4_scoreboard.sv"
    if [ -f "$file" ]; then
        # Add throughput reporting
        sed -i '/super.report_phase(phase);/a\        `uvm_info(get_type_name(), "=== Throughput Analysis ===", UVM_LOW)\n        `uvm_info(get_type_name(), $sformatf("Total Write Transactions: %0d", write_count), UVM_LOW)\n        `uvm_info(get_type_name(), $sformatf("Total Read Transactions: %0d", read_count), UVM_LOW)' "$file"
        
        echo "✅ Patched scoreboard"
    fi
}

# Function to update Makefile for verbosity
patch_makefile() {
    local file="$1/sim/Makefile"
    if [ -f "$file" ]; then
        # Add verbosity support
        sed -i 's/+UVM_TESTNAME=$(TEST)/+UVM_TESTNAME=$(TEST) +UVM_VERBOSITY=$(UVM_VERBOSITY)/g' "$file"
        
        # Add default verbosity
        sed -i '/TEST ?= axi4_basic_test/a\UVM_VERBOSITY ?= UVM_MEDIUM' "$file"
        
        echo "✅ Patched Makefile"
    fi
}

# Main patch function
apply_patches() {
    local vip_dir="$1"
    
    if [ ! -d "$vip_dir" ]; then
        echo "❌ Directory not found: $vip_dir"
        return 1
    fi
    
    echo "Applying patches to: $vip_dir"
    
    patch_master_driver_bfm "$vip_dir"
    patch_slave_driver_bfm "$vip_dir"
    patch_monitor "$vip_dir"
    patch_driver "$vip_dir"
    patch_scoreboard "$vip_dir"
    patch_makefile "$vip_dir"
    
    echo "✅ All patches applied successfully!"
}

# Check if directory is provided
if [ $# -eq 0 ]; then
    echo "Usage: $0 <vip_directory>"
    echo "Example: $0 /path/to/16x16_vip/axi4_vip_env_rtl_integration"
    exit 1
fi

apply_patches "$1"
