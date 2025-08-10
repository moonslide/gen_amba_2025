#!/bin/bash
# Patch script to add transaction logging to generated VIP

echo "=== Applying transaction logging patches to VIP ==="

# Function to add master driver logging
patch_master_driver() {
    local file="$1/master/axi4_master_pkg.sv"
    if [ -f "$file" ]; then
        # Add transaction logging after get_next_item
        sed -i '/seq_item_port.get_next_item(req);/a\
                \
                // Log transaction details\
                if (req.is_write) begin\
                    `uvm_info(get_type_name(), $sformatf("Got WRITE transaction - addr=0x%08x, len=%0d, size=%0d, burst=%0d",\
                        req.addr, req.burst_length, req.burst_size, req.burst_type), UVM_MEDIUM)\
                end else begin\
                    `uvm_info(get_type_name(), $sformatf("Got READ transaction - addr=0x%08x, len=%0d, size=%0d, burst=%0d",\
                        req.addr, req.burst_length, req.burst_size, req.burst_type), UVM_MEDIUM)\
                end' "$file"
        
        echo "✅ Patched master driver logging"
    fi
}

# Function to add slave BFM logging
patch_slave_bfm() {
    local file="$1/agent/slave_agent_bfm/axi4_slave_driver_bfm.sv"
    if [ -f "$file" ]; then
        # Add read address acceptance logging
        sed -i '/if.*arvalid.*arready/a\
                `uvm_info("AXI_SLAVE_DRIVER_BFM", $sformatf("Read address accepted: id=%0d, addr=0x%08x, len=%0d",\
                    axi_intf.arid, axi_intf.araddr, axi_intf.arlen), UVM_MEDIUM)' "$file"
        
        # Add write address acceptance logging
        sed -i '/if.*awvalid.*awready/a\
                `uvm_info("AXI_SLAVE_DRIVER_BFM", $sformatf("Write address accepted: id=%0d, addr=0x%08x, len=%0d",\
                    axi_intf.awid, axi_intf.awaddr, axi_intf.awlen), UVM_MEDIUM)' "$file"
        
        echo "✅ Patched slave BFM logging"
    fi
}

# Function to add monitor logging
patch_monitor() {
    local file="$1/master/axi4_master_pkg.sv"
    if [ -f "$file" ]; then
        # Add monitor collection logging
        sed -i '/item_collected_port.write(trans_collected);/i\
                `uvm_info(get_type_name(), $sformatf("Monitor collected %s transaction: addr=0x%08x, id=%0d",\
                    trans_collected.is_write ? "WRITE" : "READ", trans_collected.addr, trans_collected.id), UVM_HIGH)' "$file"
        
        echo "✅ Patched monitor logging"
    fi
}

# Function to add scoreboard logging
patch_scoreboard() {
    local file="$1/env/axi4_scoreboard.sv"
    if [ -f "$file" ]; then
        # Add scoreboard receive logging
        sed -i '/function void write_master.*(/a\
        `uvm_info(get_type_name(), $sformatf("Scoreboard received master[%0d] %s transaction: addr=0x%08x",\
            port_idx, trans.is_write ? "WRITE" : "READ", trans.addr), UVM_MEDIUM)' "$file"
        
        echo "✅ Patched scoreboard logging"
    fi
}

# Main patch function
apply_patches() {
    local vip_dir="$1"
    
    if [ ! -d "$vip_dir" ]; then
        echo "❌ Directory not found: $vip_dir"
        return 1
    fi
    
    echo "Applying transaction logging patches to: $vip_dir"
    
    patch_master_driver "$vip_dir"
    patch_slave_bfm "$vip_dir"
    patch_monitor "$vip_dir"
    patch_scoreboard "$vip_dir"
    
    echo "✅ All transaction logging patches applied!"
}

# Check if directory is provided
if [ $# -eq 0 ]; then
    echo "Usage: $0 <vip_directory>"
    echo "Example: $0 /path/to/16x16_vip/axi4_vip_env_rtl_integration"
    exit 1
fi

apply_patches "$1"
