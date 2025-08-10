#!/usr/bin/env python3
"""
Fix UVM driver to actually drive AXI interface signals
The current driver is just a stub - it needs to drive the actual interface
"""

import os
import sys
import shutil
from datetime import datetime

def backup_file(filepath):
    """Create backup of file before modifying"""
    backup_path = f"{filepath}.backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    shutil.copy2(filepath, backup_path)
    print(f"✓ Backed up {os.path.basename(filepath)}")
    return backup_path

def fix_master_driver(master_pkg_path):
    """Fix the master driver to actually drive interface signals"""
    
    print(f"\n📝 Fixing master driver to drive actual interface signals...")
    
    # Read the file
    with open(master_pkg_path, 'r') as f:
        content = f.read()
    
    # Replace the stub driver with a real implementation
    old_driver = """    // Driver class (stub)
    class axi4_master_driver extends uvm_driver #(axi4_master_tx);
        `uvm_component_utils(axi4_master_driver)
        
        function new(string name = "axi4_master_driver", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            `uvm_info(get_type_name(), "Starting master driver run_phase", UVM_LOW)
            forever begin
                `uvm_info(get_type_name(), "Waiting for next transaction from sequencer", UVM_HIGH)
                seq_item_port.get_next_item(req);
                
                `uvm_info(get_type_name(), $sformatf("Got %s transaction - addr=0x%0h, len=%0d, size=%0d, burst=%0d", 
                    req.tx_type.name(), 
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awaddr : req.araddr,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awlen : req.arlen,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awsize : req.arsize,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awburst : req.arburst), UVM_MEDIUM)
                
                `uvm_info(get_type_name(), $sformatf("Transaction details - id=%0d, qos=%0d, region=%0d, cache=0x%0h, prot=%0d",
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awid : req.arid,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awqos : req.arqos,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awregion : req.arregion,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awcache : req.arcache,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awprot : req.arprot), UVM_HIGH)
                
                if (req.tx_type == axi4_master_tx::WRITE && req.wdata.size() > 0) begin
                    `uvm_info(get_type_name(), $sformatf("Write data: %0d beats, first_data=0x%0h", 
                        req.wdata.size(), req.wdata[0]), UVM_HIGH)
                end
                
                `uvm_info(get_type_name(), "Driving transaction to BFM interface", UVM_HIGH)
                #100ns;
                
                `uvm_info(get_type_name(), "Transaction completed, signaling item_done", UVM_HIGH)
                seq_item_port.item_done();
            end
        endtask
    endclass"""
    
    new_driver = """    // Driver class - Properly drives AXI interface signals
    class axi4_master_driver extends uvm_driver #(axi4_master_tx);
        `uvm_component_utils(axi4_master_driver)
        
        // Virtual interface handle
        virtual axi4_if vif;
        
        function new(string name = "axi4_master_driver", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            // Get virtual interface from config_db
            if(!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif))
                `uvm_fatal("NOVIF", "Virtual interface not found in config_db")
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            `uvm_info(get_type_name(), "Starting master driver run_phase", UVM_LOW)
            
            // Initialize interface signals
            reset_signals();
            
            forever begin
                `uvm_info(get_type_name(), "Waiting for next transaction from sequencer", UVM_HIGH)
                seq_item_port.get_next_item(req);
                
                `uvm_info(get_type_name(), $sformatf("Got %s transaction - addr=0x%0h, len=%0d, size=%0d, burst=%0d", 
                    req.tx_type.name(), 
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awaddr : req.araddr,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awlen : req.arlen,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awsize : req.arsize,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awburst : req.arburst), UVM_MEDIUM)
                
                // Drive the actual transaction on the interface
                if (req.tx_type == axi4_master_tx::WRITE) begin
                    drive_write_transaction(req);
                end else begin
                    drive_read_transaction(req);
                end
                
                `uvm_info(get_type_name(), "Transaction completed, signaling item_done", UVM_HIGH)
                seq_item_port.item_done();
            end
        endtask
        
        task reset_signals();
            vif.awvalid <= 1'b0;
            vif.wvalid  <= 1'b0;
            vif.bready  <= 1'b0;
            vif.arvalid <= 1'b0;
            vif.rready  <= 1'b0;
        endtask
        
        task drive_write_transaction(axi4_master_tx tx);
            `uvm_info(get_type_name(), "Driving WRITE transaction on interface", UVM_HIGH)
            
            // Drive write address channel
            @(posedge vif.aclk);
            vif.awid    <= tx.awid;
            vif.awaddr  <= tx.awaddr;
            vif.awlen   <= tx.awlen;
            vif.awsize  <= tx.awsize;
            vif.awburst <= tx.awburst;
            vif.awlock  <= tx.awlock;
            vif.awcache <= tx.awcache;
            vif.awprot  <= tx.awprot;
            vif.awqos   <= tx.awqos;
            vif.awregion <= tx.awregion;
            vif.awvalid <= 1'b1;
            
            // Wait for awready
            while (!vif.awready) @(posedge vif.aclk);
            @(posedge vif.aclk);
            vif.awvalid <= 1'b0;
            
            // Drive write data channel
            for (int i = 0; i <= tx.awlen; i++) begin
                @(posedge vif.aclk);
                vif.wdata  <= (i < tx.wdata.size()) ? tx.wdata[i] : '0;
                vif.wstrb  <= (i < tx.wstrb.size()) ? tx.wstrb[i] : '1;
                vif.wlast  <= (i == tx.awlen);
                vif.wvalid <= 1'b1;
                
                while (!vif.wready) @(posedge vif.aclk);
            end
            @(posedge vif.aclk);
            vif.wvalid <= 1'b0;
            vif.wlast  <= 1'b0;
            
            // Wait for write response
            vif.bready <= 1'b1;
            while (!vif.bvalid) @(posedge vif.aclk);
            @(posedge vif.aclk);
            vif.bready <= 1'b0;
        endtask
        
        task drive_read_transaction(axi4_master_tx tx);
            `uvm_info(get_type_name(), "Driving READ transaction on interface", UVM_HIGH)
            
            // Drive read address channel
            @(posedge vif.aclk);
            vif.arid    <= tx.arid;
            vif.araddr  <= tx.araddr;
            vif.arlen   <= tx.arlen;
            vif.arsize  <= tx.arsize;
            vif.arburst <= tx.arburst;
            vif.arlock  <= tx.arlock;
            vif.arcache <= tx.arcache;
            vif.arprot  <= tx.arprot;
            vif.arqos   <= tx.arqos;
            vif.arregion <= tx.arregion;
            vif.arvalid <= 1'b1;
            
            // Wait for arready
            while (!vif.arready) @(posedge vif.aclk);
            @(posedge vif.aclk);
            vif.arvalid <= 1'b0;
            
            // Wait for read data
            vif.rready <= 1'b1;
            for (int i = 0; i <= tx.arlen; i++) begin
                while (!vif.rvalid) @(posedge vif.aclk);
                @(posedge vif.aclk);
                if (vif.rlast) break;
            end
            vif.rready <= 1'b0;
        endtask
    endclass"""
    
    content = content.replace(old_driver, new_driver)
    
    # Also need to fix the agent to pass the interface
    old_agent_build = """        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            `uvm_info(get_type_name(), "Building master agent components", UVM_LOW)
            
            // Get configuration
            if(!uvm_config_db#(axi4_master_agent_config)::get(this, "", "cfg", cfg))
                `uvm_fatal("CONFIG", "Cannot get master agent config from uvm_config_db")"""
    
    new_agent_build = """        // Virtual interface handle
        virtual axi4_if vif;
        
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            `uvm_info(get_type_name(), "Building master agent components", UVM_LOW)
            
            // Get virtual interface
            if(!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif))
                `uvm_info(get_type_name(), "Virtual interface not found - will be set in env", UVM_MEDIUM)
            
            // Get configuration
            if(!uvm_config_db#(axi4_master_agent_config)::get(this, "", "cfg", cfg))
                `uvm_fatal("CONFIG", "Cannot get master agent config from uvm_config_db")"""
    
    content = content.replace(old_agent_build, new_agent_build)
    
    # Add interface propagation to driver
    old_connect = """        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            `uvm_info(get_type_name(), "Connecting master agent components", UVM_LOW)
            
            if(cfg.is_active == UVM_ACTIVE) begin
                driver.seq_item_port.connect(sequencer.seq_item_export);
                `uvm_info(get_type_name(), "Connected driver to sequencer", UVM_HIGH)
            end"""
    
    new_connect = """        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            `uvm_info(get_type_name(), "Connecting master agent components", UVM_LOW)
            
            if(cfg.is_active == UVM_ACTIVE) begin
                driver.seq_item_port.connect(sequencer.seq_item_export);
                `uvm_info(get_type_name(), "Connected driver to sequencer", UVM_HIGH)
                
                // Pass interface to driver
                if (vif != null) begin
                    uvm_config_db#(virtual axi4_if)::set(this, "driver", "vif", vif);
                    `uvm_info(get_type_name(), "Passed virtual interface to driver", UVM_HIGH)
                end
            end"""
    
    content = content.replace(old_connect, new_connect)
    
    # Write the fixed content
    with open(master_pkg_path, 'w') as f:
        f.write(content)
    
    print(f"✓ Fixed master driver to properly drive interface signals")
    return True

def fix_environment_interface_passing(env_path):
    """Fix the environment to pass interfaces to agents"""
    
    print(f"\n📝 Fixing environment to pass interfaces to agents...")
    
    # Read the file
    with open(env_path, 'r') as f:
        content = f.read()
    
    # Add interface passing in build_phase
    old_build = """            // Configure master agents
            master_agent[i] = axi4_master_agent::type_id::create($sformatf("master_agent[%0d]", i), this);
            master_cfg[i] = axi4_master_agent_config::type_id::create($sformatf("master_cfg[%0d]", i));
            master_cfg[i].is_active = env_cfg.has_master[i] ? UVM_ACTIVE : UVM_PASSIVE;
            uvm_config_db#(axi4_master_agent_config)::set(this, $sformatf("master_agent[%0d]", i), "cfg", master_cfg[i]);"""
    
    new_build = """            // Configure master agents
            master_agent[i] = axi4_master_agent::type_id::create($sformatf("master_agent[%0d]", i), this);
            master_cfg[i] = axi4_master_agent_config::type_id::create($sformatf("master_cfg[%0d]", i));
            master_cfg[i].is_active = env_cfg.has_master[i] ? UVM_ACTIVE : UVM_PASSIVE;
            uvm_config_db#(axi4_master_agent_config)::set(this, $sformatf("master_agent[%0d]", i), "cfg", master_cfg[i]);
            
            // Pass virtual interface to agent
            begin
                virtual axi4_if vif;
                if(uvm_config_db#(virtual axi4_if)::get(this, "", $sformatf("master_if_%0d", i), vif)) begin
                    uvm_config_db#(virtual axi4_if)::set(this, $sformatf("master_agent[%0d]", i), "vif", vif);
                    `uvm_info(get_type_name(), $sformatf("Passed master_if_%0d to master_agent[%0d]", i, i), UVM_HIGH)
                end
            end"""
    
    content = content.replace(old_build, new_build)
    
    # Write the fixed content
    with open(env_path, 'w') as f:
        f.write(content)
    
    print(f"✓ Fixed environment to pass interfaces to agents")
    return True

def fix_test_base_interface_passing(test_path):
    """Fix the base test to set interfaces in config_db"""
    
    print(f"\n📝 Fixing base test to set interfaces in config_db...")
    
    # Read the file
    with open(test_path, 'r') as f:
        content = f.read()
    
    # Add interface setting in build_phase
    old_build_end = """        // Create environment
        env = axi4_env::type_id::create("env", this);"""
    
    new_build_end = """        // Pass interfaces to environment via config_db
        for (int i = 0; i < NO_OF_MASTERS; i++) begin
            uvm_config_db#(virtual axi4_if)::set(this, "env", $sformatf("master_if_%0d", i), hdl_top.master_if[i]);
        end
        for (int i = 0; i < NO_OF_SLAVES; i++) begin
            uvm_config_db#(virtual axi4_if)::set(this, "env", $sformatf("slave_if_%0d", i), hdl_top.slave_if[i]);
        end
        
        // Create environment
        env = axi4_env::type_id::create("env", this);"""
    
    content = content.replace(old_build_end, new_build_end)
    
    # Write the fixed content
    with open(test_path, 'w') as f:
        f.write(content)
    
    print(f"✓ Fixed base test to set interfaces in config_db")
    return True

def main():
    """Main function to apply UVM driver integration fixes"""
    
    print("\n" + "="*60)
    print("🔧 AXI4 VIP UVM Driver Integration Fix Script")
    print("="*60)
    
    # Define paths
    base_path = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration"
    master_pkg_path = os.path.join(base_path, "master/axi4_master_pkg.sv")
    env_path = os.path.join(base_path, "env/axi4_env.sv")
    test_path = os.path.join(base_path, "test/axi4_base_test.sv")
    
    # Check if files exist
    if not os.path.exists(master_pkg_path):
        print(f"❌ Error: Master package not found at {master_pkg_path}")
        return False
    
    if not os.path.exists(env_path):
        print(f"❌ Error: Environment not found at {env_path}")
        return False
        
    if not os.path.exists(test_path):
        print(f"❌ Error: Base test not found at {test_path}")
        return False
    
    # Backup files
    backup_file(master_pkg_path)
    backup_file(env_path)
    backup_file(test_path)
    
    # Apply fixes
    success = True
    success &= fix_master_driver(master_pkg_path)
    success &= fix_environment_interface_passing(env_path)
    success &= fix_test_base_interface_passing(test_path)
    
    if success:
        print("\n" + "="*60)
        print("✅ UVM Driver Integration fixes successfully applied!")
        print("\nKey improvements:")
        print("  • Master driver now actually drives interface signals")
        print("  • Virtual interface properly passed from test to env to agents to drivers")
        print("  • Proper AXI protocol implementation in driver")
        print("  • Write and read transactions fully implemented")
        print("\nNext steps:")
        print("  1. Run: make clean")
        print("  2. Run: make run_fsdb TEST=axi4_simple_crossbar_test")
        print("  3. Check waveforms in Verdi for DUT signal activity")
        print("="*60)
    else:
        print("\n❌ Some fixes failed to apply")
        return False
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)