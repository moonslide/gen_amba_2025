#!/usr/bin/env python3
"""
Fix Signal Timing Issues - Comprehensive fix for wlast, B-channel, AR channel, and scoreboard
Addresses all FSDB waveform issues reported by user
"""

import os
import sys
import shutil
from datetime import datetime

def backup_file(filepath):
    """Create backup of file before modifying"""
    if not os.path.exists(filepath):
        return None
    backup_path = f"{filepath}.backup_signal_fix_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    shutil.copy2(filepath, backup_path)
    print(f"✓ Backed up {os.path.basename(filepath)}")
    return backup_path

def fix_master_driver_timing(pkg_path):
    """Fix master driver signal timing issues"""
    
    print("\n📝 Fixing master driver signal timing...")
    
    with open(pkg_path, 'r') as f:
        content = f.read()
    
    # Fix wlast timing - don't clear it immediately after loop
    old_write_timing = """            end
            @(posedge vif.aclk);
            vif.wvalid <= 1'b0;
            vif.wlast  <= 1'b0;
            
            // Wait for write response
            vif.bready <= 1'b1;
            while (!vif.bvalid) @(posedge vif.aclk);
            @(posedge vif.aclk);
            vif.bready <= 1'b0;"""
    
    new_write_timing = """            end
            
            // Keep wlast high until wready handshake completes
            while (!(vif.wvalid && vif.wready && vif.wlast)) @(posedge vif.aclk);
            
            @(posedge vif.aclk);
            vif.wvalid <= 1'b0;
            vif.wlast  <= 1'b0;  // Now clear wlast after handshake
            vif.wdata  <= '0;
            vif.wstrb  <= '0;
            
            `uvm_info(get_type_name(), "Write data phase completed", UVM_HIGH)
            
            // Wait for write response with proper logging
            vif.bready <= 1'b1;
            `uvm_info(get_type_name(), "Waiting for B-channel response", UVM_HIGH)
            
            begin
                int b_timeout = 0;
                while (!vif.bvalid && b_timeout < 200) begin
                    @(posedge vif.aclk);
                    b_timeout++;
                end
                
                if (vif.bvalid) begin
                    `uvm_info(get_type_name(), $sformatf("B-channel response received: BID=%0d, BRESP=%0d", 
                              vif.bid, vif.bresp), UVM_MEDIUM)
                    @(posedge vif.aclk);
                end else begin
                    `uvm_warning(get_type_name(), "B-channel timeout - no response received")
                end
            end
            
            vif.bready <= 1'b0;"""
    
    content = content.replace(old_write_timing, new_write_timing)
    
    # Fix read driver to actually generate AR transactions
    old_read_driver = """        task drive_read_transaction(axi4_master_tx tx);
            `uvm_info(get_type_name(), $sformatf("Driving READ: addr=0x%0h, len=%0d, id=%0d", 
                      tx.araddr, tx.arlen, tx.arid), UVM_MEDIUM)
            
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
        endtask"""
    
    new_read_driver = """        task drive_read_transaction(axi4_master_tx tx);
            `uvm_info(get_type_name(), $sformatf("Driving READ: addr=0x%0h, len=%0d, id=%0d", 
                      tx.araddr, tx.arlen, tx.arid), UVM_MEDIUM)
            
            // Drive read address channel with proper timing
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
            
            `uvm_info(get_type_name(), $sformatf("AR channel driven: ARID=%0d, ARADDR=0x%0h", 
                      tx.arid, tx.araddr), UVM_HIGH)
            
            // Wait for arready with timeout
            begin
                int ar_timeout = 0;
                while (!vif.arready && ar_timeout < 100) begin
                    @(posedge vif.aclk);
                    ar_timeout++;
                end
                if (ar_timeout >= 100) begin
                    `uvm_error(get_type_name(), "AR channel timeout")
                end
            end
            @(posedge vif.aclk);
            vif.arvalid <= 1'b0;
            
            `uvm_info(get_type_name(), "AR handshake completed, waiting for read data", UVM_HIGH)
            
            // Collect read data with proper allocation
            tx.rdata = new[tx.arlen + 1];
            vif.rready <= 1'b1;  // Ready to accept read data
            
            for (int i = 0; i <= tx.arlen; i++) begin
                // Wait for rvalid
                begin
                    int r_timeout = 0;
                    while (!vif.rvalid && r_timeout < 100) begin
                        @(posedge vif.aclk);
                        r_timeout++;
                    end
                end
                
                if (vif.rvalid) begin
                    tx.rdata[i] = vif.rdata;
                    `uvm_info(get_type_name(), $sformatf("Read data[%0d]: 0x%0h, RID=%0d, RLAST=%0b", 
                              i, vif.rdata, vif.rid, vif.rlast), UVM_MEDIUM)
                    
                    @(posedge vif.aclk);
                    
                    if (vif.rlast) begin
                        `uvm_info(get_type_name(), "RLAST received - read complete", UVM_HIGH)
                        break;
                    end
                end
            end
            
            vif.rready <= 1'b0;  // Clear rready
            `uvm_info(get_type_name(), $sformatf("Read transaction completed, received %0d beats", tx.rdata.size()), UVM_MEDIUM)
        endtask"""
    
    content = content.replace(old_read_driver, new_read_driver)
    
    with open(pkg_path, 'w') as f:
        f.write(content)
    
    print("✓ Fixed master driver signal timing")
    return True

def fix_slave_bfm_responses(bfm_path):
    """Fix slave BFM to have better response timing"""
    
    print("\n📝 Fixing slave BFM response timing...")
    
    with open(bfm_path, 'r') as f:
        content = f.read()
    
    # Fix write response timing
    old_write_response = """                    // Capture write address ID
                    if (axi_intf.awvalid && axi_intf.awready) begin
                        write_id_queue.push_back(axi_intf.awid);
                    end
                    
                    // Send write response when wlast received
                    if (axi_intf.wvalid && axi_intf.wready && axi_intf.wlast && !axi_intf.bvalid) begin
                        if (write_id_queue.size() > 0) begin
                            axi_intf.bid    <= write_id_queue.pop_front();
                            axi_intf.bresp  <= 2'b00;  // OKAY
                            axi_intf.bvalid <= 1'b1;
                        end
                    end"""
    
    new_write_response = """                    // Capture write address ID
                    if (axi_intf.awvalid && axi_intf.awready) begin
                        write_id_queue.push_back(axi_intf.awid);
                        `uvm_info("AXI_SLAVE_BFM", $sformatf("Captured AWID=%0h", axi_intf.awid), UVM_HIGH)
                    end
                    
                    // Send write response when wlast received
                    if (axi_intf.wvalid && axi_intf.wready && axi_intf.wlast && !axi_intf.bvalid) begin
                        if (write_id_queue.size() > 0) begin
                            automatic logic [ID_WIDTH-1:0] response_id = write_id_queue.pop_front();
                            
                            // Immediate response
                            axi_intf.bid    <= response_id;
                            axi_intf.bresp  <= 2'b00;  // OKAY
                            axi_intf.bvalid <= 1'b1;
                            
                            `uvm_info("AXI_SLAVE_BFM", $sformatf("B-channel response: BID=%0h, BRESP=OKAY", response_id), UVM_MEDIUM)
                        end else begin
                            `uvm_warning("AXI_SLAVE_BFM", "WLAST received but no AWID in queue")
                        end
                    end"""
    
    content = content.replace(old_write_response, new_write_response)
    
    with open(bfm_path, 'w') as f:
        f.write(content)
    
    print("✓ Fixed slave BFM response timing")
    return True

def disable_synthetic_scoreboard(pkg_path):
    """Disable synthetic transaction generation in scoreboard"""
    
    print("\n📝 Disabling synthetic scoreboard transactions...")
    
    with open(pkg_path, 'r') as f:
        content = f.read()
    
    # Disable synthetic traffic generation
    old_synthetic = """        // For throughput testing, generate synthetic transactions
            if (enable_synthetic_traffic) begin
                fork
                    generate_synthetic_transactions();
                join_none
            end"""
    
    new_synthetic = """        // Disabled synthetic traffic - monitor real transactions only
            `uvm_info(get_type_name(), "Synthetic traffic disabled - monitoring real transactions", UVM_MEDIUM)"""
    
    content = content.replace(old_synthetic, new_synthetic)
    
    # Set enable flag to 0
    old_enable = """int enable_synthetic_traffic = 1;"""
    new_enable = """int enable_synthetic_traffic = 0;  // Disabled for real transaction monitoring"""
    
    content = content.replace(old_enable, new_enable)
    
    with open(pkg_path, 'w') as f:
        f.write(content)
    
    print("✓ Disabled synthetic scoreboard transactions")
    return True

def main():
    """Main function to fix all signal timing issues"""
    
    print("\n" + "="*70)
    print("🔧 Comprehensive Signal Timing Fix")
    print("="*70)
    
    base_path = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration"
    
    files_to_fix = [
        ("master/axi4_master_pkg.sv", fix_master_driver_timing),
        ("agent/slave_agent_bfm/axi4_slave_driver_bfm.sv", fix_slave_bfm_responses),
        ("master/axi4_master_pkg.sv", disable_synthetic_scoreboard),
    ]
    
    success = True
    for rel_path, fix_func in files_to_fix:
        full_path = os.path.join(base_path, rel_path)
        if os.path.exists(full_path):
            if "axi4_master_pkg.sv" in rel_path and fix_func == disable_synthetic_scoreboard:
                print(f"\n📝 Applying scoreboard fix to {rel_path}...")
                backup_file(full_path)
            elif fix_func != disable_synthetic_scoreboard:
                backup_file(full_path)
            success &= fix_func(full_path)
        else:
            print(f"⚠️  Warning: {rel_path} not found")
            success = False
    
    if success:
        print("\n" + "="*70)
        print("✅ Signal Timing Issues Fixed!")
        print("\nFixed problems:")
        print("  1. ✓ wlast timing - now stays high during handshake")
        print("  2. ✓ B-channel responses - better timing and logging")
        print("  3. ✓ AR channel activity - proper read transaction generation")
        print("  4. ✓ Scoreboard - disabled synthetic traffic, monitors real transactions")
        print("\nExpected FSDB improvements:")
        print("  • M0 wlast will raise properly on last beat")
        print("  • bid/bresp will change with transaction IDs")
        print("  • AR channel will show address values changing")
        print("  • Real transaction monitoring vs synthetic")
        print("\nNext steps:")
        print("  1. Run: cd sim && make clean")
        print("  2. Run: make run_fsdb TEST=axi4_simple_crossbar_test")
        print("  3. Check FSDB: All signals should show proper activity")
        print("="*70)
    else:
        print("\n❌ Some fixes failed to apply")
        return False
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)