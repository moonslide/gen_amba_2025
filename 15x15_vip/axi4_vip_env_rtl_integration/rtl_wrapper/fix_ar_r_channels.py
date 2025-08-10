#!/usr/bin/env python3
"""
Fix AR and R channel implementation issues in AXI4 VIP
- AR channel values not changing
- R channel signals showing unknown values
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

def fix_slave_driver_ar_r_channels(slave_driver_path):
    """Fix AR and R channel implementation in slave driver BFM"""
    
    print(f"\n📝 Fixing AR and R channels in slave driver BFM...")
    
    # Read the file
    with open(slave_driver_path, 'r') as f:
        content = f.read()
    
    # Find and replace the read channel implementation
    # Add transaction queue for read operations
    queue_definition = """    // Read transaction coordination - using a proper transaction queue
    typedef struct {
        logic [ID_WIDTH-1:0] arid;
        logic [ADDR_WIDTH-1:0] araddr;
        logic [7:0] arlen;
        logic [2:0] arsize;
        logic [1:0] arburst;
        logic addr_received;
        logic data_sent;
    } read_transaction_t;
    
    read_transaction_t read_trans_queue[$];  // Transaction queue
    """
    
    # Replace the global variables section for read
    old_read_vars = """    // Read Address Channel Handler
    logic read_addr_pending = 0;
    logic [ID_WIDTH-1:0] pending_arid = '0;  // Initialize to prevent 'z' values
    logic [ADDR_WIDTH-1:0] pending_araddr;
    logic [7:0] pending_arlen;
    logic [2:0] pending_arsize;
    logic [1:0] pending_arburst;"""
    
    content = content.replace(old_read_vars, queue_definition)
    
    # Replace read address handler
    new_read_addr_handler = """    // Read Address Channel Handler
    task automatic handle_read_address_channel();
        read_transaction_t new_trans;
        forever begin
            axi_intf.arready <= 1'b0;
            
            // Random delay before accepting
            repeat($urandom_range(0, ar_response_delay)) @(posedge aclk);
            axi_intf.arready <= 1'b1;
            
            // Wait for valid address and ready handshake
            while (!(axi_intf.arvalid && axi_intf.arready)) @(posedge aclk);
            
            // Capture address information during the handshake (signals are stable)
            new_trans.arid = axi_intf.arid;
            new_trans.araddr = axi_intf.araddr;
            new_trans.arlen = axi_intf.arlen;
            new_trans.arsize = axi_intf.arsize;
            new_trans.arburst = axi_intf.arburst;
            new_trans.addr_received = 1'b1;
            new_trans.data_sent = 1'b0;
            
            // Add to transaction queue
            read_trans_queue.push_back(new_trans);
            
            `uvm_info("AXI_SLAVE_DRIVER_BFM", $sformatf("Read address accepted: id=%0d, addr=0x%010x, len=%0d", 
                      new_trans.arid, new_trans.araddr, new_trans.arlen), UVM_MEDIUM)
            
            @(posedge aclk);
            axi_intf.arready <= 1'b0;
        end
    endtask"""
    
    # Find and replace the read address handler
    import re
    pattern = r'task automatic handle_read_address_channel\(\);.*?endtask'
    match = re.search(pattern, content, re.DOTALL)
    if match:
        content = content[:match.start()] + new_read_addr_handler + content[match.end():]
    
    # Replace read data handler
    new_read_data_handler = """    // Read Data Channel Handler
    task automatic handle_read_data_channel();
        int read_beat_count;
        logic [ADDR_WIDTH-1:0] beat_addr;
        logic [DATA_WIDTH-1:0] read_data;
        read_transaction_t current_trans;
        
        forever begin
            // Initialize signals to prevent unknown values
            axi_intf.rvalid <= 1'b0;
            axi_intf.rid <= '0;
            axi_intf.rdata <= '0;
            axi_intf.rresp <= 2'b00;
            axi_intf.rlast <= 1'b0;
            
            // Wait for a transaction with address received but data not sent
            while (read_trans_queue.size() == 0 || 
                   !read_trans_queue[0].addr_received || 
                   read_trans_queue[0].data_sent) @(posedge aclk);
            
            // Get the transaction to process
            current_trans = read_trans_queue[0];
            
            `uvm_info("AXI_SLAVE_DRIVER_BFM", $sformatf("Starting R-channel response for id=%0d", current_trans.arid), UVM_HIGH)
            
            // Send read data beats
            for (read_beat_count = 0; read_beat_count <= current_trans.arlen; read_beat_count++) begin
                // Calculate beat address
                beat_addr = current_trans.araddr + (read_beat_count * (DATA_WIDTH/8));
                
                // Get data from memory (or generate if not written)
                if (memory.exists(beat_addr)) begin
                    read_data = memory[beat_addr];
                end else begin
                    // Initialize with pattern instead of random to avoid X propagation
                    read_data = {DATA_WIDTH{1'b0}} | beat_addr;  // Use address as data pattern
                end
                
                // Random delay before data
                repeat($urandom_range(0, r_response_delay)) @(posedge aclk);
                
                // Send read data with proper initialization
                axi_intf.rid <= current_trans.arid;
                axi_intf.rdata <= read_data;
                axi_intf.rresp <= 2'b00;  // OKAY response
                axi_intf.rlast <= (read_beat_count == current_trans.arlen);
                axi_intf.rvalid <= 1'b1;
                
                `uvm_info("AXI_SLAVE_DRIVER_BFM", $sformatf("Read data beat %0d sent: id=%0d, addr=0x%010x, data=0x%016x, last=%0b", 
                          read_beat_count, current_trans.arid, beat_addr, read_data, axi_intf.rlast), UVM_HIGH)
                
                // Wait for rready with timeout
                begin
                    int r_timeout = 0;
                    while (!axi_intf.rready) begin
                        @(posedge aclk);
                        r_timeout++;
                        if (r_timeout > 1000) begin
                            `uvm_error("AXI_SLAVE_DRIVER_BFM", $sformatf("R-channel handshake timeout for id=%0d", current_trans.arid))
                            break;
                        end
                    end
                end
                
                @(posedge aclk);
                axi_intf.rvalid <= 1'b0;
                axi_intf.rlast <= 1'b0;
            end
            
            // Remove completed transaction from queue
            read_trans_queue.pop_front();
            
            `uvm_info("AXI_SLAVE_DRIVER_BFM", $sformatf("Read transaction completed for id=%0d", current_trans.arid), UVM_MEDIUM)
        end
    endtask"""
    
    # Find and replace the read data handler
    pattern = r'// Read Data Channel Handler.*?endtask'
    match = re.search(pattern, content, re.DOTALL)
    if match:
        content = content[:match.start()] + new_read_data_handler + content[match.end():]
    
    # Also need to fix the parallel task execution for read channels
    old_read_tasks = """    task automatic handle_read_transactions();
        `uvm_info("AXI_SLAVE_DRIVER_BFM", "Starting read transaction handling", UVM_LOW)
        
        forever begin
            fork
                handle_read_address_channel();
                handle_read_data_channel();
            join_none
            @(posedge aclk);
        end
    endtask"""
    
    new_read_tasks = """    task automatic handle_read_transactions();
        `uvm_info("AXI_SLAVE_DRIVER_BFM", "Starting read transaction handling", UVM_LOW)
        
        fork
            handle_read_address_channel();
            handle_read_data_channel();
        join_none
    endtask"""
    
    content = content.replace(old_read_tasks, new_read_tasks)
    
    # Write the fixed content
    with open(slave_driver_path, 'w') as f:
        f.write(content)
    
    print(f"✓ Fixed AR and R channel implementation in slave driver")
    return True

def fix_master_driver_ar_r_channels(master_driver_path):
    """Fix AR and R channel implementation in master driver BFM"""
    
    print(f"\n📝 Fixing AR and R channels in master driver BFM...")
    
    # Read the file
    with open(master_driver_path, 'r') as f:
        content = f.read()
    
    # Fix the read data phase to ensure signals are properly handled
    # Find and improve the read transaction
    import re
    
    # Add better initialization and handshaking for read data phase
    old_read_data = """        // Read Data Phase
        axi_intf.rready <= 1'b1;
        beat_count = 0;
        
        while (beat_count <= len) begin
            while (!axi_intf.rvalid) @(posedge aclk);
            
            `uvm_info("AXI_MASTER_DRIVER_BFM", $sformatf("Read data beat %0d received for transaction %0d, data=0x%016x, rresp=%0d", 
                      beat_count, trans_id, axi_intf.rdata, axi_intf.rresp), UVM_HIGH)
            
            @(posedge aclk);
            beat_count++;
            
            if (axi_intf.rlast) break;
        end
        
        axi_intf.rready <= 1'b0;"""
    
    new_read_data = """        // Read Data Phase - Enhanced R-channel handling
        axi_intf.rready <= 1'b1;
        beat_count = 0;
        
        `uvm_info("AXI_MASTER_DRIVER_BFM", $sformatf("Starting R-channel data phase for transaction %0d, expecting %0d beats", 
                  trans_id, len + 1), UVM_HIGH)
        
        while (beat_count <= len) begin
            // Wait for rvalid with timeout
            begin
                int r_timeout = 0;
                while (!axi_intf.rvalid) begin
                    @(posedge aclk);
                    r_timeout++;
                    if (r_timeout > 1000) begin
                        `uvm_error("AXI_MASTER_DRIVER_BFM", $sformatf("R-channel timeout for transaction %0d, beat %0d", trans_id, beat_count))
                        break;
                    end
                end
            end
            
            if (axi_intf.rvalid) begin
                // Check RID matches expected ARID
                if (axi_intf.rid !== id) begin
                    `uvm_warning("AXI_MASTER_DRIVER_BFM", $sformatf("RID mismatch for transaction %0d: expected=%0d, received=%0d", 
                                trans_id, id, axi_intf.rid))
                end
                
                // Check RRESP
                case (axi_intf.rresp)
                    2'b00: `uvm_info("AXI_MASTER_DRIVER_BFM", $sformatf("R-channel OKAY response for transaction %0d, beat %0d", trans_id, beat_count), UVM_HIGH)
                    2'b01: `uvm_info("AXI_MASTER_DRIVER_BFM", $sformatf("R-channel EXOKAY response for transaction %0d, beat %0d", trans_id, beat_count), UVM_HIGH)
                    2'b10: `uvm_warning("AXI_MASTER_DRIVER_BFM", $sformatf("R-channel SLVERR response for transaction %0d, beat %0d", trans_id, beat_count))
                    2'b11: `uvm_error("AXI_MASTER_DRIVER_BFM", $sformatf("R-channel DECERR response for transaction %0d, beat %0d", trans_id, beat_count))
                endcase
                
                `uvm_info("AXI_MASTER_DRIVER_BFM", $sformatf("Read data beat %0d received: trans=%0d, rid=%0d, data=0x%016x, rresp=%0b, rlast=%0b", 
                          beat_count, trans_id, axi_intf.rid, axi_intf.rdata, axi_intf.rresp, axi_intf.rlast), UVM_MEDIUM)
                
                @(posedge aclk);
                beat_count++;
                
                if (axi_intf.rlast) begin
                    if (beat_count - 1 != len) begin
                        `uvm_warning("AXI_MASTER_DRIVER_BFM", $sformatf("RLAST asserted early: expected at beat %0d, got at %0d", len, beat_count - 1))
                    end
                    break;
                end
            end
        end
        
        @(posedge aclk);
        axi_intf.rready <= 1'b0;"""
    
    content = content.replace(old_read_data, new_read_data)
    
    # Write the fixed content
    with open(master_driver_path, 'w') as f:
        f.write(content)
    
    print(f"✓ Fixed AR and R channel implementation in master driver")
    return True

def main():
    """Main function to apply AR and R channel fixes"""
    
    print("\n" + "="*60)
    print("🔧 AXI4 VIP AR and R Channel Fix Script")
    print("="*60)
    
    # Define paths
    base_path = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration"
    slave_driver_path = os.path.join(base_path, "agent/slave_agent_bfm/axi4_slave_driver_bfm.sv")
    master_driver_path = os.path.join(base_path, "agent/master_agent_bfm/axi4_master_driver_bfm.sv")
    
    # Check if files exist
    if not os.path.exists(slave_driver_path):
        print(f"❌ Error: Slave driver not found at {slave_driver_path}")
        return False
    
    if not os.path.exists(master_driver_path):
        print(f"❌ Error: Master driver not found at {master_driver_path}")
        return False
    
    # Backup files
    backup_file(slave_driver_path)
    backup_file(master_driver_path)
    
    # Apply fixes
    success = True
    success &= fix_slave_driver_ar_r_channels(slave_driver_path)
    success &= fix_master_driver_ar_r_channels(master_driver_path)
    
    if success:
        print("\n" + "="*60)
        print("✅ AR and R channel fixes successfully applied!")
        print("\nKey improvements:")
        print("  • Transaction queue system for read operations")
        print("  • Proper state management between AR and R channels")
        print("  • Signal initialization to prevent unknown values")
        print("  • Timeout protection for handshakes")
        print("  • Enhanced debugging messages")
        print("\nNext steps:")
        print("  1. Run: make clean")
        print("  2. Run: make run_fsdb TEST=axi4_simple_crossbar_test")
        print("  3. Check waveforms in Verdi for AR and R channel activity")
        print("="*60)
    else:
        print("\n❌ Some fixes failed to apply")
        return False
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)