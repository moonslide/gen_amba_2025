#!/usr/bin/env python3
"""
Fix slave BFM by adding missing handle_write_transactions and handle_read_transactions tasks
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

def fix_slave_bfm(bfm_path):
    """Add missing transaction handling tasks to slave BFM"""
    
    print(f"\n📝 Fixing slave BFM to add missing transaction handling tasks...")
    
    # Read the file
    with open(bfm_path, 'r') as f:
        content = f.read()
    
    # Find where to insert the tasks (before endmodule)
    insertion_point = "endmodule : axi4_slave_driver_bfm"
    
    # Define the missing tasks
    new_tasks = """
    //--------------------------------------------------------------------------
    // Handle Write Transactions - Accept all writes immediately
    //--------------------------------------------------------------------------
    task handle_write_transactions();
        forever begin
            @(posedge aclk);
            
            // Handle write address channel
            if (axi_intf.awvalid && !axi_intf.awready) begin
                axi_intf.awready <= 1'b1;
                @(posedge aclk);
                axi_intf.awready <= 1'b0;
            end
            
            // Handle write data channel
            if (axi_intf.wvalid && !axi_intf.wready) begin
                axi_intf.wready <= 1'b1;
                
                // Wait for last beat
                while (!(axi_intf.wvalid && axi_intf.wlast)) begin
                    @(posedge aclk);
                end
                
                @(posedge aclk);
                axi_intf.wready <= 1'b0;
                
                // Send write response
                axi_intf.bid    <= axi_intf.awid;
                axi_intf.bresp  <= 2'b00; // OKAY
                axi_intf.bvalid <= 1'b1;
                
                // Wait for response acceptance
                while (!axi_intf.bready) begin
                    @(posedge aclk);
                end
                
                @(posedge aclk);
                axi_intf.bvalid <= 1'b0;
            end
        end
    endtask
    
    //--------------------------------------------------------------------------
    // Handle Read Transactions - Return dummy data immediately
    //--------------------------------------------------------------------------
    task handle_read_transactions();
        int beat_count;
        
        forever begin
            @(posedge aclk);
            
            // Handle read address channel
            if (axi_intf.arvalid && !axi_intf.arready) begin
                axi_intf.arready <= 1'b1;
                @(posedge aclk);
                axi_intf.arready <= 1'b0;
                
                // Generate read data response
                beat_count = axi_intf.arlen + 1;
                
                for (int i = 0; i < beat_count; i++) begin
                    axi_intf.rid    <= axi_intf.arid;
                    axi_intf.rdata  <= {DATA_WIDTH{1'b1}}; // Return all 1s as dummy data
                    axi_intf.rresp  <= 2'b00; // OKAY
                    axi_intf.rlast  <= (i == beat_count - 1);
                    axi_intf.rvalid <= 1'b1;
                    
                    // Wait for ready
                    while (!axi_intf.rready) begin
                        @(posedge aclk);
                    end
                    
                    @(posedge aclk);
                end
                
                axi_intf.rvalid <= 1'b0;
                axi_intf.rlast  <= 1'b0;
            end
        end
    endtask

"""
    
    # Insert the tasks before endmodule
    content = content.replace(insertion_point, new_tasks + insertion_point)
    
    # Write the fixed content
    with open(bfm_path, 'w') as f:
        f.write(content)
    
    print(f"✓ Added missing handle_write_transactions and handle_read_transactions tasks")
    return True

def main():
    """Main function to fix slave BFM"""
    
    print("\n" + "="*60)
    print("🔧 AXI4 Slave BFM Missing Tasks Fix")
    print("="*60)
    
    # Define path
    base_path = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration"
    bfm_path = os.path.join(base_path, "agent/slave_agent_bfm/axi4_slave_driver_bfm.sv")
    
    # Check if file exists
    if not os.path.exists(bfm_path):
        print(f"❌ Error: Slave BFM not found at {bfm_path}")
        return False
    
    # Backup file
    backup_file(bfm_path)
    
    # Apply fix
    success = fix_slave_bfm(bfm_path)
    
    if success:
        print("\n" + "="*60)
        print("✅ Slave BFM fix successfully applied!")
        print("\nKey improvements:")
        print("  • Added handle_write_transactions task")
        print("  • Added handle_read_transactions task")
        print("  • Slaves will now respond with ready signals")
        print("  • DUT signals should now be active")
        print("\nNext steps:")
        print("  1. Run: make clean")
        print("  2. Run: make run_fsdb TEST=axi4_simple_crossbar_test")
        print("  3. Check DUT signals in waveform - they should now show activity!")
        print("="*60)
    else:
        print("\n❌ Fix failed to apply")
        return False
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)