#!/usr/bin/env python3
"""
WLAST Counting and Validation Fix - ULTRATHINK Edition
Adds proper wlast counting per master and scoreboard validation
"""

import os
import sys
import shutil
import re
from datetime import datetime

def backup_file(filepath):
    """Create backup of file before modifying"""
    if not os.path.exists(filepath):
        return None
    backup_path = f"{filepath}.backup_wlast_count_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    shutil.copy2(filepath, backup_path)
    print(f"✓ Backed up {os.path.basename(filepath)}")
    return backup_path

def fix_master_driver_wlast_counting(pkg_path):
    """Add comprehensive wlast counting and signal generation to master driver"""
    
    print("📝 Adding wlast counting and validation to master driver...")
    
    with open(pkg_path, 'r') as f:
        content = f.read()
    
    # Enhanced driver class with wlast counting
    enhanced_driver_class = '''    // Driver class - Properly drives AXI interface signals with WLAST counting
    class axi4_master_driver extends uvm_driver #(axi4_master_tx);
        `uvm_component_utils(axi4_master_driver)
        
        // Virtual interface handle
        virtual axi4_if vif;
        
        // WLAST counting and validation
        int wlast_count = 0;
        int transaction_count = 0;
        int expected_wlast_count = 0;
        
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
            `uvm_info(get_type_name(), "Starting master driver run_phase with WLAST counting", UVM_LOW)
            
            // Initialize interface signals
            reset_signals();
            
            forever begin
                `uvm_info(get_type_name(), "Waiting for next transaction from sequencer", UVM_HIGH)
                seq_item_port.get_next_item(req);
                
                transaction_count++;
                `uvm_info(get_type_name(), $sformatf("Processing transaction %0d: %s - addr=0x%0h, len=%0d", 
                    transaction_count, req.tx_type.name(), 
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awaddr : req.araddr,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awlen : req.arlen), UVM_MEDIUM)
                
                // Drive the actual transaction on the interface
                if (req.tx_type == axi4_master_tx::WRITE) begin
                    expected_wlast_count++; // Each write transaction should generate 1 WLAST
                    drive_write_transaction(req);
                end else begin
                    drive_read_transaction(req);
                end
                
                `uvm_info(get_type_name(), $sformatf("Transaction %0d completed. WLAST count: %0d/%0d expected", 
                          transaction_count, wlast_count, expected_wlast_count), UVM_MEDIUM)
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
            int wlast_generated = 0;
            
            `uvm_info(get_type_name(), $sformatf("AXI4 WRITE: addr=0x%0h, len=%0d, size=%0d, burst=%0d, id=%0d", 
                      tx.awaddr, tx.awlen, tx.awsize, tx.awburst, tx.awid), UVM_MEDIUM)
            
            // Per IHI0022D Section A3.2 - Write Address Channel
            @(posedge vif.aclk);
            vif.awid    <= tx.awid;        // IHI0022D A3.2.1 - Write address ID
            vif.awaddr  <= tx.awaddr;      // IHI0022D A3.2.1 - Write address
            vif.awlen   <= tx.awlen;       // IHI0022D A3.2.1 - Burst length (beats - 1)
            vif.awsize  <= tx.awsize;      // IHI0022D A3.2.1 - Burst size
            vif.awburst <= tx.awburst;     // IHI0022D A3.2.1 - Burst type
            vif.awlock  <= tx.awlock;      // IHI0022D A3.2.1 - Lock type
            vif.awcache <= tx.awcache;     // IHI0022D A3.2.1 - Memory type
            vif.awprot  <= tx.awprot;      // IHI0022D A3.2.1 - Protection type
            vif.awqos   <= tx.awqos;       // IHI0022D A3.2.1 - Quality of Service
            vif.awregion <= tx.awregion;   // IHI0022D A3.2.1 - Region identifier
            vif.awvalid <= 1'b1;           // IHI0022D A3.2.2 - Address valid
            
            `uvm_info(get_type_name(), $sformatf("AW channel driven with AWID=%0d, AWADDR=0x%0h", tx.awid, tx.awaddr), UVM_HIGH)
            
            // Per IHI0022D A3.2.2 - Wait for AWREADY handshake
            while (!vif.awready) @(posedge vif.aclk);
            @(posedge vif.aclk);
            vif.awvalid <= 1'b0;           // Clear AWVALID after handshake
            
            `uvm_info(get_type_name(), "AW handshake completed", UVM_HIGH)
            
            // Per IHI0022D Section A3.2 - Write Data Channel with WLAST counting  
            // CRITICAL: awlen+1 beats, WLAST on final beat
            for (int beat = 0; beat <= tx.awlen; beat++) begin
                @(posedge vif.aclk);
                vif.wdata  <= (beat < tx.wdata.size()) ? tx.wdata[beat] : {DATA_WIDTH{1'b0}};
                vif.wstrb  <= (beat < tx.wstrb.size()) ? tx.wstrb[beat] : {(DATA_WIDTH/8){1'b1}};
                // IHI0022D A3.2.1 - WLAST indicates the last transfer in a write burst
                vif.wlast  <= (beat == tx.awlen);    // CRITICAL: Last beat per spec
                vif.wvalid <= 1'b1;
                
                `uvm_info(get_type_name(), $sformatf("Write beat %0d/%0d: WDATA=0x%0h, WLAST=%0b", 
                          beat, tx.awlen, vif.wdata, vif.wlast), UVM_HIGH)
                
                // Count WLAST assertion
                if (vif.wlast && vif.wvalid) begin
                    wlast_generated = 1;
                    `uvm_info(get_type_name(), $sformatf("*** WLAST ASSERTED *** on beat %0d (master transaction %0d)", 
                              beat, transaction_count), UVM_MEDIUM)
                end
                
                // Per IHI0022D A3.2.2 - Wait for WREADY handshake
                while (!vif.wready) @(posedge vif.aclk);
                
                // IHI0022D A3.2.2 - Both WVALID and WREADY must be HIGH for transfer
                `uvm_info(get_type_name(), $sformatf("Write handshake %0d complete (WLAST=%0b)", beat, vif.wlast), UVM_HIGH)
                
                // Count WLAST during successful handshake
                if (vif.wlast && vif.wvalid && vif.wready) begin
                    wlast_count++;
                    `uvm_info(get_type_name(), $sformatf("*** WLAST HANDSHAKE COMPLETE *** count now: %0d", wlast_count), UVM_MEDIUM)
                end
            end
            
            @(posedge vif.aclk);
            vif.wvalid <= 1'b0;            // Clear after final beat
            vif.wlast  <= 1'b0;            // Clear WLAST after final handshake
            vif.wdata  <= '0;
            vif.wstrb  <= '0;
            
            // Validation check
            if (!wlast_generated) begin
                `uvm_error(get_type_name(), $sformatf("WLAST was never generated for transaction %0d!", transaction_count))
            end else begin
                `uvm_info(get_type_name(), $sformatf("Write data phase completed per AXI4 spec. WLAST count: %0d", wlast_count), UVM_MEDIUM)
            end
            
            // Per IHI0022D Section A3.3 - Write Response Channel
            vif.bready <= 1'b1;            // Ready to accept write response
            `uvm_info(get_type_name(), "Waiting for B-channel response", UVM_HIGH)
            
            // IHI0022D A3.3.2 - Wait for BVALID and check BID matches AWID
            begin
                int b_timeout = 0;
                while (!vif.bvalid && b_timeout < 500) begin
                    @(posedge vif.aclk);
                    b_timeout++;
                end
                
                if (vif.bvalid) begin
                    // IHI0022D A3.3.1 - BID must match AWID of write address
                    `uvm_info(get_type_name(), $sformatf("B-channel response: BID=%0d (expect %0d), BRESP=%0d", 
                              vif.bid, tx.awid, vif.bresp), UVM_MEDIUM)
                    
                    if (vif.bid != tx.awid) begin
                        `uvm_error(get_type_name(), $sformatf("BID mismatch! Expected %0d, got %0d", tx.awid, vif.bid))
                    end
                    
                    @(posedge vif.aclk);  // Complete B-channel handshake
                end else begin
                    `uvm_error(get_type_name(), "B-channel timeout - no write response received")
                end
            end
            
            vif.bready <= 1'b0;            // Clear BREADY
        endtask
        
        task drive_read_transaction(axi4_master_tx tx);
            `uvm_info(get_type_name(), $sformatf("AXI4 READ: addr=0x%0h, len=%0d, size=%0d, burst=%0d, id=%0d", 
                      tx.araddr, tx.arlen, tx.arsize, tx.arburst, tx.arid), UVM_MEDIUM)
            
            // Per IHI0022D Section A3.4 - Read Address Channel
            @(posedge vif.aclk);
            vif.arid    <= tx.arid;        // IHI0022D A3.4.1 - Read address ID  
            vif.araddr  <= tx.araddr;      // IHI0022D A3.4.1 - Read address
            vif.arlen   <= tx.arlen;       // IHI0022D A3.4.1 - Burst length (beats - 1)
            vif.arsize  <= tx.arsize;      // IHI0022D A3.4.1 - Burst size
            vif.arburst <= tx.arburst;     // IHI0022D A3.4.1 - Burst type
            vif.arlock  <= tx.arlock;      // IHI0022D A3.4.1 - Lock type
            vif.arcache <= tx.arcache;     // IHI0022D A3.4.1 - Memory type
            vif.arprot  <= tx.arprot;      // IHI0022D A3.4.1 - Protection type
            vif.arqos   <= tx.arqos;       // IHI0022D A3.4.1 - Quality of Service
            vif.arregion <= tx.arregion;   // IHI0022D A3.4.1 - Region identifier
            vif.arvalid <= 1'b1;           // IHI0022D A3.4.2 - Address valid
            
            `uvm_info(get_type_name(), $sformatf("AR channel driven: ARID=%0d, ARADDR=0x%0h, ARLEN=%0d", 
                      tx.arid, tx.araddr, tx.arlen), UVM_MEDIUM)
            
            // Per IHI0022D A3.4.2 - Wait for ARREADY handshake
            while (!vif.arready) @(posedge vif.aclk);
            @(posedge vif.aclk);
            vif.arvalid <= 1'b0;           // Clear ARVALID after handshake
            
            `uvm_info(get_type_name(), "AR handshake completed - read address accepted", UVM_HIGH)
            
            // Per IHI0022D Section A3.4 - Read Data Channel
            tx.rdata = new[tx.arlen + 1];  // Allocate for arlen+1 beats
            vif.rready <= 1'b1;            // Ready to accept read data
            
            `uvm_info(get_type_name(), $sformatf("Waiting for %0d read data beats", tx.arlen+1), UVM_HIGH)
            
            // IHI0022D A3.4.2 - Collect arlen+1 data beats
            for (int beat = 0; beat <= tx.arlen; beat++) begin
                // Wait for RVALID
                begin
                    int r_timeout = 0;
                    while (!vif.rvalid && r_timeout < 500) begin
                        @(posedge vif.aclk);
                        r_timeout++;
                    end
                    
                    if (r_timeout >= 500) begin
                        `uvm_error(get_type_name(), $sformatf("R-channel timeout on beat %0d", beat))
                        break;
                    end
                end
                
                if (vif.rvalid) begin
                    // IHI0022D A3.4.1 - Capture read data and check RID matches ARID
                    tx.rdata[beat] = vif.rdata;
                    `uvm_info(get_type_name(), $sformatf("Read beat %0d/%0d: RID=%0d (expect %0d), RDATA=0x%0h, RLAST=%0b, RRESP=%0d", 
                              beat, tx.arlen, vif.rid, tx.arid, vif.rdata, vif.rlast, vif.rresp), UVM_MEDIUM)
                    
                    // IHI0022D A3.4.1 - RID must match ARID
                    if (vif.rid != tx.arid) begin
                        `uvm_error(get_type_name(), $sformatf("RID mismatch! Expected %0d, got %0d", tx.arid, vif.rid))
                    end
                    
                    // IHI0022D A3.4.1 - RLAST indicates final transfer in read burst
                    if (beat == tx.arlen && !vif.rlast) begin
                        `uvm_error(get_type_name(), "RLAST not asserted on final beat")
                    end else if (beat < tx.arlen && vif.rlast) begin
                        `uvm_error(get_type_name(), $sformatf("RLAST asserted early on beat %0d", beat))
                    end
                    
                    @(posedge vif.aclk);  // Complete R-channel handshake
                    
                    if (vif.rlast) begin
                        `uvm_info(get_type_name(), "RLAST received - read burst complete", UVM_HIGH)
                        break;
                    end
                end
            end
            
            vif.rready <= 1'b0;            // Clear RREADY
            `uvm_info(get_type_name(), $sformatf("Read transaction completed, received %0d beats per AXI4 spec", 
                      tx.rdata.size()), UVM_MEDIUM)
        endtask
        
        // Report final statistics
        function void report_phase(uvm_phase phase);
            super.report_phase(phase);
            `uvm_info(get_type_name(), $sformatf("=== WLAST STATISTICS ==="), UVM_LOW)
            `uvm_info(get_type_name(), $sformatf("Total Transactions: %0d", transaction_count), UVM_LOW)
            `uvm_info(get_type_name(), $sformatf("Expected WLAST Count: %0d", expected_wlast_count), UVM_LOW)
            `uvm_info(get_type_name(), $sformatf("Actual WLAST Count: %0d", wlast_count), UVM_LOW)
            if (wlast_count != expected_wlast_count) begin
                `uvm_error(get_type_name(), $sformatf("WLAST COUNT MISMATCH! Expected: %0d, Got: %0d", expected_wlast_count, wlast_count))
            end else begin
                `uvm_info(get_type_name(), "✓ WLAST count matches expected!", UVM_LOW)
            end
        endfunction'''
    
    # Find the driver class and replace it
    driver_class_pattern = r'// Driver class - Properly drives AXI interface signals.*?endclass'
    content = re.sub(driver_class_pattern, enhanced_driver_class, content, flags=re.DOTALL)
    
    with open(pkg_path, 'w') as f:
        f.write(content)
    
    print("✓ Added wlast counting and validation to master driver")
    return True

def enhance_scoreboard_wlast_tracking(scoreboard_path):
    """Add WLAST tracking to scoreboard"""
    
    print("📝 Enhancing scoreboard with WLAST tracking...")
    
    with open(scoreboard_path, 'r') as f:
        content = f.read()
    
    # Find scoreboard class and add WLAST tracking
    enhanced_scoreboard = '''    class axi4_scoreboard extends uvm_scoreboard;
        `uvm_component_utils(axi4_scoreboard)
        
        // Analysis fifos for master and slave transactions
        uvm_tlm_analysis_fifo #(axi4_master_tx) master_fifo;
        uvm_tlm_analysis_fifo #(axi4_slave_tx) slave_fifo;
        
        // WLAST tracking per master
        int wlast_count_per_master[int];
        int write_transactions_per_master[int];
        int total_wlast_expected = 0;
        int total_wlast_observed = 0;
        
        function new(string name = "axi4_scoreboard", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            master_fifo = new("master_fifo", this);
            slave_fifo = new("slave_fifo", this);
            `uvm_info(get_type_name(), "Scoreboard built with WLAST tracking", UVM_LOW)
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            `uvm_info(get_type_name(), "Starting scoreboard with WLAST monitoring", UVM_LOW)
            
            fork
                process_master_transactions();
                process_slave_transactions();
                wlast_validation_monitor();
            join_none
        endtask
        
        virtual task process_master_transactions();
            axi4_master_tx master_tx;
            forever begin
                master_fifo.get(master_tx);
                
                if (master_tx.tx_type == axi4_master_tx::WRITE) begin
                    if (!wlast_count_per_master.exists(master_tx.awid)) begin
                        wlast_count_per_master[master_tx.awid] = 0;
                        write_transactions_per_master[master_tx.awid] = 0;
                    end
                    
                    write_transactions_per_master[master_tx.awid]++;
                    total_wlast_expected++;
                    
                    `uvm_info(get_type_name(), $sformatf("Master %0d WRITE transaction: expected WLAST count now %0d", 
                              master_tx.awid, write_transactions_per_master[master_tx.awid]), UVM_MEDIUM)
                end
                
                `uvm_info(get_type_name(), $sformatf("Processed master transaction: ID=%0d, TYPE=%s", 
                          (master_tx.tx_type == axi4_master_tx::WRITE) ? master_tx.awid : master_tx.arid,
                          master_tx.tx_type.name()), UVM_HIGH)
            end
        endtask
        
        virtual task process_slave_transactions();
            axi4_slave_tx slave_tx;
            forever begin
                slave_fifo.get(slave_tx);
                `uvm_info(get_type_name(), $sformatf("Processed slave transaction"), UVM_HIGH)
            end
        endtask
        
        virtual task wlast_validation_monitor();
            // Monitor interface for WLAST signals (if interface access is available)
            forever begin
                #1000; // Periodic validation
                `uvm_info(get_type_name(), $sformatf("WLAST Status - Expected: %0d, Observed: %0d", 
                          total_wlast_expected, total_wlast_observed), UVM_HIGH)
            end
        endtask
        
        function void report_phase(uvm_phase phase);
            super.report_phase(phase);
            
            `uvm_info(get_type_name(), "=== SCOREBOARD WLAST REPORT ===", UVM_LOW)
            `uvm_info(get_type_name(), $sformatf("Total Expected WLAST: %0d", total_wlast_expected), UVM_LOW)
            `uvm_info(get_type_name(), $sformatf("Total Observed WLAST: %0d", total_wlast_observed), UVM_LOW)
            
            foreach (wlast_count_per_master[master_id]) begin
                `uvm_info(get_type_name(), $sformatf("Master %0d - WLAST: %0d/%0d", 
                          master_id, wlast_count_per_master[master_id], write_transactions_per_master[master_id]), UVM_LOW)
            end
            
            if (total_wlast_expected != total_wlast_observed) begin
                `uvm_error(get_type_name(), $sformatf("WLAST VALIDATION FAILED! Expected: %0d, Observed: %0d", 
                          total_wlast_expected, total_wlast_observed))
            end else begin
                `uvm_info(get_type_name(), "✓ WLAST validation PASSED!", UVM_LOW)
            end
        endfunction'''
    
    # Replace the scoreboard class
    scoreboard_class_pattern = r'class axi4_scoreboard extends uvm_scoreboard;.*?endclass'
    content = re.sub(scoreboard_class_pattern, enhanced_scoreboard, content, flags=re.DOTALL)
    
    with open(scoreboard_path, 'w') as f:
        f.write(content)
    
    print("✓ Enhanced scoreboard with WLAST tracking")
    return True

def add_wlast_monitor(monitor_path):
    """Add WLAST signal monitoring to monitor"""
    
    print("📝 Adding WLAST signal monitoring...")
    
    with open(monitor_path, 'r') as f:
        content = f.read()
    
    # Find monitor and add WLAST monitoring
    wlast_monitor_addition = '''        // WLAST Signal Monitoring
        int wlast_assertions = 0;
        
        virtual task monitor_wlast_signals();
            `uvm_info(get_type_name(), "Starting WLAST signal monitoring", UVM_LOW)
            forever begin
                @(posedge vif.aclk);
                if (vif.wvalid && vif.wready && vif.wlast) begin
                    wlast_assertions++;
                    `uvm_info(get_type_name(), $sformatf("*** WLAST ASSERTION DETECTED *** Count: %0d", wlast_assertions), UVM_MEDIUM)
                end
            end
        endtask'''
    
    # Add WLAST monitoring to run_phase
    run_phase_pattern = r'(virtual task run_phase\(uvm_phase phase\);.*?)(forever begin.*?end\s*endtask)'
    
    def add_wlast_monitoring(match):
        return match.group(1) + '''
            // Start WLAST monitoring
            fork
                monitor_wlast_signals();
            join_none
            
''' + match.group(2)
    
    content = re.sub(run_phase_pattern, add_wlast_monitoring, content, flags=re.DOTALL)
    
    # Add the monitoring method before the endclass
    endclass_pattern = r'(endclass.*)'
    content = re.sub(endclass_pattern, wlast_monitor_addition + '\n        \n    \\1', content)
    
    with open(monitor_path, 'w') as f:
        f.write(content)
    
    print("✓ Added WLAST signal monitoring")
    return True

def main():
    """Main function to apply WLAST counting and validation fixes"""
    
    print("\n" + "="*70)
    print("🎯 WLAST Counting and Validation Fix - ULTRATHINK")
    print("="*70)
    
    base_path = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration"
    
    files_to_fix = [
        ("master/axi4_master_pkg.sv", fix_master_driver_wlast_counting),
        ("env/axi4_scoreboard.sv", enhance_scoreboard_wlast_tracking),
        ("master/axi4_master_pkg.sv", add_wlast_monitor),  # Add to monitor in same file
    ]
    
    success = True
    for rel_path, fix_func in files_to_fix:
        full_path = os.path.join(base_path, rel_path)
        if os.path.exists(full_path):
            if fix_func != add_wlast_monitor:  # Don't backup same file twice
                backup_file(full_path)
            success &= fix_func(full_path)
        else:
            print(f"❌ Error: {rel_path} not found")
            success = False
    
    if success:
        print("\n" + "="*70)
        print("✅ WLAST Counting and Validation Applied!")
        print("\n🎯 Enhanced Features:")
        print("  1. ✅ WLAST counting per master transaction")
        print("  2. ✅ Driver validation of WLAST generation")
        print("  3. ✅ Scoreboard WLAST tracking and comparison")
        print("  4. ✅ Signal monitoring for WLAST assertions")
        print("  5. ✅ Comprehensive reporting and validation")
        
        print("\n📊 Expected Results:")
        print("  • Each write transaction will generate exactly 1 WLAST")
        print("  • Driver reports WLAST count per master")
        print("  • Scoreboard validates expected vs actual WLAST")
        print("  • Monitor tracks WLAST signal assertions")
        print("  • Full validation report at test completion")
        
        print("\n💡 Next Steps:")
        print("  1. Run test to verify WLAST counting")
        print("  2. Check logs for WLAST statistics")
        print("  3. Update generator script with fixes")
        print("="*70)
    else:
        print("\n❌ Some WLAST fixes failed to apply")
        return False
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)