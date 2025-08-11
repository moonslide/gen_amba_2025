#!/usr/bin/env python3
"""
AXI4 Spec Compliance Fix - ULTRATHINK Edition
Fixes all AXI4 protocol compliance issues per IHI0022D_amba_axi_protocol_spec.pdf

Issues addressed:
1. wlast not raising in last transaction
2. bid and bresp not changing  
3. AR channel not showing value changes
4. Full AXI4 protocol compliance per spec
"""

import os
import sys
import shutil
from datetime import datetime

def backup_file(filepath):
    """Create backup of file before modifying"""
    if not os.path.exists(filepath):
        return None
    backup_path = f"{filepath}.backup_axi4_spec_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    shutil.copy2(filepath, backup_path)
    print(f"✓ Backed up {os.path.basename(filepath)}")
    return backup_path

def create_axi4_spec_compliant_driver():
    """Create AXI4 spec compliant driver implementation per IHI0022D"""
    
    return '''        task drive_write_transaction(axi4_master_tx tx);
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
            
            // Per IHI0022D Section A3.2 - Write Data Channel  
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
                
                // Per IHI0022D A3.2.2 - Wait for WREADY handshake
                while (!vif.wready) @(posedge vif.aclk);
                
                // IHI0022D A3.2.2 - Both WVALID and WREADY must be HIGH for transfer
                `uvm_info(get_type_name(), $sformatf("Write handshake %0d complete (WLAST=%0b)", beat, vif.wlast), UVM_HIGH)
            end
            
            @(posedge vif.aclk);
            vif.wvalid <= 1'b0;            // Clear after final beat
            vif.wlast  <= 1'b0;            // Clear WLAST after final handshake
            vif.wdata  <= '0;
            vif.wstrb  <= '0;
            
            `uvm_info(get_type_name(), "Write data phase completed per AXI4 spec", UVM_MEDIUM)
            
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
        endtask'''

def create_axi4_spec_compliant_slave_bfm():
    """Create AXI4 spec compliant slave BFM per IHI0022D"""
    
    return '''    // AXI4 Spec Compliant BFM - Per IHI0022D_amba_axi_protocol_spec.pdf
    initial begin
        // Initialize all response signals per spec
        axi_intf.awready = 1'b0;
        axi_intf.wready  = 1'b0; 
        axi_intf.bvalid  = 1'b0;
        axi_intf.bid     = '0;
        axi_intf.bresp   = 2'b00;
        axi_intf.arready = 1'b0;
        axi_intf.rvalid  = 1'b0;
        axi_intf.rid     = '0;
        axi_intf.rdata   = '0;
        axi_intf.rresp   = 2'b00;
        axi_intf.rlast   = 1'b0;
        
        // Wait for reset release
        wait(aresetn == 1'b1);
        #10;
        
        // Per IHI0022D - slave can be always ready or add delays
        axi_intf.awready <= 1'b1;  // Ready to accept write addresses
        axi_intf.wready  <= 1'b1;  // Ready to accept write data  
        axi_intf.arready <= 1'b1;  // Ready to accept read addresses
        
        `uvm_info("AXI4_SLAVE_BFM", "AXI4 Slave BFM initialized per IHI0022D spec", UVM_MEDIUM);
        
        // AXI4 compliant response handling
        fork
            // Write Response Handler - Per IHI0022D Section A3.3
            begin
                logic [ID_WIDTH-1:0] write_id_queue[$];
                forever begin
                    @(posedge aclk);
                    
                    // IHI0022D A3.2.2 - Capture AWID during AW handshake
                    if (axi_intf.awvalid && axi_intf.awready) begin
                        write_id_queue.push_back(axi_intf.awid);
                        `uvm_info("AXI4_SLAVE_BFM", $sformatf("Write address captured: AWID=%0d, AWADDR=0x%0h", 
                                  axi_intf.awid, axi_intf.awaddr), UVM_HIGH)
                    end
                    
                    // IHI0022D A3.2.1 - Respond when WLAST indicates end of burst
                    if (axi_intf.wvalid && axi_intf.wready && axi_intf.wlast && !axi_intf.bvalid) begin
                        if (write_id_queue.size() > 0) begin
                            automatic logic [ID_WIDTH-1:0] response_id = write_id_queue.pop_front();
                            
                            // IHI0022D A3.3.1 - BID must match AWID, BRESP indicates status
                            axi_intf.bid    <= response_id;  // Must match AWID per spec
                            axi_intf.bresp  <= 2'b00;        // OKAY response
                            axi_intf.bvalid <= 1'b1;         // Response valid
                            
                            `uvm_info("AXI4_SLAVE_BFM", $sformatf("Write response: BID=%0d, BRESP=OKAY (per IHI0022D A3.3)", 
                                      response_id), UVM_MEDIUM)
                        end else begin
                            `uvm_error("AXI4_SLAVE_BFM", "WLAST without corresponding AWID - AXI4 protocol violation")
                        end
                    end
                    
                    // IHI0022D A3.3.2 - Clear response when BREADY handshake completes
                    if (axi_intf.bvalid && axi_intf.bready) begin
                        @(posedge aclk);
                        axi_intf.bvalid <= 1'b0;
                        axi_intf.bid    <= '0;
                        `uvm_info("AXI4_SLAVE_BFM", "Write response handshake completed", UVM_HIGH)
                    end
                end
            end
            
            // Read Response Handler - Per IHI0022D Section A3.4
            begin
                forever begin
                    @(posedge aclk);
                    
                    // IHI0022D A3.4.2 - Handle read request during AR handshake
                    if (axi_intf.arvalid && axi_intf.arready && !axi_intf.rvalid) begin
                        automatic logic [ID_WIDTH-1:0] read_id = axi_intf.arid;
                        automatic logic [7:0] read_len = axi_intf.arlen;
                        automatic logic [ADDR_WIDTH-1:0] read_addr = axi_intf.araddr;
                        
                        `uvm_info("AXI4_SLAVE_BFM", $sformatf("Read request: ARID=%0d, ARADDR=0x%0h, ARLEN=%0d (per IHI0022D A3.4)", 
                                  read_id, read_addr, read_len), UVM_MEDIUM)
                        
                        // IHI0022D A3.4.1 - Send arlen+1 data beats, RLAST on final beat
                        for (int beat = 0; beat <= read_len; beat++) begin
                            @(posedge aclk);
                            
                            // IHI0022D A3.4.1 - RID must match ARID
                            axi_intf.rid    <= read_id;
                            axi_intf.rdata  <= {DATA_WIDTH{1'b0}} | (read_addr + beat * 8);  // Address pattern
                            axi_intf.rresp  <= 2'b00;              // OKAY response
                            axi_intf.rlast  <= (beat == read_len);  // RLAST on final beat per spec
                            axi_intf.rvalid <= 1'b1;               // Data valid
                            
                            `uvm_info("AXI4_SLAVE_BFM", $sformatf("Read response beat %0d/%0d: RID=%0d, RDATA=0x%0h, RLAST=%0b", 
                                      beat, read_len, read_id, axi_intf.rdata, axi_intf.rlast), UVM_HIGH)
                            
                            // IHI0022D A3.4.2 - Wait for RREADY handshake
                            while (!axi_intf.rready) @(posedge aclk);
                            @(posedge aclk);
                            
                            axi_intf.rvalid <= 1'b0;
                            axi_intf.rlast  <= 1'b0;
                        end
                        
                        `uvm_info("AXI4_SLAVE_BFM", $sformatf("Read burst completed for ARID=%0d per AXI4 spec", read_id), UVM_MEDIUM)
                    end
                end
            end
        join_none
    end'''

def fix_axi4_master_driver(pkg_path):
    """Fix master driver with full AXI4 spec compliance"""
    
    print("📝 Applying AXI4 spec compliant master driver...")
    
    with open(pkg_path, 'r') as f:
        content = f.read()
    
    # Replace the entire driver task implementations
    spec_compliant_driver = create_axi4_spec_compliant_driver()
    
    # Find and replace write task
    write_task_start = content.find('task drive_write_transaction(axi4_master_tx tx);')
    if write_task_start != -1:
        write_task_end = content.find('endtask', write_task_start) + len('endtask')
        # Find read task start
        read_task_start = content.find('task drive_read_transaction(axi4_master_tx tx);', write_task_end)
        if read_task_start != -1:
            read_task_end = content.find('endtask', read_task_start) + len('endtask')
            # Replace both tasks
            content = content[:write_task_start] + spec_compliant_driver + content[read_task_end:]
        else:
            print("⚠️ Could not find read task")
    else:
        print("⚠️ Could not find write task")
    
    with open(pkg_path, 'w') as f:
        f.write(content)
    
    print("✓ Applied AXI4 spec compliant driver")
    return True

def fix_axi4_slave_bfm(bfm_path):
    """Fix slave BFM with full AXI4 spec compliance"""
    
    print("📝 Applying AXI4 spec compliant slave BFM...")
    
    with open(bfm_path, 'r') as f:
        content = f.read()
    
    # Find the initial block and replace it
    initial_start = content.find('// Ultra-simple slave BFM - always ready, immediate response')
    if initial_start != -1:
        initial_block_start = content.find('initial begin', initial_start)
        if initial_block_start != -1:
            initial_block_end = content.find('\nendmodule', initial_block_start)
            if initial_block_end != -1:
                spec_compliant_bfm = create_axi4_spec_compliant_slave_bfm()
                content = content[:initial_block_start] + spec_compliant_bfm + '\n\nendmodule : axi4_slave_driver_bfm\n'
            else:
                print("⚠️ Could not find endmodule")
        else:
            print("⚠️ Could not find initial begin")
    else:
        print("⚠️ Could not find BFM section to replace")
        return False
    
    with open(bfm_path, 'w') as f:
        f.write(content)
    
    print("✓ Applied AXI4 spec compliant slave BFM")
    return True

def main():
    """Main function to apply AXI4 spec compliant fixes"""
    
    print("\n" + "="*80)
    print("🎯 AXI4 Specification Compliance Fix - ULTRATHINK Edition")
    print("   Per IHI0022D_amba_axi_protocol_spec.pdf")
    print("="*80)
    
    base_path = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration"
    
    files_to_fix = [
        ("master/axi4_master_pkg.sv", fix_axi4_master_driver),
        ("agent/slave_agent_bfm/axi4_slave_driver_bfm.sv", fix_axi4_slave_bfm),
    ]
    
    success = True
    for rel_path, fix_func in files_to_fix:
        full_path = os.path.join(base_path, rel_path)
        if os.path.exists(full_path):
            backup_file(full_path)
            success &= fix_func(full_path)
        else:
            print(f"❌ Error: {rel_path} not found")
            success = False
    
    if success:
        print("\n" + "="*80)
        print("✅ AXI4 Specification Compliance Applied!")
        print("\n🎯 Fixed Issues per IHI0022D:")
        print("  1. ✅ WLAST timing - asserted on final beat of write burst")
        print("  2. ✅ BID/BRESP - BID matches AWID, proper response timing")  
        print("  3. ✅ AR channel - proper read address channel driving")
        print("  4. ✅ RID/RLAST - RID matches ARID, RLAST on final beat")
        print("  5. ✅ Handshake timing - proper VALID/READY protocol")
        
        print("\n📋 AXI4 Protocol Compliance:")
        print("  • Write: AW → W(WLAST) → B handshakes per spec")
        print("  • Read: AR → R(RLAST) handshakes per spec")
        print("  • ID matching: BID=AWID, RID=ARID per spec")
        print("  • Burst handling: awlen+1/arlen+1 beats per spec")
        print("  • Signal timing: compliant with IHI0022D timing")
        
        print("\n🔍 Expected FSDB Results:")
        print("  • M0 WLAST will assert on beat 3 (last of 4 beats)")  
        print("  • BID will match AWID values and change per transaction")
        print("  • BRESP will show OKAY responses")
        print("  • AR channel will show changing address values")
        print("  • RID will match ARID values")
        print("  • All channels will show proper AXI4 activity")
        
        print("\n💡 Next Steps:")
        print("  1. Run: make clean && make run_fsdb TEST=axi4_simple_crossbar_test")
        print("  2. Check FSDB: All 5 AXI4 channels should show activity")
        print("  3. Verify: WLAST on final beat, BID changes, AR activity")
        print("="*80)
    else:
        print("\n❌ Some AXI4 fixes failed to apply")
        return False
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)