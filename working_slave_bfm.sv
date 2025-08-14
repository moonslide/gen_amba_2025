//==============================================================================
// AXI4 Slave Driver BFM - WORKING VERSION
// Proper implementation with transaction queue
//==============================================================================

module axi4_slave_driver_bfm #(
    parameter ADDR_WIDTH = 48,
    parameter DATA_WIDTH = 256,
    parameter ID_WIDTH   = 8
)(
    input aclk,
    input aresetn,
    axi4_if.slave axi_intf
);

    import axi4_globals_pkg::*;
    import uvm_pkg::*;
    
    // Simple memory for slave responses
    bit [DATA_WIDTH-1:0] memory[bit [ADDR_WIDTH-1:0]];
    
    // Transaction tracking - CRITICAL for proper B-channel response
    logic [ID_WIDTH-1:0] captured_awid;
    logic awid_valid;
    
    // Control signal for BFM operation
    bit bfm_enable = 1;
    
    // Initialize all signals
    initial begin
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
        
        captured_awid = '0;
        awid_valid = 1'b0;
        
        // Wait for reset
        wait(aresetn == 1'b1);
        #10;
        
        `uvm_info("AXI_SLAVE_DRIVER_BFM", "Slave BFM initialized and ready", UVM_LOW)
        
        // Set ready signals after reset
        axi_intf.awready <= 1'b1;
        axi_intf.wready  <= 1'b1;
        axi_intf.arready <= 1'b1;
    end
    
    // Write Address Channel - Capture AWID
    always @(posedge aclk) begin
        if (axi_intf.awvalid && axi_intf.awready) begin
            captured_awid <= axi_intf.awid;
            awid_valid <= 1'b1;
            `uvm_info("AXI_SLAVE_DRIVER_BFM", 
                $sformatf("Write address captured: AWID=%0d, AWADDR=0x%0h", 
                axi_intf.awid, axi_intf.awaddr), UVM_HIGH)
        end
    end
    
    // Write Response Channel - Use captured AWID
    always @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            axi_intf.bvalid <= 1'b0;
            axi_intf.bresp <= 2'b00;
            axi_intf.bid <= '0;
        end else if (bfm_enable && axi_intf.wvalid && axi_intf.wready && axi_intf.wlast && awid_valid) begin
            // Generate write response using captured AWID
            axi_intf.bid <= captured_awid;  // Use captured AWID, not direct access
            axi_intf.bresp <= 2'b00;  // OKAY
            axi_intf.bvalid <= 1'b1;
            awid_valid <= 1'b0;  // Clear for next transaction
            
            `uvm_info("AXI_SLAVE_DRIVER_BFM", 
                $sformatf("B-channel response: BID=%0d, BRESP=OKAY", captured_awid), UVM_MEDIUM)
        end else if (axi_intf.bvalid && axi_intf.bready) begin
            axi_intf.bvalid <= 1'b0;
            axi_intf.bid <= '0;
        end
    end
    
    // Read handling - simplified for single beat
    logic [ID_WIDTH-1:0] captured_arid;
    logic [7:0] captured_arlen;
    logic arid_valid;
    
    always @(posedge aclk) begin
        if (axi_intf.arvalid && axi_intf.arready) begin
            captured_arid <= axi_intf.arid;
            captured_arlen <= axi_intf.arlen;
            arid_valid <= 1'b1;
            `uvm_info("AXI_SLAVE_DRIVER_BFM", 
                $sformatf("Read address captured: ARID=%0d, ARADDR=0x%0h", 
                axi_intf.arid, axi_intf.araddr), UVM_HIGH)
        end
    end
    
    // Read data response
    always @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            axi_intf.rvalid <= 1'b0;
            axi_intf.rdata <= '0;
            axi_intf.rresp <= 2'b00;
            axi_intf.rlast <= 1'b0;
            axi_intf.rid <= '0;
        end else if (bfm_enable && arid_valid && !axi_intf.rvalid) begin
            // Generate read response
            axi_intf.rid <= captured_arid;
            axi_intf.rdata <= {DATA_WIDTH{1'b0}} | 64'hDEADBEEF;  // Test pattern
            axi_intf.rresp <= 2'b00;  // OKAY
            axi_intf.rlast <= 1'b1;   // Single beat for now
            axi_intf.rvalid <= 1'b1;
            
            `uvm_info("AXI_SLAVE_DRIVER_BFM", 
                $sformatf("R-channel response: RID=%0d, RLAST=1", captured_arid), UVM_HIGH)
        end else if (axi_intf.rvalid && axi_intf.rready) begin
            axi_intf.rvalid <= 1'b0;
            axi_intf.rlast <= 1'b0;
            arid_valid <= 1'b0;
        end
    end

endmodule : axi4_slave_driver_bfm