//==============================================================================
// AXI4 RTL Wrapper - Integrates generated RTL with VIP testbench
// Supports both behavioral model and actual RTL DUT modes
//==============================================================================

`ifndef AXI4_RTL_WRAPPER_SV
`define AXI4_RTL_WRAPPER_SV

module axi4_rtl_wrapper #(
    parameter int NUM_MASTERS = 2,
    parameter int NUM_SLAVES = 3,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64,
    parameter int ID_WIDTH = 4,
    parameter int USER_WIDTH = 1
)(
    // Clock and reset
    input logic aclk,
    input logic aresetn,
    
    // Master interfaces (from VIP master agents)
    axi4_if.slave master_if[NUM_MASTERS],
    
    // Slave interfaces (to VIP slave agents)
    axi4_if.master slave_if[NUM_SLAVES]
);
    
    // RTL Integration Mode Selection
    string rtl_mode;
    string rtl_path;
    bit use_generated_rtl;
    
    initial begin
        // Check if RTL mode is enabled
        if ($value$plusargs("RTL_MODE=%s", rtl_mode)) begin
            use_generated_rtl = (rtl_mode == "GENERATED");
            `uvm_info("RTL_WRAPPER", $sformatf("RTL Mode: %s", rtl_mode), UVM_LOW)
        end else begin
            use_generated_rtl = 0;
            rtl_mode = "BEHAVIORAL";
            `uvm_info("RTL_WRAPPER", "Using behavioral model (no RTL)", UVM_LOW)
        end
        
        // Get RTL path if using generated RTL
        if (use_generated_rtl) begin
            if ($value$plusargs("RTL_PATH=%s", rtl_path)) begin
                `uvm_info("RTL_WRAPPER", $sformatf("RTL Path: %s", rtl_path), UVM_LOW)
            end else begin
                `uvm_fatal("RTL_WRAPPER", "RTL_MODE=GENERATED but no RTL_PATH specified")
            end
        end
    end
    
    generate
        if (1) begin : rtl_selection
            // This block will be replaced by actual RTL inclusion based on mode
            `ifdef USE_GENERATED_RTL
                // Include the generated RTL interconnect
                `include "generated_rtl_interconnect.sv"
                
                axi4_interconnect_top #(
                    .NUM_MASTERS(NUM_MASTERS),
                    .NUM_SLAVES(NUM_SLAVES),
                    .ADDR_WIDTH(ADDR_WIDTH),
                    .DATA_WIDTH(DATA_WIDTH),
                    .ID_WIDTH(ID_WIDTH)
                ) dut (
                    .aclk(aclk),
                    .aresetn(aresetn),
                    .s_axi(master_if),  // Masters connect to slave ports
                    .m_axi(slave_if)    // Slaves connect to master ports
                );
            `else
                // Behavioral interconnect model for testing without RTL
                behavioral_axi4_interconnect #(
                    .NUM_MASTERS(NUM_MASTERS),
                    .NUM_SLAVES(NUM_SLAVES),
                    .ADDR_WIDTH(ADDR_WIDTH),
                    .DATA_WIDTH(DATA_WIDTH),
                    .ID_WIDTH(ID_WIDTH)
                ) behavioral_model (
                    .aclk(aclk),
                    .aresetn(aresetn),
                    .master_if(master_if),
                    .slave_if(slave_if)
                );
            `endif
        end
    endgenerate
    
endmodule : axi4_rtl_wrapper


//==============================================================================
// Behavioral AXI4 Interconnect Model
// Simple crossbar implementation for VIP-only testing
//==============================================================================
module behavioral_axi4_interconnect #(
    parameter int NUM_MASTERS = 2,
    parameter int NUM_SLAVES = 3,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64,
    parameter int ID_WIDTH = 4
)(
    input logic aclk,
    input logic aresetn,
    
    axi4_if.slave master_if[NUM_MASTERS],
    axi4_if.master slave_if[NUM_SLAVES]
);
    
    // Address decoder function (simplified)
    function automatic int decode_slave_index(logic [ADDR_WIDTH-1:0] addr);
        // Default address mapping (can be configured)
        // Slave 0: 0x0000_0000 - 0x3FFF_FFFF
        // Slave 1: 0x4000_0000 - 0x7FFF_FFFF
        // Slave 2: 0x8000_0000 - 0xBFFF_FFFF
        // Slave 3: 0xC000_0000 - 0xFFFF_FFFF
        
        if (NUM_SLAVES == 1) return 0;
        
        case (addr[31:30])
            2'b00: return 0;
            2'b01: return (NUM_SLAVES > 1) ? 1 : 0;
            2'b10: return (NUM_SLAVES > 2) ? 2 : 0;
            2'b11: return (NUM_SLAVES > 3) ? 3 : 0;
            default: return 0;
        endcase
    endfunction
    
    // Simple round-robin arbitration for each slave
    logic [3:0] slave_grant[NUM_SLAVES];
    logic [3:0] slave_request[NUM_SLAVES];
    
    // Write address channel routing
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            for (int s = 0; s < NUM_SLAVES; s++) begin
                slave_if[s].awvalid <= 1'b0;
                slave_grant[s] <= '0;
            end
        end else begin
            // Route write addresses to appropriate slaves
            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (master_if[m].awvalid && !master_if[m].awready) begin
                    int slave_idx = decode_slave_index(master_if[m].awaddr);
                    if (slave_idx < NUM_SLAVES) begin
                        // Simple forwarding (no arbitration for behavioral model)
                        slave_if[slave_idx].awid <= master_if[m].awid;
                        slave_if[slave_idx].awaddr <= master_if[m].awaddr;
                        slave_if[slave_idx].awlen <= master_if[m].awlen;
                        slave_if[slave_idx].awsize <= master_if[m].awsize;
                        slave_if[slave_idx].awburst <= master_if[m].awburst;
                        slave_if[slave_idx].awlock <= master_if[m].awlock;
                        slave_if[slave_idx].awcache <= master_if[m].awcache;
                        slave_if[slave_idx].awprot <= master_if[m].awprot;
                        slave_if[slave_idx].awqos <= master_if[m].awqos;
                        slave_if[slave_idx].awregion <= master_if[m].awregion;
                        slave_if[slave_idx].awuser <= master_if[m].awuser;
                        slave_if[slave_idx].awvalid <= 1'b1;
                        
                        // Connect ready back
                        master_if[m].awready <= slave_if[slave_idx].awready;
                    end
                end
            end
        end
    end
    
    // Write data channel routing
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            for (int s = 0; s < NUM_SLAVES; s++) begin
                slave_if[s].wvalid <= 1'b0;
            end
        end else begin
            // Route write data based on outstanding AW transactions
            // Simplified: assumes in-order data follows address
            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (master_if[m].wvalid && !master_if[m].wready) begin
                    // Find matching slave based on previous AW
                    for (int s = 0; s < NUM_SLAVES; s++) begin
                        // Simple forwarding
                        slave_if[s].wdata <= master_if[m].wdata;
                        slave_if[s].wstrb <= master_if[m].wstrb;
                        slave_if[s].wlast <= master_if[m].wlast;
                        slave_if[s].wuser <= master_if[m].wuser;
                        slave_if[s].wvalid <= master_if[m].wvalid;
                        
                        master_if[m].wready <= slave_if[s].wready;
                    end
                end
            end
        end
    end
    
    // Write response channel routing
    always_comb begin
        // Default values
        for (int m = 0; m < NUM_MASTERS; m++) begin
            master_if[m].bvalid = 1'b0;
            master_if[m].bid = '0;
            master_if[m].bresp = 2'b00;
            master_if[m].buser = '0;
        end
        
        // Route responses back to masters
        for (int s = 0; s < NUM_SLAVES; s++) begin
            if (slave_if[s].bvalid) begin
                // Find matching master based on ID
                for (int m = 0; m < NUM_MASTERS; m++) begin
                    // Simplified: route to first master
                    master_if[m].bvalid = slave_if[s].bvalid;
                    master_if[m].bid = slave_if[s].bid;
                    master_if[m].bresp = slave_if[s].bresp;
                    master_if[m].buser = slave_if[s].buser;
                    
                    slave_if[s].bready = master_if[m].bready;
                    break;
                end
            end
        end
    end
    
    // Read address channel routing
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            for (int s = 0; s < NUM_SLAVES; s++) begin
                slave_if[s].arvalid <= 1'b0;
            end
        end else begin
            // Route read addresses to appropriate slaves
            for (int m = 0; m < NUM_MASTERS; m++) begin
                if (master_if[m].arvalid && !master_if[m].arready) begin
                    int slave_idx = decode_slave_index(master_if[m].araddr);
                    if (slave_idx < NUM_SLAVES) begin
                        // Forward to slave
                        slave_if[slave_idx].arid <= master_if[m].arid;
                        slave_if[slave_idx].araddr <= master_if[m].araddr;
                        slave_if[slave_idx].arlen <= master_if[m].arlen;
                        slave_if[slave_idx].arsize <= master_if[m].arsize;
                        slave_if[slave_idx].arburst <= master_if[m].arburst;
                        slave_if[slave_idx].arlock <= master_if[m].arlock;
                        slave_if[slave_idx].arcache <= master_if[m].arcache;
                        slave_if[slave_idx].arprot <= master_if[m].arprot;
                        slave_if[slave_idx].arqos <= master_if[m].arqos;
                        slave_if[slave_idx].arregion <= master_if[m].arregion;
                        slave_if[slave_idx].aruser <= master_if[m].aruser;
                        slave_if[slave_idx].arvalid <= 1'b1;
                        
                        master_if[m].arready <= slave_if[slave_idx].arready;
                    end
                end
            end
        end
    end
    
    // Read data channel routing
    always_comb begin
        // Default values
        for (int m = 0; m < NUM_MASTERS; m++) begin
            master_if[m].rvalid = 1'b0;
            master_if[m].rid = '0;
            master_if[m].rdata = '0;
            master_if[m].rresp = 2'b00;
            master_if[m].rlast = 1'b0;
            master_if[m].ruser = '0;
        end
        
        // Route read data back to masters
        for (int s = 0; s < NUM_SLAVES; s++) begin
            if (slave_if[s].rvalid) begin
                // Find matching master based on ID
                for (int m = 0; m < NUM_MASTERS; m++) begin
                    // Simplified: route to first master
                    master_if[m].rvalid = slave_if[s].rvalid;
                    master_if[m].rid = slave_if[s].rid;
                    master_if[m].rdata = slave_if[s].rdata;
                    master_if[m].rresp = slave_if[s].rresp;
                    master_if[m].rlast = slave_if[s].rlast;
                    master_if[m].ruser = slave_if[s].ruser;
                    
                    slave_if[s].rready = master_if[m].rready;
                    break;
                end
            end
        end
    end
    
endmodule : behavioral_axi4_interconnect

`endif // AXI4_RTL_WRAPPER_SV