//==============================================================================
// AXI4 VIP Testbench Top Module
// Top-level testbench that instantiates interface, DUT, and runs UVM tests
//==============================================================================

`timescale 1ns/1ps

module axi4_tb_top;
    
    // Clock and reset generation
    logic aclk;
    logic aresetn;
    
    // Clock generation - 100MHz (10ns period)
    initial begin
        aclk = 0;
        forever #5 aclk = ~aclk;
    end
    
    // Reset generation
    initial begin
        aresetn = 0;
        #50;
        aresetn = 1;
        `uvm_info("TB_TOP", "Reset released", UVM_MEDIUM)
    end
    
    // AXI4 interface instantiation
    axi4_if #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(64),
        .ID_WIDTH(4),
        .USER_WIDTH(1)
    ) axi4_if_inst (
        .aclk(aclk),
        .aresetn(aresetn)
    );
    
    // VIP Mode selection
    string vip_mode;
    string rtl_path;
    
    initial begin
        // Check VIP mode
        if (!$value$plusargs("VIP_MODE=%s", vip_mode)) begin
            vip_mode = "BEHAVIORAL"; // Default to behavioral model
        end
        
        `uvm_info("TB_TOP", $sformatf("VIP Mode: %s", vip_mode), UVM_LOW)
        
        if (vip_mode == "RTL") begin
            if ($value$plusargs("RTL_PATH=%s", rtl_path)) begin
                `uvm_info("TB_TOP", $sformatf("RTL Path: %s", rtl_path), UVM_LOW)
            end else begin
                `uvm_warning("TB_TOP", "VIP_MODE=RTL but no RTL_PATH specified, using behavioral model")
                vip_mode = "BEHAVIORAL";
            end
        end
    end
    
    // Read configuration parameters
    int num_masters = 2;
    int num_slaves = 3;
    
    initial begin
        // Get configuration from plusargs
        if ($value$plusargs("NUM_MASTERS=%d", num_masters)) begin
            `uvm_info("TB_TOP", $sformatf("Number of Masters: %0d", num_masters), UVM_LOW)
        end
        if ($value$plusargs("NUM_SLAVES=%d", num_slaves)) begin
            `uvm_info("TB_TOP", $sformatf("Number of Slaves: %0d", num_slaves), UVM_LOW)
        end
    end
    
    // Master and slave interfaces
    axi4_if #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(64),
        .ID_WIDTH(4),
        .USER_WIDTH(1)
    ) master_if[num_masters] (
        .aclk(aclk),
        .aresetn(aresetn)
    );
    
    axi4_if #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(64),
        .ID_WIDTH(4),
        .USER_WIDTH(1)
    ) slave_if[num_slaves] (
        .aclk(aclk),
        .aresetn(aresetn)
    );
    
    // DUT selection based on VIP mode
    generate
        if (1) begin : dut_selection
            // Instantiate RTL wrapper (supports both behavioral and RTL modes)
            axi4_rtl_wrapper #(
                .NUM_MASTERS(num_masters),
                .NUM_SLAVES(num_slaves),
                .ADDR_WIDTH(32),
                .DATA_WIDTH(64),
                .ID_WIDTH(4),
                .USER_WIDTH(1)
            ) dut (
                .aclk(aclk),
                .aresetn(aresetn),
                .master_if(master_if),
                .slave_if(slave_if)
            );
            
            // Simple memory models for slaves
            for (genvar i = 0; i < num_slaves; i++) begin : slave_memory
                axi4_memory_model #(
                    .ADDR_WIDTH(32),
                    .DATA_WIDTH(64),
                    .ID_WIDTH(4),
                    .USER_WIDTH(1),
                    .MEMORY_SIZE(256*1024) // 256KB per slave
                ) slave_mem (
                    .axi4_if(slave_if[i].slave)
                );
            end
        end
    endgenerate
    
    // UVM test runner
    initial begin
        // Set interfaces in config DB
        for (int i = 0; i < num_masters; i++) begin
            uvm_config_db#(virtual axi4_if)::set(null, $sformatf("*master_agent[%0d]*", i), "vif", master_if[i]);
        end
        for (int i = 0; i < num_slaves; i++) begin
            uvm_config_db#(virtual axi4_if)::set(null, $sformatf("*slave_agent[%0d]*", i), "vif", slave_if[i]);
        end
        
        // Set main interface for backward compatibility
        uvm_config_db#(virtual axi4_if)::set(null, "*", "vif", master_if[0]);
        
        // Set verbosity level
        uvm_top.set_report_verbosity_level_hier(UVM_MEDIUM);
        
        // Enable UVM command line processor
        uvm_cmdline_processor clp = uvm_cmdline_processor::get_inst();
        
        // Print test information
        `uvm_info("TB_TOP", "========================================", UVM_LOW)
        `uvm_info("TB_TOP", "    AXI4 VIP Comprehensive TestBench   ", UVM_LOW)
        `uvm_info("TB_TOP", "========================================", UVM_LOW)
        `uvm_info("TB_TOP", $sformatf("AXI4 Interface Configuration:"), UVM_LOW)
        `uvm_info("TB_TOP", $sformatf("  Address Width: %0d bits", 32), UVM_LOW)
        `uvm_info("TB_TOP", $sformatf("  Data Width: %0d bits", 64), UVM_LOW)
        `uvm_info("TB_TOP", $sformatf("  ID Width: %0d bits", 4), UVM_LOW)
        `uvm_info("TB_TOP", $sformatf("  User Width: %0d bits", 1), UVM_LOW)
        `uvm_info("TB_TOP", $sformatf("  Clock Period: 10ns (100MHz)"), UVM_LOW)
        `uvm_info("TB_TOP", "========================================", UVM_LOW)
        
        // Run the test
        run_test();
    end
    
    // Simulation control and monitoring
    initial begin
        // Dump waveforms if requested
        if ($test$plusargs("DUMP_VCD")) begin
            $dumpfile("axi4_vip_sim.vcd");
            $dumpvars(0, axi4_tb_top);
            `uvm_info("TB_TOP", "VCD dumping enabled", UVM_LOW)
        end
        
        if ($test$plusargs("DUMP_FSDB")) begin
            $fsdbDumpfile("axi4_vip_sim.fsdb");
            $fsdbDumpvars(0, axi4_tb_top);
            `uvm_info("TB_TOP", "FSDB dumping enabled", UVM_LOW)
        end
    end
    
    // Watchdog timer
    initial begin
        #10ms; // 10ms maximum simulation time
        `uvm_error("TB_TOP", "Simulation timeout - forcing finish")
        $finish;
    end
    
    // Protocol assertions binding
    bind axi4_if_inst axi4_protocol_assertions axi4_assertions_inst (
        .aclk(aclk),
        .aresetn(aresetn),
        .awvalid(awvalid),
        .awready(awready),
        .awid(awid),
        .awaddr(awaddr),
        .awlen(awlen),
        .awsize(awsize),
        .awburst(awburst),
        .wvalid(wvalid),
        .wready(wready),
        .wdata(wdata),
        .wstrb(wstrb),
        .wlast(wlast),
        .bvalid(bvalid),
        .bready(bready),
        .bid(bid),
        .bresp(bresp),
        .arvalid(arvalid),
        .arready(arready),
        .arid(arid),
        .araddr(araddr),
        .arlen(arlen),
        .arsize(arsize),
        .arburst(arburst),
        .rvalid(rvalid),
        .rready(rready),
        .rid(rid),
        .rdata(rdata),
        .rresp(rresp),
        .rlast(rlast)
    );
    
    // Final simulation summary
    final begin
        `uvm_info("TB_TOP", "========================================", UVM_LOW)
        `uvm_info("TB_TOP", "    AXI4 VIP Simulation Completed      ", UVM_LOW)
        `uvm_info("TB_TOP", "========================================", UVM_LOW)
    end
    
endmodule : axi4_tb_top


//==============================================================================
// Simple AXI4 Memory Model DUT for testing
//==============================================================================
module axi4_memory_model #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64,
    parameter int ID_WIDTH = 4,
    parameter int USER_WIDTH = 1,
    parameter int MEMORY_SIZE = 1024*1024 // 1MB default
) (
    axi4_if.slave axi4_if
);
    
    // Memory array
    logic [7:0] memory [0:MEMORY_SIZE-1];
    
    // Initialize memory with pattern
    initial begin
        for (int i = 0; i < MEMORY_SIZE; i++) begin
            memory[i] = i % 256;
        end
    end
    
    // Write address channel
    always_ff @(posedge axi4_if.aclk or negedge axi4_if.aresetn) begin
        if (!axi4_if.aresetn) begin
            axi4_if.awready <= 1'b0;
        end else begin
            // Simple ready generation
            axi4_if.awready <= axi4_if.awvalid;
        end
    end
    
    // Write data channel
    always_ff @(posedge axi4_if.aclk or negedge axi4_if.aresetn) begin
        if (!axi4_if.aresetn) begin
            axi4_if.wready <= 1'b0;
        end else begin
            // Simple ready generation
            axi4_if.wready <= axi4_if.wvalid;
        end
    end
    
    // Write response channel
    logic [ID_WIDTH-1:0] bid_reg;
    logic bvalid_reg;
    
    always_ff @(posedge axi4_if.aclk or negedge axi4_if.aresetn) begin
        if (!axi4_if.aresetn) begin
            axi4_if.bvalid <= 1'b0;
            axi4_if.bid <= '0;
            axi4_if.bresp <= 2'b00;
            axi4_if.buser <= '0;
        end else begin
            // Generate write response after data phase
            if (axi4_if.wvalid && axi4_if.wready && axi4_if.wlast) begin
                axi4_if.bvalid <= 1'b1;
                axi4_if.bid <= axi4_if.awid; // Simplified - should track properly
                axi4_if.bresp <= 2'b00; // OKAY response
            end else if (axi4_if.bvalid && axi4_if.bready) begin
                axi4_if.bvalid <= 1'b0;
            end
        end
    end
    
    // Read address channel
    always_ff @(posedge axi4_if.aclk or negedge axi4_if.aresetn) begin
        if (!axi4_if.aresetn) begin
            axi4_if.arready <= 1'b0;
        end else begin
            // Simple ready generation
            axi4_if.arready <= axi4_if.arvalid;
        end
    end
    
    // Read data channel
    logic [ID_WIDTH-1:0] rid_reg;
    logic [7:0] rlen_reg;
    logic [7:0] rbeat_count;
    logic ractive;
    
    always_ff @(posedge axi4_if.aclk or negedge axi4_if.aresetn) begin
        if (!axi4_if.aresetn) begin
            axi4_if.rvalid <= 1'b0;
            axi4_if.rid <= '0;
            axi4_if.rdata <= '0;
            axi4_if.rresp <= 2'b00;
            axi4_if.rlast <= 1'b0;
            axi4_if.ruser <= '0;
            ractive <= 1'b0;
            rbeat_count <= 0;
        end else begin
            // Start read transaction
            if (axi4_if.arvalid && axi4_if.arready && !ractive) begin
                rid_reg <= axi4_if.arid;
                rlen_reg <= axi4_if.arlen;
                rbeat_count <= 0;
                ractive <= 1'b1;
                axi4_if.rvalid <= 1'b1;
                axi4_if.rid <= axi4_if.arid;
                axi4_if.rdata <= {DATA_WIDTH{1'b0}}; // Simplified data
                axi4_if.rresp <= 2'b00; // OKAY
                axi4_if.rlast <= (axi4_if.arlen == 0);
            end
            // Continue read beats
            else if (ractive && axi4_if.rvalid && axi4_if.rready) begin
                if (rbeat_count == rlen_reg) begin
                    // Last beat completed
                    ractive <= 1'b0;
                    axi4_if.rvalid <= 1'b0;
                    axi4_if.rlast <= 1'b0;
                end else begin
                    // Next beat
                    rbeat_count <= rbeat_count + 1;
                    axi4_if.rlast <= (rbeat_count + 1 == rlen_reg);
                end
            end
        end
    end
    
endmodule : axi4_memory_model


//==============================================================================
// AXI4 Protocol Assertions Module
//==============================================================================
module axi4_protocol_assertions #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64,
    parameter int ID_WIDTH = 4
) (
    input logic aclk,
    input logic aresetn,
    
    // Write address channel
    input logic awvalid,
    input logic awready,
    input logic [ID_WIDTH-1:0] awid,
    input logic [ADDR_WIDTH-1:0] awaddr,
    input logic [7:0] awlen,
    input logic [2:0] awsize,
    input logic [1:0] awburst,
    
    // Write data channel
    input logic wvalid,
    input logic wready,
    input logic [DATA_WIDTH-1:0] wdata,
    input logic [DATA_WIDTH/8-1:0] wstrb,
    input logic wlast,
    
    // Write response channel
    input logic bvalid,
    input logic bready,
    input logic [ID_WIDTH-1:0] bid,
    input logic [1:0] bresp,
    
    // Read address channel
    input logic arvalid,
    input logic arready,
    input logic [ID_WIDTH-1:0] arid,
    input logic [ADDR_WIDTH-1:0] araddr,
    input logic [7:0] arlen,
    input logic [2:0] arsize,
    input logic [1:0] arburst,
    
    // Read data channel
    input logic rvalid,
    input logic rready,
    input logic [ID_WIDTH-1:0] rid,
    input logic [DATA_WIDTH-1:0] rdata,
    input logic [1:0] rresp,
    input logic rlast
);
    
    // Write address channel assertions
    property awvalid_stable;
        @(posedge aclk) disable iff (!aresetn)
        $rose(awvalid) |=> awvalid throughout (awvalid && !awready)[*0:$] ##1 awready;
    endproperty
    
    property awaddr_stable_during_valid;
        @(posedge aclk) disable iff (!aresetn)
        awvalid && !awready |=> $stable({awid, awaddr, awlen, awsize, awburst});
    endproperty
    
    // Write data channel assertions
    property wvalid_stable;
        @(posedge aclk) disable iff (!aresetn)
        $rose(wvalid) |=> wvalid throughout (wvalid && !wready)[*0:$] ##1 wready;
    endproperty
    
    property wdata_stable_during_valid;
        @(posedge aclk) disable iff (!aresetn)
        wvalid && !wready |=> $stable({wdata, wstrb, wlast});
    endproperty
    
    // Read address channel assertions
    property arvalid_stable;
        @(posedge aclk) disable iff (!aresetn)
        $rose(arvalid) |=> arvalid throughout (arvalid && !arready)[*0:$] ##1 arready;
    endproperty
    
    property araddr_stable_during_valid;
        @(posedge aclk) disable iff (!aresetn)
        arvalid && !arready |=> $stable({arid, araddr, arlen, arsize, arburst});
    endproperty
    
    // Read data channel assertions
    property rvalid_stable;
        @(posedge aclk) disable iff (!aresetn)
        $rose(rvalid) |=> rvalid throughout (rvalid && !rready)[*0:$] ##1 rready;
    endproperty
    
    property rdata_stable_during_valid;
        @(posedge aclk) disable iff (!aresetn)
        rvalid && !rready |=> $stable({rid, rdata, rresp, rlast});
    endproperty
    
    // Bind assertions
    assert_awvalid_stable: assert property (awvalid_stable)
        else $error("AXI4 Protocol Violation: AWVALID not stable during handshake");
    
    assert_awaddr_stable: assert property (awaddr_stable_during_valid)
        else $error("AXI4 Protocol Violation: AW signals not stable during AWVALID");
    
    assert_wvalid_stable: assert property (wvalid_stable)
        else $error("AXI4 Protocol Violation: WVALID not stable during handshake");
    
    assert_wdata_stable: assert property (wdata_stable_during_valid)
        else $error("AXI4 Protocol Violation: W signals not stable during WVALID");
    
    assert_arvalid_stable: assert property (arvalid_stable)
        else $error("AXI4 Protocol Violation: ARVALID not stable during handshake");
    
    assert_araddr_stable: assert property (araddr_stable_during_valid)
        else $error("AXI4 Protocol Violation: AR signals not stable during ARVALID");
    
    assert_rvalid_stable: assert property (rvalid_stable)
        else $error("AXI4 Protocol Violation: RVALID not stable during handshake");
    
    assert_rdata_stable: assert property (rdata_stable_during_valid)
        else $error("AXI4 Protocol Violation: R signals not stable during RVALID");
    
endmodule : axi4_protocol_assertions