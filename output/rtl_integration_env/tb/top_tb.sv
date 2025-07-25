`timescale 1ns/1ps

import axi4_globals_pkg::*;
import axi4_master_pkg::*;
import axi4_slave_pkg::*;
import axi4_master_seq_pkg::*;
import axi4_slave_seq_pkg::*;
import axi4_env_pkg::*;
import axi4_test_pkg::*;
import uvm_pkg::*;

module top_tb;

    // Clock and reset
    logic clk;
    logic rst_n;
    
    // Clock generation
    initial clk = 0;
    always #5 clk = ~clk;
    
    // Reset generation
    initial begin
        rst_n = 0;
        repeat(10) @(posedge clk);
        rst_n = 1;
    end
    
    // AXI4 interface instance from tim_axi4_vip
    axi4_if #(
        .AXI4_ADDRESS_WIDTH(32),
        .AXI4_RDATA_WIDTH(64),
        .AXI4_WDATA_WIDTH(64),
        .AXI4_ID_WIDTH(4),
        .AXI4_USER_WIDTH(1)
    ) dut_if (
        .clk(clk),
        .resetn(rst_n)
    );
    
    // Master and Slave BFM instantiation
    axi4_master_agent_bfm #(.MASTER_ID(0)) master_bfm(dut_if);
    axi4_slave_agent_bfm #(.SLAVE_ID(0)) slave_bfm(dut_if);
    
    // DUT wrapper instantiation
    dut_wrapper #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(64),
        .ID_WIDTH(4)
    ) dut_inst (
        .clk(clk),
        .rst_n(rst_n),
        .axi_if(dut_if)
    );
    
    // UVM test harness
    initial begin
        // Configure number of masters and slaves
        uvm_config_db#(int)::set(null, "*", "no_of_masters", 2);
        uvm_config_db#(int)::set(null, "*", "no_of_slaves", 3);
        
        // Register interface with UVM config DB
        uvm_config_db#(virtual axi4_if)::set(null, "*", "vif", dut_if);
        
        // Register BFMs
        uvm_config_db#(axi4_master_agent_bfm)::set(null, "*master_agent*", "master_agent_bfm", master_bfm);
        uvm_config_db#(axi4_slave_agent_bfm)::set(null, "*slave_agent*", "slave_agent_bfm", slave_bfm);
        
        // Run UVM test
        run_test();
    end
    
endmodule
