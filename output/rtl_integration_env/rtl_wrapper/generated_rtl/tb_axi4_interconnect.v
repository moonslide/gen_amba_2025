//==============================================================================
// Testbench for AXI4 Interconnect
//==============================================================================

`timescale 1ns/1ps

module tb_axi4_interconnect;

parameter DATA_WIDTH = 64;
parameter ADDR_WIDTH = 32;

reg aclk;
reg aresetn;

// Clock generation
initial begin
    aclk = 0;
    forever #5 aclk = ~aclk;
end

// Reset generation
initial begin
    aresetn = 0;
    #100;
    aresetn = 1;
end

// DUT instantiation
axi4_interconnect_m2s3 #(
    .DATA_WIDTH(DATA_WIDTH),
    .ADDR_WIDTH(ADDR_WIDTH)
) dut (
    .aclk(aclk),
    .aresetn(aresetn)
    // Connect all interfaces
);

// Test sequences
initial begin
    $dumpfile("axi4_interconnect.vcd");
    $dumpvars(0, tb_axi4_interconnect);
    
    // Wait for reset
    @(posedge aresetn);
    repeat(10) @(posedge aclk);
    
    // Test 1: Basic write transaction
    $display("Test 1: Basic write transaction");
    
    // Test 2: Basic read transaction
    $display("Test 2: Basic read transaction");
    
    // Test 3: 4KB boundary test
    $display("Test 3: 4KB boundary test");
    
    // Test 4: Access permission test
    $display("Test 4: Access permission test");
    
    // Test 5: QoS arbitration test
    $display("Test 5: QoS arbitration test");
    
    #1000;
    $finish;
end

endmodule
