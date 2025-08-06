// AXI4 Slave Driver BFM with detailed logging
module axi4_slave_driver_bfm #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int ID_WIDTH = 4,
    parameter int USER_WIDTH = 1
)(
    input logic aclk,
    input logic aresetn,
    axi4_if.slave axi_if
);


    import axi4_globals_pkg::*;
    import uvm_pkg::*;
    initial begin
        `ifdef UVM_HDL_NO_DPI
            `uvm_info("AXI_SLAVE_DRIVER_BFM", "UVM_HDL_NO_DPI defined, using stub BFM", UVM_LOW)
        `else
            `uvm_info("AXI_SLAVE_DRIVER_BFM", "Slave BFM signals initialized", UVM_LOW)
        `endif
    end

    // Signal initialization to avoid X
    initial begin
        axi_if.awready = 1'b1;
        axi_if.wready = 1'b1;
        axi_if.bvalid = 1'b0;
        axi_if.arready = 1'b1;
        axi_if.rvalid = 1'b0;
    end

endmodule
