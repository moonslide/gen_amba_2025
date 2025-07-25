//==============================================================================
// AXI4 Address Decoder with Access Control
// Maps addresses to slave select signals and checks permissions
//==============================================================================

module axi4_address_decoder #(
    parameter ADDR_WIDTH = 32,
    parameter NUM_SLAVES = 8,
    parameter NUM_MASTERS = 8
)(
    input  wire [ADDR_WIDTH-1:0] awaddr,
    input  wire                  awvalid,
    input  wire [2:0]            awprot,   // Protection attributes
    input  wire [ADDR_WIDTH-1:0] araddr,
    input  wire                  arvalid,
    input  wire [2:0]            arprot,   // Protection attributes
    input  wire [$clog2(NUM_MASTERS)-1:0] master_id,  // Current master ID
    output reg  [NUM_SLAVES-1:0] slave_select,
    output reg                   access_error  // Permission denied
);

// Permission matrix - which masters can access which slaves
reg [NUM_MASTERS-1:0] slave_permissions [0:NUM_SLAVES-1];

initial begin
    // DDR4_Channel_0 permissions
    slave_permissions[0] = {8{1'b1}}; // All masters allowed (default)
    // DDR4_Channel_1 permissions
    slave_permissions[1] = {8{1'b1}}; // All masters allowed (default)
    // L3_Cache_SRAM permissions
    slave_permissions[2] = {8{1'b1}}; // All masters allowed (default)
    // Boot_ROM permissions
    slave_permissions[3] = {8{1'b1}}; // All masters allowed (default)
    // System_Registers permissions
    slave_permissions[4] = {8{1'b1}}; // All masters allowed (default)
    // PCIe_Config_Space permissions
    slave_permissions[5] = {8{1'b1}}; // All masters allowed (default)
    // Crypto_Engine permissions
    slave_permissions[6] = {8{1'b1}}; // All masters allowed (default)
    // Debug_APB_Bridge permissions
    slave_permissions[7] = {8{1'b1}}; // All masters allowed (default)
end

always @(*) begin
    slave_select = {NUM_SLAVES{1'b0}};
    access_error = 1'b0;
    
    if (awvalid || arvalid) begin
        case (1'b1)
            // DDR4_Channel_0: 0x0000000000 - 0x01FFFFFFFF
            (awvalid ? awaddr : araddr) >= 40'h0 && (awvalid ? awaddr : araddr) <= 40'h1FFFFFFFF: begin
                if (slave_permissions[0][master_id]) begin
                    slave_select[0] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // DDR4_Channel_1: 0x0200000000 - 0x03FFFFFFFF
            (awvalid ? awaddr : araddr) >= 40'h200000000 && (awvalid ? awaddr : araddr) <= 40'h3FFFFFFFF: begin
                if (slave_permissions[1][master_id]) begin
                    slave_select[1] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // L3_Cache_SRAM: 0x0400000000 - 0x0400FFFFFF
            (awvalid ? awaddr : araddr) >= 40'h400000000 && (awvalid ? awaddr : araddr) <= 40'h400FFFFFF: begin
                if (slave_permissions[2][master_id]) begin
                    slave_select[2] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // Boot_ROM: 0x1000000000 - 0x100003FFFF
            (awvalid ? awaddr : araddr) >= 40'h1000000000 && (awvalid ? awaddr : araddr) <= 40'h100003FFFF: begin
                if (slave_permissions[3][master_id]) begin
                    slave_select[3] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // System_Registers: 0x2000000000 - 0x200000FFFF
            (awvalid ? awaddr : araddr) >= 40'h2000000000 && (awvalid ? awaddr : araddr) <= 40'h200000FFFF: begin
                if (slave_permissions[4][master_id]) begin
                    // Security checks
                    if (((awvalid ? awprot[0] : arprot[0]) == 1'b1)) begin
                        slave_select[4] = 1'b1;
                    end else begin
                        access_error = 1'b1; // Security violation
                    end
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // PCIe_Config_Space: 0x4000000000 - 0x4003FFFFFF
            (awvalid ? awaddr : araddr) >= 40'h4000000000 && (awvalid ? awaddr : araddr) <= 40'h4003FFFFFF: begin
                if (slave_permissions[5][master_id]) begin
                    slave_select[5] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // Crypto_Engine: 0x8000000000 - 0x800003FFFF
            (awvalid ? awaddr : araddr) >= 40'h8000000000 && (awvalid ? awaddr : araddr) <= 40'h800003FFFF: begin
                if (slave_permissions[6][master_id]) begin
                    // Security checks
                    if (((awvalid ? awprot[1] : arprot[1]) == 1'b0) && ((awvalid ? awprot[0] : arprot[0]) == 1'b1)) begin
                        slave_select[6] = 1'b1;
                    end else begin
                        access_error = 1'b1; // Security violation
                    end
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // Debug_APB_Bridge: 0x10000000000 - 0x100000FFFFF
            (awvalid ? awaddr : araddr) >= 40'h10000000000 && (awvalid ? awaddr : araddr) <= 40'h100000FFFFF: begin
                if (slave_permissions[7][master_id]) begin
                    // Security checks
                    if (((awvalid ? awprot[0] : arprot[0]) == 1'b1)) begin
                        slave_select[7] = 1'b1;
                    end else begin
                        access_error = 1'b1; // Security violation
                    end
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            default: slave_select = {NUM_SLAVES{1'b0}}; // No slave selected
        endcase
    end
end

endmodule
