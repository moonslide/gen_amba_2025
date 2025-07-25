//==============================================================================
// AXI4 Address Decoder with Access Control
// Maps addresses to slave select signals and checks permissions
//==============================================================================

module axi4_address_decoder #(
    parameter ADDR_WIDTH = 32,
    parameter NUM_SLAVES = 3,
    parameter NUM_MASTERS = 2
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
    // DDR permissions
    slave_permissions[0] = {2{1'b1}}; // All masters allowed (default)
    // SecureRAM permissions
    slave_permissions[1] = {2{1'b1}}; // All masters allowed (default)
    // Peripherals permissions
    slave_permissions[2] = {2{1'b1}}; // All masters allowed (default)
end

always @(*) begin
    slave_select = {NUM_SLAVES{1'b0}};
    access_error = 1'b0;
    
    if (awvalid || arvalid) begin
        case (1'b1)
            // DDR: 0x80000000 - 0x8FFFFFFF
            (awvalid ? awaddr : araddr) >= 32'h80000000 && (awvalid ? awaddr : araddr) <= 32'h8FFFFFFF: begin
                if (slave_permissions[0][master_id]) begin
                    slave_select[0] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // SecureRAM: 0x90000000 - 0x93FFFFFF
            (awvalid ? awaddr : araddr) >= 32'h90000000 && (awvalid ? awaddr : araddr) <= 32'h93FFFFFF: begin
                if (slave_permissions[1][master_id]) begin
                    // Security checks
                    if (((awvalid ? awprot[1] : arprot[1]) == 1'b0) && ((awvalid ? awprot[0] : arprot[0]) == 1'b1)) begin
                        slave_select[1] = 1'b1;
                    end else begin
                        access_error = 1'b1; // Security violation
                    end
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // Peripherals: 0xA0000000 - 0xA00FFFFF
            (awvalid ? awaddr : araddr) >= 32'hA0000000 && (awvalid ? awaddr : araddr) <= 32'hA00FFFFF: begin
                if (slave_permissions[2][master_id]) begin
                    slave_select[2] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            default: slave_select = {NUM_SLAVES{1'b0}}; // No slave selected
        endcase
    end
end

endmodule
