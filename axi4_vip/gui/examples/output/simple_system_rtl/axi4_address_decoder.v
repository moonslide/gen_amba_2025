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
    // RAM permissions
    slave_permissions[0] = {2{1'b1}}; // All masters allowed (default)
    // ROM permissions
    slave_permissions[1] = {2{1'b1}}; // All masters allowed (default)
    // UART permissions
    slave_permissions[2] = {2{1'b1}}; // All masters allowed (default)
end

always @(*) begin
    slave_select = {NUM_SLAVES{1'b0}};
    access_error = 1'b0;
    
    if (awvalid || arvalid) begin
        case (1'b1)
            // RAM: 0x00000000 - 0x3FFFFFFF
            (awvalid ? awaddr : araddr) >= 32'h0 && (awvalid ? awaddr : araddr) <= 32'h3FFFFFFF: begin
                if (slave_permissions[0][master_id]) begin
                    slave_select[0] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // ROM: 0x10000000 - 0x13FFFFFF
            (awvalid ? awaddr : araddr) >= 32'h10000000 && (awvalid ? awaddr : araddr) <= 32'h13FFFFFF: begin
                if (slave_permissions[1][master_id]) begin
                    slave_select[1] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // UART: 0x20000000 - 0x20000FFF
            (awvalid ? awaddr : araddr) >= 32'h20000000 && (awvalid ? awaddr : araddr) <= 32'h20000FFF: begin
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
