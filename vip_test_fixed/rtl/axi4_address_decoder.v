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
    // slave0 permissions
    slave_permissions[0] = {8{1'b1}}; // All masters allowed (default)
    // slave1 permissions
    slave_permissions[1] = {8{1'b1}}; // All masters allowed (default)
    // slave2 permissions
    slave_permissions[2] = {8{1'b1}}; // All masters allowed (default)
    // slave3 permissions
    slave_permissions[3] = {8{1'b1}}; // All masters allowed (default)
    // slave4 permissions
    slave_permissions[4] = {8{1'b1}}; // All masters allowed (default)
    // slave5 permissions
    slave_permissions[5] = {8{1'b1}}; // All masters allowed (default)
    // slave6 permissions
    slave_permissions[6] = {8{1'b1}}; // All masters allowed (default)
    // slave7 permissions
    slave_permissions[7] = {8{1'b1}}; // All masters allowed (default)
end

always @(*) begin
    slave_select = {NUM_SLAVES{1'b0}};
    access_error = 1'b0;
    
    if (awvalid || arvalid) begin
        case (1'b1)
            // slave0: 0x00000000 - 0x0FFFFFFF
            (awvalid ? awaddr : araddr) >= 32'h0 && (awvalid ? awaddr : araddr) <= 32'hFFFFFFF: begin
                if (slave_permissions[0][master_id]) begin
                    slave_select[0] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // slave1: 0x10000000 - 0x1FFFFFFF
            (awvalid ? awaddr : araddr) >= 32'h10000000 && (awvalid ? awaddr : araddr) <= 32'h1FFFFFFF: begin
                if (slave_permissions[1][master_id]) begin
                    slave_select[1] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // slave2: 0x20000000 - 0x2FFFFFFF
            (awvalid ? awaddr : araddr) >= 32'h20000000 && (awvalid ? awaddr : araddr) <= 32'h2FFFFFFF: begin
                if (slave_permissions[2][master_id]) begin
                    slave_select[2] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // slave3: 0x30000000 - 0x3FFFFFFF
            (awvalid ? awaddr : araddr) >= 32'h30000000 && (awvalid ? awaddr : araddr) <= 32'h3FFFFFFF: begin
                if (slave_permissions[3][master_id]) begin
                    slave_select[3] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // slave4: 0x40000000 - 0x4FFFFFFF
            (awvalid ? awaddr : araddr) >= 32'h40000000 && (awvalid ? awaddr : araddr) <= 32'h4FFFFFFF: begin
                if (slave_permissions[4][master_id]) begin
                    slave_select[4] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // slave5: 0x50000000 - 0x5FFFFFFF
            (awvalid ? awaddr : araddr) >= 32'h50000000 && (awvalid ? awaddr : araddr) <= 32'h5FFFFFFF: begin
                if (slave_permissions[5][master_id]) begin
                    slave_select[5] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // slave6: 0x60000000 - 0x6FFFFFFF
            (awvalid ? awaddr : araddr) >= 32'h60000000 && (awvalid ? awaddr : araddr) <= 32'h6FFFFFFF: begin
                if (slave_permissions[6][master_id]) begin
                    slave_select[6] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            // slave7: 0x70000000 - 0x7FFFFFFF
            (awvalid ? awaddr : araddr) >= 32'h70000000 && (awvalid ? awaddr : araddr) <= 32'h7FFFFFFF: begin
                if (slave_permissions[7][master_id]) begin
                    slave_select[7] = 1'b1;
                end else begin
                    access_error = 1'b1; // Permission denied
                end
            end
            default: slave_select = {NUM_SLAVES{1'b0}}; // No slave selected
        endcase
    end
end

endmodule
