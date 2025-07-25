//==============================================================================
// AXI4 Exclusive Access Monitor
// 
// Description: Monitors and manages exclusive access operations
// Tracks exclusive read addresses per ID and validates exclusive writes
//==============================================================================

`include "axi4_defines.sv"

module axi4_exclusive_monitor #(
    parameter int ADDR_WIDTH = 32,
    parameter int ID_WIDTH   = 4,
    parameter int NUM_IDS    = 2**ID_WIDTH,
    parameter int DATA_WIDTH = 64
)(
    input logic                    clk,
    input logic                    rst_n,
    
    // Exclusive read tracking
    input logic                    exclusive_read_req,
    input logic [ID_WIDTH-1:0]     exclusive_read_id,
    input logic [ADDR_WIDTH-1:0]   exclusive_read_addr,
    input logic [2:0]              exclusive_read_size,
    input logic [7:0]              exclusive_read_len,
    
    // Write monitoring (any write clears exclusive state)
    input logic                    write_req,
    input logic [ADDR_WIDTH-1:0]   write_addr,
    input logic [2:0]              write_size,
    input logic [7:0]              write_len,
    
    // Exclusive write checking
    input logic                    exclusive_write_req,
    input logic [ID_WIDTH-1:0]     exclusive_write_id,
    input logic [ADDR_WIDTH-1:0]   exclusive_write_addr,
    input logic [2:0]              exclusive_write_size,
    input logic [7:0]              exclusive_write_len,
    output logic                   exclusive_write_pass
);

    // Storage for exclusive access tracking
    typedef struct packed {
        logic                    valid;
        logic [ADDR_WIDTH-1:0]   addr;
        logic [ADDR_WIDTH-1:0]   addr_mask;  // Based on size
        logic [2:0]              size;
        logic [7:0]              len;
    } exclusive_entry_t;
    
    exclusive_entry_t exclusive_table[NUM_IDS];
    
    // Calculate address mask based on size
    function automatic logic [ADDR_WIDTH-1:0] calc_addr_mask(input logic [2:0] size);
        case (size)
            3'b000: return {{ADDR_WIDTH-1{1'b1}}, 1'b0};      // 1 byte
            3'b001: return {{ADDR_WIDTH-2{1'b1}}, 2'b00};     // 2 bytes
            3'b010: return {{ADDR_WIDTH-3{1'b1}}, 3'b000};    // 4 bytes
            3'b011: return {{ADDR_WIDTH-4{1'b1}}, 4'b0000};   // 8 bytes
            3'b100: return {{ADDR_WIDTH-5{1'b1}}, 5'b00000};  // 16 bytes
            3'b101: return {{ADDR_WIDTH-6{1'b1}}, 6'b000000}; // 32 bytes
            3'b110: return {{ADDR_WIDTH-7{1'b1}}, 7'b0000000};// 64 bytes
            3'b111: return {{ADDR_WIDTH-8{1'b1}}, 8'b00000000};//128 bytes
            default: return {ADDR_WIDTH{1'b1}};
        endcase
    endfunction
    
    // Check if addresses overlap
    function automatic logic addrs_overlap(
        input logic [ADDR_WIDTH-1:0] addr1,
        input logic [2:0] size1,
        input logic [7:0] len1,
        input logic [ADDR_WIDTH-1:0] addr2,
        input logic [2:0] size2,
        input logic [7:0] len2
    );
        logic [ADDR_WIDTH-1:0] end_addr1, end_addr2;
        end_addr1 = addr1 + ((len1 + 1) << size1) - 1;
        end_addr2 = addr2 + ((len2 + 1) << size2) - 1;
        
        return !((end_addr1 < addr2) || (end_addr2 < addr1));
    endfunction
    
    // Monitor exclusive reads
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_IDS; i++) begin
                exclusive_table[i] <= '0;
            end
        end else begin
            // Handle exclusive read
            if (exclusive_read_req) begin
                exclusive_table[exclusive_read_id].valid <= 1'b1;
                exclusive_table[exclusive_read_id].addr <= exclusive_read_addr;
                exclusive_table[exclusive_read_id].addr_mask <= calc_addr_mask(exclusive_read_size);
                exclusive_table[exclusive_read_id].size <= exclusive_read_size;
                exclusive_table[exclusive_read_id].len <= exclusive_read_len;
            end
            
            // Clear exclusive states on any overlapping write
            if (write_req) begin
                for (int i = 0; i < NUM_IDS; i++) begin
                    if (exclusive_table[i].valid) begin
                        if (addrs_overlap(exclusive_table[i].addr, exclusive_table[i].size, exclusive_table[i].len,
                                        write_addr, write_size, write_len)) begin
                            exclusive_table[i].valid <= 1'b0;
                        end
                    end
                end
            end
        end
    end
    
    // Check exclusive write
    always_comb begin
        exclusive_write_pass = 1'b0;
        
        if (exclusive_write_req && exclusive_table[exclusive_write_id].valid) begin
            // Check if addresses match (considering mask)
            logic [ADDR_WIDTH-1:0] mask = exclusive_table[exclusive_write_id].addr_mask;
            logic addr_match = ((exclusive_write_addr & mask) == 
                              (exclusive_table[exclusive_write_id].addr & mask));
            
            // Check if size and length match
            logic size_match = (exclusive_write_size == exclusive_table[exclusive_write_id].size);
            logic len_match = (exclusive_write_len == exclusive_table[exclusive_write_id].len);
            
            exclusive_write_pass = addr_match && size_match && len_match;
        end
    end
    
    // Assertions
    `ifdef AXI4_EXCLUSIVE_CHECK
    // Check exclusive access constraints
    property exclusive_size_valid;
        @(posedge clk) disable iff (!rst_n)
        exclusive_read_req |-> 
        ((1 << exclusive_read_size) * (exclusive_read_len + 1)) <= `AXI4_EXCLUSIVE_MAX_BYTES;
    endproperty
    
    assert property (exclusive_size_valid)
        else $error("Exclusive access exceeds maximum allowed size");
    
    // Check power-of-2 constraint
    property exclusive_power_of_2;
        @(posedge clk) disable iff (!rst_n)
        exclusive_read_req |-> 
        $onehot((1 << exclusive_read_size) * (exclusive_read_len + 1));
    endproperty
    
    assert property (exclusive_power_of_2)
        else $error("Exclusive access size is not power of 2");
    `endif
    
endmodule : axi4_exclusive_monitor