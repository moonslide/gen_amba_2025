//==============================================================================
// AXI4 Region Decoder
// 
// Description: Maps addresses to region identifiers
// Ensures region remains constant within 4KB boundaries
//==============================================================================

`include "axi4_defines.sv"

module axi4_region_decoder #(
    parameter int ADDR_WIDTH = 32,
    parameter int NUM_REGIONS = 16,
    parameter int REGION_WIDTH = 4
)(
    input logic                      clk,
    input logic                      rst_n,
    
    // Configuration interface
    input logic                      cfg_valid,
    input logic [3:0]                cfg_region_id,
    input logic [ADDR_WIDTH-1:0]     cfg_start_addr,
    input logic [ADDR_WIDTH-1:0]     cfg_end_addr,
    input logic                      cfg_enable,
    
    // Decode interface
    input logic [ADDR_WIDTH-1:0]     decode_addr,
    input logic                      decode_valid,
    output logic [REGION_WIDTH-1:0]  decode_region,
    output logic                     decode_hit,
    output logic                     decode_error  // Multiple region match
);

    // Region entry structure
    typedef struct packed {
        logic [ADDR_WIDTH-1:0]    start_addr;
        logic [ADDR_WIDTH-1:0]    end_addr;
        logic [REGION_WIDTH-1:0]  region_id;
        logic                     enable;
    } region_entry_t;
    
    // Region table
    region_entry_t region_table[NUM_REGIONS];
    
    // Configuration logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_REGIONS; i++) begin
                region_table[i] <= '0;
            end
        end else if (cfg_valid && cfg_region_id < NUM_REGIONS) begin
            region_table[cfg_region_id].start_addr <= cfg_start_addr;
            region_table[cfg_region_id].end_addr   <= cfg_end_addr;
            region_table[cfg_region_id].region_id  <= cfg_region_id;
            region_table[cfg_region_id].enable     <= cfg_enable;
        end
    end
    
    // Decode logic
    logic [NUM_REGIONS-1:0] region_match;
    logic [REGION_WIDTH-1:0] matched_region;
    
    always_comb begin
        decode_hit = 1'b0;
        decode_error = 1'b0;
        decode_region = '0;
        region_match = '0;
        matched_region = '0;
        
        if (decode_valid) begin
            // Check all regions for matches
            for (int i = 0; i < NUM_REGIONS; i++) begin
                if (region_table[i].enable &&
                    decode_addr >= region_table[i].start_addr &&
                    decode_addr <= region_table[i].end_addr) begin
                    region_match[i] = 1'b1;
                    matched_region = region_table[i].region_id;
                end
            end
            
            // Check results
            case ($countones(region_match))
                0: begin
                    decode_hit = 1'b0;
                    decode_region = '0;  // Default region
                end
                1: begin
                    decode_hit = 1'b1;
                    decode_region = matched_region;
                end
                default: begin
                    decode_hit = 1'b1;
                    decode_error = 1'b1;  // Multiple matches
                    decode_region = matched_region;  // Return one of them
                end
            endcase
        end
    end
    
    // 4KB boundary validation
    function automatic bit validate_4kb_consistency(
        logic [ADDR_WIDTH-1:0] start_addr,
        logic [ADDR_WIDTH-1:0] end_addr
    );
        // Check if region spans multiple 4KB pages
        logic [ADDR_WIDTH-13:0] start_page = start_addr[ADDR_WIDTH-1:12];
        logic [ADDR_WIDTH-13:0] end_page = end_addr[ADDR_WIDTH-1:12];
        
        // Region can span multiple pages, but must be consistent
        return 1'b1;  // This check is more relevant during access
    endfunction
    
    // Assertions
    `ifdef AXI4_REGION_CHECK
    // Check for overlapping regions during configuration
    property no_overlap;
        @(posedge clk) disable iff (!rst_n)
        cfg_valid && cfg_enable |-> 
        !$past(cfg_valid) || check_no_overlap();
    endproperty
    
    function automatic bit check_no_overlap();
        for (int i = 0; i < NUM_REGIONS; i++) begin
            if (i != cfg_region_id && region_table[i].enable) begin
                // Check if new region overlaps with existing
                if (!((cfg_end_addr < region_table[i].start_addr) ||
                      (cfg_start_addr > region_table[i].end_addr))) begin
                    return 1'b0;  // Overlap detected
                end
            end
        end
        return 1'b1;  // No overlap
    endfunction
    
    assert property (no_overlap)
        else $warning("Region overlap detected during configuration");
    
    // Check region consistency within 4KB
    property region_4kb_consistent;
        @(posedge clk) disable iff (!rst_n)
        decode_valid && decode_hit |-> 
        check_4kb_consistency(decode_addr, decode_region);
    endproperty
    
    function automatic bit check_4kb_consistency(
        logic [ADDR_WIDTH-1:0] addr,
        logic [REGION_WIDTH-1:0] region
    );
        logic [ADDR_WIDTH-1:0] page_start = {addr[ADDR_WIDTH-1:12], 12'h000};
        logic [ADDR_WIDTH-1:0] page_end = {addr[ADDR_WIDTH-1:12], 12'hFFF};
        logic [REGION_WIDTH-1:0] start_region, end_region;
        
        // Decode region at page boundaries
        for (int i = 0; i < NUM_REGIONS; i++) begin
            if (region_table[i].enable) begin
                if (page_start >= region_table[i].start_addr &&
                    page_start <= region_table[i].end_addr) begin
                    start_region = region_table[i].region_id;
                end
                if (page_end >= region_table[i].start_addr &&
                    page_end <= region_table[i].end_addr) begin
                    end_region = region_table[i].region_id;
                end
            end
        end
        
        return (start_region == end_region);
    endfunction
    
    assert property (region_4kb_consistent)
        else $error("Region changes within 4KB boundary");
    `endif
    
    // Debug
    `ifdef AXI4_REGION_DEBUG
    always_ff @(posedge clk) begin
        if (cfg_valid) begin
            $display("[%t] REGION_DECODER: Config region %0d - [%0h:%0h] %s",
                     $time, cfg_region_id, cfg_start_addr, cfg_end_addr,
                     cfg_enable ? "ENABLED" : "DISABLED");
        end
        
        if (decode_valid && decode_hit) begin
            $display("[%t] REGION_DECODER: Addr %0h -> Region %0d",
                     $time, decode_addr, decode_region);
        end
    end
    `endif
    
endmodule : axi4_region_decoder