//==============================================================================
// AXI4 Arbiter
// Arbitrates between multiple masters for slave access
//==============================================================================

module axi4_arbiter #(
    parameter NUM_MASTERS = 4,
    parameter ARBITRATION = "QOS"  // FIXED, RR, QOS, WRR
)(
    input  wire                          aclk,
    input  wire                          aresetn,
    
    // Master requests and priorities
    input  wire                          master0_request,
    input  wire [3:0]                    master0_priority,
    input  wire                          master1_request,
    input  wire [3:0]                    master1_priority,
    input  wire                          master2_request,
    input  wire [3:0]                    master2_priority,
    input  wire                          master3_request,
    input  wire [3:0]                    master3_priority,
    
    // Grant output
    output reg  [NUM_MASTERS-1:0]        grant
);

reg [NUM_MASTERS-1:0] grant_next;
reg [$clog2(NUM_MASTERS)-1:0] rr_counter;

// Collect requests
wire [NUM_MASTERS-1:0] request;
assign request = {(NUM_MASTERS > 3) ? master3_request : 1'b0, (NUM_MASTERS > 2) ? master2_request : 1'b0, (NUM_MASTERS > 1) ? master1_request : 1'b0, (NUM_MASTERS > 0) ? master0_request : 1'b0};

// Priority collection for QoS
wire [3:0] priority [0:NUM_MASTERS-1];
assign priority[0] = (NUM_MASTERS > 0) ? master0_priority : 4'b0;
assign priority[1] = (NUM_MASTERS > 1) ? master1_priority : 4'b0;
assign priority[2] = (NUM_MASTERS > 2) ? master2_priority : 4'b0;
assign priority[3] = (NUM_MASTERS > 3) ? master3_priority : 4'b0;

// Arbitration logic
always @(*) begin
    grant_next = grant;
    
    case (ARBITRATION)
        "FIXED": begin
            // Fixed priority - lower index = higher priority
            grant_next = {NUM_MASTERS{1'b0}};
            if (request[0]) grant_next[0] = 1'b1;
            else if (NUM_MASTERS > 1 && request[1]) grant_next[1] = 1'b1;
            else if (NUM_MASTERS > 2 && request[2]) grant_next[2] = 1'b1;
            else if (NUM_MASTERS > 3 && request[3]) grant_next[3] = 1'b1;
        end
        
        "RR": begin
            // Round-robin arbitration
            grant_next = {NUM_MASTERS{1'b0}};
            // Implementation simplified for clarity
            grant_next[rr_counter] = request[rr_counter];
        end
        
        "QOS": begin
            // Quality of Service based arbitration
            integer i, j;
            reg [3:0] max_priority;
            reg [NUM_MASTERS-1:0] candidates;
            
            grant_next = {NUM_MASTERS{1'b0}};
            max_priority = 4'b0;
            candidates = {NUM_MASTERS{1'b0}};
            
            // Find highest priority
            for (i = 0; i < NUM_MASTERS; i = i + 1) begin
                if (request[i] && priority[i] > max_priority) begin
                    max_priority = priority[i];
                end
            end
            
            // Find all masters with highest priority
            for (i = 0; i < NUM_MASTERS; i = i + 1) begin
                if (request[i] && priority[i] == max_priority) begin
                    candidates[i] = 1'b1;
                end
            end
            
            // Among candidates, use fixed priority
            for (i = 0; i < NUM_MASTERS; i = i + 1) begin
                if (candidates[i]) begin
                    grant_next[i] = 1'b1;
                    i = NUM_MASTERS; // Break
                end
            end
        end
        
        default: grant_next = {NUM_MASTERS{1'b0}};
    endcase
end

// Sequential logic
always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        grant <= {NUM_MASTERS{1'b0}};
        rr_counter <= {$clog2(NUM_MASTERS){1'b0}};
    end else begin
        grant <= grant_next;
        
        // Update round-robin counter
        if (ARBITRATION == "RR" && |grant) begin
            if (rr_counter == NUM_MASTERS-1)
                rr_counter <= {$clog2(NUM_MASTERS){1'b0}};
            else
                rr_counter <= rr_counter + 1'b1;
        end
    end
end

endmodule
