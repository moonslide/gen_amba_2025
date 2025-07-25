//==============================================================================
// AXI4 QoS-based Arbiter
// 
// Description: Implements QoS-aware arbitration with configurable schemes
// Supports strict priority, weighted round-robin, and fair share modes
//==============================================================================

`include "axi4_defines.sv"

module axi4_qos_arbiter #(
    parameter int NUM_MASTERS = 4,
    parameter int ID_WIDTH = 4,
    parameter int ADDR_WIDTH = 32
)(
    input logic                         clk,
    input logic                         rst_n,
    
    // Arbitration mode
    input logic [1:0]                   arb_mode,  // 0=Fixed, 1=RR, 2=QoS, 3=WRR
    input logic [3:0]                   weight[NUM_MASTERS],  // For WRR mode
    
    // Request inputs from masters
    input logic                         req_valid[NUM_MASTERS],
    input logic [3:0]                   req_qos[NUM_MASTERS],
    input logic [ID_WIDTH-1:0]          req_id[NUM_MASTERS],
    input logic [ADDR_WIDTH-1:0]        req_addr[NUM_MASTERS],
    output logic                        req_ready[NUM_MASTERS],
    
    // Granted output
    output logic                        grant_valid,
    output logic [$clog2(NUM_MASTERS)-1:0] grant_master,
    input logic                         grant_ready,
    
    // Performance counters
    output logic [31:0]                 grant_count[NUM_MASTERS],
    output logic [31:0]                 wait_cycles[NUM_MASTERS]
);

    // Arbitration modes
    localparam FIXED_PRIORITY = 2'b00;
    localparam ROUND_ROBIN    = 2'b01;
    localparam QOS_PRIORITY   = 2'b10;
    localparam WEIGHTED_RR    = 2'b11;
    
    // Internal signals
    logic [$clog2(NUM_MASTERS)-1:0] rr_ptr;
    logic [$clog2(NUM_MASTERS)-1:0] next_grant;
    logic [3:0] wrr_credit[NUM_MASTERS];
    logic pending_grant;
    logic [NUM_MASTERS-1:0] req_pending;
    
    // Track pending requests
    always_comb begin
        for (int i = 0; i < NUM_MASTERS; i++) begin
            req_pending[i] = req_valid[i] && !req_ready[i];
        end
    end
    
    // Arbitration logic
    always_comb begin
        next_grant = '0;
        pending_grant = 1'b0;
        
        case (arb_mode)
            FIXED_PRIORITY: begin
                // Fixed priority - lower index has higher priority
                for (int i = NUM_MASTERS-1; i >= 0; i--) begin
                    if (req_pending[i]) begin
                        next_grant = i[$clog2(NUM_MASTERS)-1:0];
                        pending_grant = 1'b1;
                    end
                end
            end
            
            ROUND_ROBIN: begin
                // Round-robin arbitration
                logic found = 1'b0;
                for (int i = 0; i < NUM_MASTERS; i++) begin
                    int idx = (rr_ptr + i) % NUM_MASTERS;
                    if (req_pending[idx] && !found) begin
                        next_grant = idx[$clog2(NUM_MASTERS)-1:0];
                        pending_grant = 1'b1;
                        found = 1'b1;
                    end
                end
            end
            
            QOS_PRIORITY: begin
                // QoS-based priority
                logic [3:0] max_qos = 4'h0;
                logic found = 1'b0;
                
                // Find highest QoS value
                for (int i = 0; i < NUM_MASTERS; i++) begin
                    if (req_pending[i] && req_qos[i] > max_qos) begin
                        max_qos = req_qos[i];
                    end
                end
                
                // Grant to first master with highest QoS
                for (int i = 0; i < NUM_MASTERS; i++) begin
                    if (req_pending[i] && req_qos[i] == max_qos && !found) begin
                        next_grant = i[$clog2(NUM_MASTERS)-1:0];
                        pending_grant = 1'b1;
                        found = 1'b1;
                    end
                end
            end
            
            WEIGHTED_RR: begin
                // Weighted round-robin
                logic found = 1'b0;
                
                // First check masters with remaining credit
                for (int i = 0; i < NUM_MASTERS; i++) begin
                    int idx = (rr_ptr + i) % NUM_MASTERS;
                    if (req_pending[idx] && wrr_credit[idx] > 0 && !found) begin
                        next_grant = idx[$clog2(NUM_MASTERS)-1:0];
                        pending_grant = 1'b1;
                        found = 1'b1;
                    end
                end
                
                // If no credited master found, grant to any
                if (!found) begin
                    for (int i = 0; i < NUM_MASTERS; i++) begin
                        int idx = (rr_ptr + i) % NUM_MASTERS;
                        if (req_pending[idx] && !found) begin
                            next_grant = idx[$clog2(NUM_MASTERS)-1:0];
                            pending_grant = 1'b1;
                            found = 1'b1;
                        end
                    end
                end
            end
        endcase
    end
    
    // Grant control and pointer updates
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            grant_valid <= 1'b0;
            grant_master <= '0;
            rr_ptr <= '0;
            for (int i = 0; i < NUM_MASTERS; i++) begin
                wrr_credit[i] <= weight[i];
            end
        end else begin
            if (grant_valid && grant_ready) begin
                grant_valid <= 1'b0;
                
                // Update round-robin pointer
                if (arb_mode == ROUND_ROBIN || arb_mode == WEIGHTED_RR) begin
                    rr_ptr <= (grant_master + 1) % NUM_MASTERS;
                end
                
                // Update WRR credits
                if (arb_mode == WEIGHTED_RR) begin
                    if (wrr_credit[grant_master] > 0) begin
                        wrr_credit[grant_master] <= wrr_credit[grant_master] - 1;
                    end
                    
                    // Reload credits if all are zero
                    logic all_zero = 1'b1;
                    for (int i = 0; i < NUM_MASTERS; i++) begin
                        if (wrr_credit[i] != 0) all_zero = 1'b0;
                    end
                    if (all_zero) begin
                        for (int i = 0; i < NUM_MASTERS; i++) begin
                            wrr_credit[i] <= weight[i];
                        end
                    end
                end
            end
            
            if (!grant_valid && pending_grant) begin
                grant_valid <= 1'b1;
                grant_master <= next_grant;
            end
        end
    end
    
    // Ready signal generation
    always_comb begin
        for (int i = 0; i < NUM_MASTERS; i++) begin
            req_ready[i] = grant_valid && grant_ready && (grant_master == i);
        end
    end
    
    // Performance counters
    logic [31:0] wait_counter[NUM_MASTERS];
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < NUM_MASTERS; i++) begin
                grant_count[i] <= '0;
                wait_cycles[i] <= '0;
                wait_counter[i] <= '0;
            end
        end else begin
            for (int i = 0; i < NUM_MASTERS; i++) begin
                // Count grants
                if (grant_valid && grant_ready && grant_master == i) begin
                    grant_count[i] <= grant_count[i] + 1;
                end
                
                // Count wait cycles
                if (req_valid[i] && !req_ready[i]) begin
                    wait_counter[i] <= wait_counter[i] + 1;
                end else if (req_ready[i]) begin
                    wait_cycles[i] <= wait_cycles[i] + wait_counter[i];
                    wait_counter[i] <= '0;
                end
            end
        end
    end
    
    // Assertions
    `ifdef AXI4_ARB_CHECK
    // Check one-hot grant
    property onehot_grant;
        @(posedge clk) disable iff (!rst_n)
        grant_valid |-> $onehot0(req_ready);
    endproperty
    
    assert property (onehot_grant)
        else $error("Multiple grants active simultaneously");
    
    // Check grant to valid requestor
    property valid_grant;
        @(posedge clk) disable iff (!rst_n)
        grant_valid |-> req_valid[grant_master];
    endproperty
    
    assert property (valid_grant)
        else $error("Grant to inactive master");
    `endif
    
endmodule : axi4_qos_arbiter