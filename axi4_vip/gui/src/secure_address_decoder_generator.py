#!/usr/bin/env python3
"""
Secure Address Decoder RTL Generator
Generates timing-safe, security-hardened address decoder RTL
"""

class SecureAddressDecoderGenerator:
    """Generate secure, timing-safe address decoder RTL"""
    
    def __init__(self, config):
        self.config = config
        
    def generate_secure_decoder(self, output_dir="generated_rtl"):
        """Generate security-hardened address decoder"""
        filename = f"{output_dir}/axi4_secure_address_decoder.v"
        
        with open(filename, 'w') as f:
            f.write(self._generate_secure_decoder_rtl())
        
        return filename
    
    def _generate_secure_decoder_rtl(self):
        """Generate the secure RTL implementation"""
        num_masters = len(self.config.masters)
        num_slaves = len(self.config.slaves)
        
        return f"""//==============================================================================
// AXI4 Secure Address Decoder - Timing & Security Hardened
// Mitigates: Race conditions, timing violations, security bypass
// Features: Pipelined decode, ECC protection, anti-tampering
//==============================================================================

module axi4_secure_address_decoder #(
    parameter ADDR_WIDTH = 32,
    parameter NUM_SLAVES = {num_slaves},
    parameter NUM_MASTERS = {num_masters},
    parameter PIPELINE_STAGES = 2,  // Configurable pipeline depth
    parameter ECC_ENABLE = 1        // Enable ECC protection
)(
    input  wire                          aclk,
    input  wire                          aresetn,
    
    // Address channels (AXI4)
    input  wire [ADDR_WIDTH-1:0]         awaddr,
    input  wire                          awvalid,
    input  wire [2:0]                    awprot,
    input  wire [ADDR_WIDTH-1:0]         araddr,  
    input  wire                          arvalid,
    input  wire [2:0]                    arprot,
    input  wire [$clog2(NUM_MASTERS)-1:0] master_id,
    
    // Outputs
    output reg  [NUM_SLAVES-1:0]         slave_select,
    output reg                           access_error,
    output reg                           timing_violation,    // NEW: Timing safety
    output reg                           security_violation,  // NEW: Security alert
    
    // Configuration interface (secure)
    input  wire                          config_mode,         // NEW: Secure config
    input  wire [NUM_MASTERS-1:0]        config_permissions,
    input  wire [$clog2(NUM_SLAVES)-1:0] config_slave_id,
    input  wire                          config_valid,
    
    // Security & Debug
    input  wire                          debug_disable,       // NEW: Disable debug
    input  wire                          production_mode,     // NEW: Production lock
    output wire                          tamper_detect        // NEW: Tamper detection
);

//==============================================================================
// SECURE PERMISSION MATRIX WITH ECC PROTECTION
//==============================================================================

// Permission storage with ECC
reg [NUM_MASTERS-1:0] slave_permissions_raw [0:NUM_SLAVES-1];
wire [NUM_MASTERS-1:0] slave_permissions [0:NUM_SLAVES-1];
wire [NUM_SLAVES-1:0] permission_ecc_error;

generate
    if (ECC_ENABLE) begin : g_ecc_protection
        // ECC-protected permission matrix
        genvar i;
        for (i = 0; i < NUM_SLAVES; i = i + 1) begin : g_slave_ecc
            permission_ecc u_perm_ecc (
                .clk(aclk),
                .rst_n(aresetn),
                .data_in(slave_permissions_raw[i]),
                .data_out(slave_permissions[i]),
                .ecc_error(permission_ecc_error[i])
            );
        end
    end else begin : g_no_ecc
        // Direct assignment without ECC
        genvar i;
        for (i = 0; i < NUM_SLAVES; i = i + 1) begin : g_slave_direct
            assign slave_permissions[i] = slave_permissions_raw[i];
            assign permission_ecc_error[i] = 1'b0;
        end
    end
endgenerate

//==============================================================================
// SECURE CONFIGURATION WITH RESET PROTECTION
//==============================================================================

// Configuration state machine
typedef enum logic [1:0] {{
    CONFIG_LOCKED,      // Default - all access denied
    CONFIG_UNLOCKED,    // Temporary unlock for configuration
    CONFIG_PRODUCTION   // Permanently locked
}} config_state_t;

config_state_t config_state;

always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        // SECURE DEFAULT: Deny all access on reset
        for (int i = 0; i < NUM_SLAVES; i++) begin
            slave_permissions_raw[i] <= '0;  // All masters denied initially
        end
        config_state <= CONFIG_LOCKED;
    end else begin
        case (config_state)
            CONFIG_LOCKED: begin
                if (config_mode && !production_mode) begin
                    config_state <= CONFIG_UNLOCKED;
                end
            end
            
            CONFIG_UNLOCKED: begin
                if (config_valid && config_slave_id < NUM_SLAVES) begin
                    // Secure configuration update
                    slave_permissions_raw[config_slave_id] <= config_permissions;
                end
                
                if (!config_mode) begin
                    config_state <= CONFIG_LOCKED;
                end
                
                if (production_mode) begin
                    config_state <= CONFIG_PRODUCTION;  // Permanent lock
                end
            end
            
            CONFIG_PRODUCTION: begin
                // Permanently locked - no further configuration allowed
                // This prevents runtime tampering in production
            end
        endcase
    end
end

//==============================================================================
// PIPELINED ADDRESS DECODER - TIMING SAFE
//==============================================================================

// Pipeline stage registers
reg [ADDR_WIDTH-1:0] addr_pipe [0:PIPELINE_STAGES-1];
reg [2:0] prot_pipe [0:PIPELINE_STAGES-1];
reg valid_pipe [0:PIPELINE_STAGES-1];
reg [$clog2(NUM_MASTERS)-1:0] master_id_pipe [0:PIPELINE_STAGES-1];
reg is_write_pipe [0:PIPELINE_STAGES-1];

// Pipeline input stage
always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        for (int i = 0; i < PIPELINE_STAGES; i++) begin
            addr_pipe[i] <= '0;
            prot_pipe[i] <= '0;
            valid_pipe[i] <= 1'b0;
            master_id_pipe[i] <= '0;
            is_write_pipe[i] <= 1'b0;
        end
    end else begin
        // Stage 0: Input capture
        if (awvalid) begin
            addr_pipe[0] <= awaddr;
            prot_pipe[0] <= awprot;
            valid_pipe[0] <= 1'b1;
            is_write_pipe[0] <= 1'b1;
        end else if (arvalid) begin
            addr_pipe[0] <= araddr;
            prot_pipe[0] <= arprot;
            valid_pipe[0] <= 1'b1;
            is_write_pipe[0] <= 1'b0;
        end else begin
            valid_pipe[0] <= 1'b0;
        end
        
        master_id_pipe[0] <= master_id;
        
        // Pipeline advancement
        for (int i = 1; i < PIPELINE_STAGES; i++) begin
            addr_pipe[i] <= addr_pipe[i-1];
            prot_pipe[i] <= prot_pipe[i-1];
            valid_pipe[i] <= valid_pipe[i-1];
            master_id_pipe[i] <= master_id_pipe[i-1];
            is_write_pipe[i] <= is_write_pipe[i-1];
        end
    end
end

//==============================================================================  
// SECURE ADDRESS DECODE LOGIC
//==============================================================================

// Address decode results for each slave
reg [NUM_SLAVES-1:0] addr_match;
reg [NUM_SLAVES-1:0] perm_match;
reg [NUM_SLAVES-1:0] security_match;

// Final pipeline stage - decode logic
always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        slave_select <= '0;
        access_error <= 1'b0;
        timing_violation <= 1'b0;
        security_violation <= 1'b0;
    end else if (valid_pipe[PIPELINE_STAGES-1]) begin
        // Use final pipeline stage data
        wire [ADDR_WIDTH-1:0] decode_addr = addr_pipe[PIPELINE_STAGES-1];
        wire [2:0] decode_prot = prot_pipe[PIPELINE_STAGES-1];
        wire [$clog2(NUM_MASTERS)-1:0] decode_master = master_id_pipe[PIPELINE_STAGES-1];
        
        // Reset decode results
        addr_match = '0;
        perm_match = '0;
        security_match = '0;
        
        // Address range checking (broken into smaller logic)
{self._generate_address_decode_logic()}
        
        // Final result generation
        slave_select <= addr_match & perm_match & security_match;
        access_error <= |(addr_match & ~perm_match);
        security_violation <= |(addr_match & perm_match & ~security_match);
        
        // Timing violation detection (placeholder)
        timing_violation <= 1'b0;  // Would be set by timing monitors
        
    end else begin
        slave_select <= '0;
        access_error <= 1'b0;
        security_violation <= 1'b0;
    end
end

//==============================================================================
// ANTI-TAMPERING & SECURITY MONITORING
//==============================================================================

// Tamper detection logic
reg [15:0] tamper_counter;
wire config_tamper = (config_state == CONFIG_PRODUCTION) && config_mode;
wire ecc_tamper = |permission_ecc_error;
wire master_id_tamper = (decode_master >= NUM_MASTERS);

assign tamper_detect = config_tamper | ecc_tamper | master_id_tamper;

always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        tamper_counter <= '0;
    end else if (tamper_detect) begin
        if (tamper_counter != 16'hFFFF) begin
            tamper_counter <= tamper_counter + 1;
        end
    end
end

//==============================================================================
// DEBUG INTERFACE PROTECTION
//==============================================================================

`ifdef PRODUCTION_BUILD
    // In production builds, disable all debug interfaces
    assign scan_enable = 1'b0;
    assign debug_data_out = '0;
`else
    // Development builds allow controlled debug access
    assign scan_enable = debug_disable ? 1'b0 : scan_enable_in;
    assign debug_data_out = debug_disable ? '0 : internal_debug_data;
`endif

//==============================================================================
// ASSERTIONS FOR VERIFICATION
//==============================================================================

`ifdef FORMAL_VERIFICATION
    // Security properties that must always hold
    
    property no_unauthorized_access;
        @(posedge aclk) disable iff (!aresetn)
        (slave_select[i] && valid_pipe[PIPELINE_STAGES-1]) |-> 
        slave_permissions[i][master_id_pipe[PIPELINE_STAGES-1]];
    endproperty
    
    property secure_reset;
        @(posedge aclk) 
        !aresetn |-> ##1 (slave_select == '0);
    endproperty
    
    property production_lock;
        @(posedge aclk) disable iff (!aresetn)
        (config_state == CONFIG_PRODUCTION) |-> !config_valid;
    endproperty
    
    assert_no_unauthorized_access: assert property (no_unauthorized_access);
    assert_secure_reset: assert property (secure_reset);
    assert_production_lock: assert property (production_lock);
`endif

endmodule

//==============================================================================
// ECC PROTECTION MODULE
//==============================================================================

module permission_ecc #(
    parameter DATA_WIDTH = 8
)(
    input  wire                     clk,
    input  wire                     rst_n,
    input  wire [DATA_WIDTH-1:0]    data_in,
    output wire [DATA_WIDTH-1:0]    data_out,
    output wire                     ecc_error
);

// Simplified ECC - in production would use proper SECDED
wire [3:0] ecc_bits;
reg [DATA_WIDTH+3:0] ecc_memory;

// Generate ECC bits (simplified)
assign ecc_bits[0] = ^data_in[3:0];
assign ecc_bits[1] = ^data_in[7:4];
assign ecc_bits[2] = ^{{data_in[7:6], data_in[3:2]}};
assign ecc_bits[3] = ^{{data_in[5:4], data_in[1:0]}};

always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        ecc_memory <= '0;
    end else begin
        ecc_memory <= {{ecc_bits, data_in}};
    end
end

// Decode and error detection
wire [3:0] check_bits;
assign check_bits[0] = ^ecc_memory[3:0];
assign check_bits[1] = ^ecc_memory[7:4];
assign check_bits[2] = ^{{ecc_memory[7:6], ecc_memory[3:2]}};
assign check_bits[3] = ^{{ecc_memory[5:4], ecc_memory[1:0]}};

assign ecc_error = |(check_bits ^ ecc_memory[DATA_WIDTH+3:DATA_WIDTH]);
assign data_out = ecc_memory[DATA_WIDTH-1:0];

endmodule"""

    def _generate_address_decode_logic(self):
        """Generate secure address decode logic with timing consideration"""
        decode_logic = []
        
        for i, slave in enumerate(self.config.slaves):
            base = slave.base_address
            size = slave.size * 1024  # Convert KB to bytes
            end = base + size - 1
            
            decode_logic.append(f"""
        // Slave {i}: {slave.name} - Secure decode
        // Address range: 0x{base:08X} - 0x{end:08X}
        if (decode_addr >= {self.config.addr_width}'h{base:X} && 
            decode_addr <= {self.config.addr_width}'h{end:X}) begin
            addr_match[{i}] = 1'b1;
            
            // Permission check
            if (slave_permissions[{i}][decode_master]) begin
                perm_match[{i}] = 1'b1;
                
                // Security attribute checking
                security_match[{i}] = check_security_attributes(
                    decode_prot, 
                    1'b{1 if getattr(slave, 'secure_only', False) else 0},
                    1'b{1 if getattr(slave, 'privileged_only', False) else 0}
                );
            end
        end""")
        
        return "\n".join(decode_logic) + """
        
// Security checking function
function automatic check_security_attributes;
    input [2:0] prot;
    input secure_only;
    input privileged_only;
    begin
        check_security_attributes = 1'b1;
        
        // Secure access check (bit 1: 0=secure, 1=non-secure)
        if (secure_only && prot[1]) begin
            check_security_attributes = 1'b0;
        end
        
        // Privileged access check (bit 0: 1=privileged, 0=unprivileged)  
        if (privileged_only && !prot[0]) begin
            check_security_attributes = 1'b0;
        end
    end
endfunction"""