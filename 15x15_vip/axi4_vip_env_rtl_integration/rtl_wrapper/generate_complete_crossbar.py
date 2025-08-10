#!/usr/bin/env python3
"""Generate complete AXI4 crossbar with address decoding and arbitration"""

def generate_complete_crossbar():
    """Generate full AXI4 crossbar implementation for 15x15 interconnect"""
    
    code = []
    
    # Header
    code.append("""//------------------------------------------------------------------------------
// AXI4 Crossbar Switch Implementation
// Implements full crossbar allowing any master to access any slave
// Based on address decoding and round-robin arbitration
//------------------------------------------------------------------------------

// Address decoding - each slave gets 256MB address space
// Slave 0: 0x00000000 - 0x0FFFFFFF
// Slave 1: 0x10000000 - 0x1FFFFFFF
// ...
// Slave 14: 0xE0000000 - 0xEFFFFFFF

// For each master, decode target slave from address
""")
    
    # Generate address decoders for each master
    for m in range(15):
        code.append(f"""
// Master {m} address decoder
reg [14:0] m{m}_aw_slave_select;
reg [14:0] m{m}_ar_slave_select;

always @(*) begin
    m{m}_aw_slave_select = 15'b0;
    m{m}_ar_slave_select = 15'b0;
    
    // Decode write address channel
    if (m{m}_awvalid) begin
        case (m{m}_awaddr[31:28])
            4'h0: m{m}_aw_slave_select[0] = 1'b1;
            4'h1: m{m}_aw_slave_select[1] = 1'b1;
            4'h2: m{m}_aw_slave_select[2] = 1'b1;
            4'h3: m{m}_aw_slave_select[3] = 1'b1;
            4'h4: m{m}_aw_slave_select[4] = 1'b1;
            4'h5: m{m}_aw_slave_select[5] = 1'b1;
            4'h6: m{m}_aw_slave_select[6] = 1'b1;
            4'h7: m{m}_aw_slave_select[7] = 1'b1;
            4'h8: m{m}_aw_slave_select[8] = 1'b1;
            4'h9: m{m}_aw_slave_select[9] = 1'b1;
            4'hA: m{m}_aw_slave_select[10] = 1'b1;
            4'hB: m{m}_aw_slave_select[11] = 1'b1;
            4'hC: m{m}_aw_slave_select[12] = 1'b1;
            4'hD: m{m}_aw_slave_select[13] = 1'b1;
            4'hE: m{m}_aw_slave_select[14] = 1'b1;
            default: m{m}_aw_slave_select[0] = 1'b1; // Default to slave 0
        endcase
    end
    
    // Decode read address channel
    if (m{m}_arvalid) begin
        case (m{m}_araddr[31:28])
            4'h0: m{m}_ar_slave_select[0] = 1'b1;
            4'h1: m{m}_ar_slave_select[1] = 1'b1;
            4'h2: m{m}_ar_slave_select[2] = 1'b1;
            4'h3: m{m}_ar_slave_select[3] = 1'b1;
            4'h4: m{m}_ar_slave_select[4] = 1'b1;
            4'h5: m{m}_ar_slave_select[5] = 1'b1;
            4'h6: m{m}_ar_slave_select[6] = 1'b1;
            4'h7: m{m}_ar_slave_select[7] = 1'b1;
            4'h8: m{m}_ar_slave_select[8] = 1'b1;
            4'h9: m{m}_ar_slave_select[9] = 1'b1;
            4'hA: m{m}_ar_slave_select[10] = 1'b1;
            4'hB: m{m}_ar_slave_select[11] = 1'b1;
            4'hC: m{m}_ar_slave_select[12] = 1'b1;
            4'hD: m{m}_ar_slave_select[13] = 1'b1;
            4'hE: m{m}_ar_slave_select[14] = 1'b1;
            default: m{m}_ar_slave_select[0] = 1'b1; // Default to slave 0
        endcase
    end
end
""")
    
    # Generate arbitration logic for each slave
    code.append("""
//------------------------------------------------------------------------------
// Arbitration logic - Round-robin for each slave
//------------------------------------------------------------------------------
""")
    
    for s in range(15):
        code.append(f"""
// Slave {s} arbitration
reg [3:0] s{s}_aw_grant;  // Which master has AW grant
reg [3:0] s{s}_ar_grant;  // Which master has AR grant
reg [3:0] s{s}_aw_last_grant;
reg [3:0] s{s}_ar_last_grant;

// Collect requests from all masters for this slave
wire [14:0] s{s}_aw_requests = {{""")
        
        # Build request vector
        reqs = []
        for m in range(14, -1, -1):
            reqs.append(f"(m{m}_awvalid & m{m}_aw_slave_select[{s}])")
        code.append(", ".join(reqs))
        code.append("};\n")
        
        code.append(f"wire [14:0] s{s}_ar_requests = {{")
        reqs = []
        for m in range(14, -1, -1):
            reqs.append(f"(m{m}_arvalid & m{m}_ar_slave_select[{s}])")
        code.append(", ".join(reqs))
        code.append("};\n")
        
        # Round-robin arbitration
        code.append(f"""
// Round-robin arbitration for slave {s}
always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        s{s}_aw_grant <= 4'd15; // No grant
        s{s}_ar_grant <= 4'd15; // No grant
        s{s}_aw_last_grant <= 4'd0;
        s{s}_ar_last_grant <= 4'd0;
    end else begin
        // AW channel arbitration
        if (s{s}_aw_grant == 4'd15) begin // No current grant
            // Find next requester in round-robin order
            if (s{s}_aw_requests != 15'b0) begin
                integer i;
                for (i = 1; i <= 15; i = i + 1) begin
                    if (s{s}_aw_requests[(s{s}_aw_last_grant + i) % 15] && s{s}_aw_grant == 4'd15) begin
                        s{s}_aw_grant <= (s{s}_aw_last_grant + i) % 15;
                    end
                end
            end
        end else if (s{s}_awready && s{s}_awvalid) begin
            // Transaction accepted, release grant
            s{s}_aw_last_grant <= s{s}_aw_grant;
            s{s}_aw_grant <= 4'd15;
        end
        
        // AR channel arbitration
        if (s{s}_ar_grant == 4'd15) begin // No current grant
            // Find next requester in round-robin order
            if (s{s}_ar_requests != 15'b0) begin
                integer j;
                for (j = 1; j <= 15; j = j + 1) begin
                    if (s{s}_ar_requests[(s{s}_ar_last_grant + j) % 15] && s{s}_ar_grant == 4'd15) begin
                        s{s}_ar_grant <= (s{s}_ar_last_grant + j) % 15;
                    end
                end
            end
        end else if (s{s}_arready && s{s}_arvalid) begin
            // Transaction accepted, release grant
            s{s}_ar_last_grant <= s{s}_ar_grant;
            s{s}_ar_grant <= 4'd15;
        end
    end
end
""")
    
    # Generate crossbar multiplexing for each slave
    code.append("""
//------------------------------------------------------------------------------
// Crossbar multiplexing - connect granted master to each slave
//------------------------------------------------------------------------------
""")
    
    for s in range(15):
        code.append(f"""
// Slave {s} input multiplexing
always @(*) begin
    // Default values
    s{s}_awid    = {{ID_WIDTH{{1'b0}}}};
    s{s}_awaddr  = {{ADDR_WIDTH{{1'b0}}}};
    s{s}_awlen   = 8'b0;
    s{s}_awsize  = 3'b0;
    s{s}_awburst = 2'b0;
    s{s}_awlock  = 1'b0;
    s{s}_awcache = 4'b0;
    s{s}_awprot  = 3'b0;
    s{s}_awqos   = 4'b0;
    s{s}_awvalid = 1'b0;
    
    s{s}_wdata   = {{DATA_WIDTH{{1'b0}}}};
    s{s}_wstrb   = {{DATA_WIDTH/8{{1'b0}}}};
    s{s}_wlast   = 1'b0;
    s{s}_wvalid  = 1'b0;
    
    s{s}_bready  = 1'b0;
    
    s{s}_arid    = {{ID_WIDTH{{1'b0}}}};
    s{s}_araddr  = {{ADDR_WIDTH{{1'b0}}}};
    s{s}_arlen   = 8'b0;
    s{s}_arsize  = 3'b0;
    s{s}_arburst = 2'b0;
    s{s}_arlock  = 1'b0;
    s{s}_arcache = 4'b0;
    s{s}_arprot  = 3'b0;
    s{s}_arqos   = 4'b0;
    s{s}_arvalid = 1'b0;
    
    s{s}_rready  = 1'b0;
    
    // Connect granted master for AW channel
    case (s{s}_aw_grant)""")
        
        for m in range(15):
            code.append(f"""
        4'd{m}: begin
            s{s}_awid    = m{m}_awid;
            s{s}_awaddr  = m{m}_awaddr;
            s{s}_awlen   = m{m}_awlen;
            s{s}_awsize  = m{m}_awsize;
            s{s}_awburst = m{m}_awburst;
            s{s}_awlock  = m{m}_awlock;
            s{s}_awcache = m{m}_awcache;
            s{s}_awprot  = m{m}_awprot;
            s{s}_awqos   = m{m}_awqos;
            s{s}_awvalid = m{m}_awvalid & m{m}_aw_slave_select[{s}];
            
            s{s}_wdata   = m{m}_wdata;
            s{s}_wstrb   = m{m}_wstrb;
            s{s}_wlast   = m{m}_wlast;
            s{s}_wvalid  = m{m}_wvalid;
            
            s{s}_bready  = m{m}_bready;
        end""")
        
        code.append("""
        default: begin
            // No grant, keep defaults
        end
    endcase
    
    // Connect granted master for AR channel""")
        code.append(f"""
    case (s{s}_ar_grant)""")
        
        for m in range(15):
            code.append(f"""
        4'd{m}: begin
            s{s}_arid    = m{m}_arid;
            s{s}_araddr  = m{m}_araddr;
            s{s}_arlen   = m{m}_arlen;
            s{s}_arsize  = m{m}_arsize;
            s{s}_arburst = m{m}_arburst;
            s{s}_arlock  = m{m}_arlock;
            s{s}_arcache = m{m}_arcache;
            s{s}_arprot  = m{m}_arprot;
            s{s}_arqos   = m{m}_arqos;
            s{s}_arvalid = m{m}_arvalid & m{m}_ar_slave_select[{s}];
            
            s{s}_rready  = m{m}_rready;
        end""")
        
        code.append("""
        default: begin
            // No grant, keep defaults
        end
    endcase
end
""")
    
    # Generate response routing back to masters
    code.append("""
//------------------------------------------------------------------------------
// Response routing - route slave responses back to requesting master
//------------------------------------------------------------------------------
""")
    
    for m in range(15):
        code.append(f"""
// Master {m} response multiplexing
reg [3:0] m{m}_active_aw_slave;
reg [3:0] m{m}_active_ar_slave;

// Track which slave this master is accessing
always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        m{m}_active_aw_slave <= 4'd15;
        m{m}_active_ar_slave <= 4'd15;
    end else begin
        // Track AW slave
        if (m{m}_awvalid && m{m}_awready) begin
            if (m{m}_aw_slave_select[0]) m{m}_active_aw_slave <= 4'd0;""")
        
        for s in range(1, 15):
            code.append(f"""
            else if (m{m}_aw_slave_select[{s}]) m{m}_active_aw_slave <= 4'd{s};""")
        
        code.append(f"""
        end else if (m{m}_bvalid && m{m}_bready) begin
            m{m}_active_aw_slave <= 4'd15; // Clear after response
        end
        
        // Track AR slave
        if (m{m}_arvalid && m{m}_arready) begin
            if (m{m}_ar_slave_select[0]) m{m}_active_ar_slave <= 4'd0;""")
        
        for s in range(1, 15):
            code.append(f"""
            else if (m{m}_ar_slave_select[{s}]) m{m}_active_ar_slave <= 4'd{s};""")
        
        code.append(f"""
        end else if (m{m}_rvalid && m{m}_rready && m{m}_rlast) begin
            m{m}_active_ar_slave <= 4'd15; // Clear after last response
        end
    end
end

always @(*) begin
    // Default values
    m{m}_awready = 1'b0;
    m{m}_wready  = 1'b0;
    m{m}_bid     = {{ID_WIDTH{{1'b0}}}};
    m{m}_bresp   = 2'b00;
    m{m}_bvalid  = 1'b0;
    m{m}_arready = 1'b0;
    m{m}_rid     = {{ID_WIDTH{{1'b0}}}};
    m{m}_rdata   = {{DATA_WIDTH{{1'b0}}}};
    m{m}_rresp   = 2'b00;
    m{m}_rlast   = 1'b0;
    m{m}_rvalid  = 1'b0;
    
    // Route AW/W/B responses
    case (m{m}_active_aw_slave)""")
        
        for s in range(15):
            code.append(f"""
        4'd{s}: begin
            if (s{s}_aw_grant == 4'd{m}) begin
                m{m}_awready = s{s}_awready;
                m{m}_wready  = s{s}_wready;
            end
            m{m}_bid     = s{s}_bid;
            m{m}_bresp   = s{s}_bresp;
            m{m}_bvalid  = s{s}_bvalid;
        end""")
        
        code.append("""
        default: begin
            // Check for new AW transaction
            if (m""" + str(m) + """_aw_slave_select[0] && s0_aw_grant == 4'd""" + str(m) + """) begin
                m""" + str(m) + """_awready = s0_awready;
            end""")
        
        for s in range(1, 15):
            code.append("""
            else if (m""" + str(m) + """_aw_slave_select[""" + str(s) + """] && s""" + str(s) + """_aw_grant == 4'd""" + str(m) + """) begin
                m""" + str(m) + """_awready = s""" + str(s) + """_awready;
            end""")
        
        code.append("""
        end
    endcase
    
    // Route AR/R responses
    case (m""" + str(m) + """_active_ar_slave)""")
        
        for s in range(15):
            code.append(f"""
        4'd{s}: begin
            if (s{s}_ar_grant == 4'd{m}) begin
                m{m}_arready = s{s}_arready;
            end
            m{m}_rid     = s{s}_rid;
            m{m}_rdata   = s{s}_rdata;
            m{m}_rresp   = s{s}_rresp;
            m{m}_rlast   = s{s}_rlast;
            m{m}_rvalid  = s{s}_rvalid;
        end""")
        
        code.append("""
        default: begin
            // Check for new AR transaction
            if (m""" + str(m) + """_ar_slave_select[0] && s0_ar_grant == 4'd""" + str(m) + """) begin
                m""" + str(m) + """_arready = s0_arready;
            end""")
        
        for s in range(1, 15):
            code.append("""
            else if (m""" + str(m) + """_ar_slave_select[""" + str(s) + """] && s""" + str(s) + """_ar_grant == 4'd""" + str(m) + """) begin
                m""" + str(m) + """_arready = s""" + str(s) + """_arready;
            end""")
        
        code.append("""
        end
    endcase
end
""")
    
    return '\n'.join(code)

if __name__ == "__main__":
    print(generate_complete_crossbar())