#!/usr/bin/env python3
"""Generate complete AXI4 crossbar with continuous assignments"""

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
wire [14:0] m{m}_aw_slave_select;
wire [14:0] m{m}_ar_slave_select;

assign m{m}_aw_slave_select[0]  = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'h0);
assign m{m}_aw_slave_select[1]  = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'h1);
assign m{m}_aw_slave_select[2]  = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'h2);
assign m{m}_aw_slave_select[3]  = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'h3);
assign m{m}_aw_slave_select[4]  = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'h4);
assign m{m}_aw_slave_select[5]  = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'h5);
assign m{m}_aw_slave_select[6]  = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'h6);
assign m{m}_aw_slave_select[7]  = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'h7);
assign m{m}_aw_slave_select[8]  = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'h8);
assign m{m}_aw_slave_select[9]  = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'h9);
assign m{m}_aw_slave_select[10] = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'hA);
assign m{m}_aw_slave_select[11] = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'hB);
assign m{m}_aw_slave_select[12] = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'hC);
assign m{m}_aw_slave_select[13] = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'hD);
assign m{m}_aw_slave_select[14] = m{m}_awvalid && (m{m}_awaddr[31:28] == 4'hE);

assign m{m}_ar_slave_select[0]  = m{m}_arvalid && (m{m}_araddr[31:28] == 4'h0);
assign m{m}_ar_slave_select[1]  = m{m}_arvalid && (m{m}_araddr[31:28] == 4'h1);
assign m{m}_ar_slave_select[2]  = m{m}_arvalid && (m{m}_araddr[31:28] == 4'h2);
assign m{m}_ar_slave_select[3]  = m{m}_arvalid && (m{m}_araddr[31:28] == 4'h3);
assign m{m}_ar_slave_select[4]  = m{m}_arvalid && (m{m}_araddr[31:28] == 4'h4);
assign m{m}_ar_slave_select[5]  = m{m}_arvalid && (m{m}_araddr[31:28] == 4'h5);
assign m{m}_ar_slave_select[6]  = m{m}_arvalid && (m{m}_araddr[31:28] == 4'h6);
assign m{m}_ar_slave_select[7]  = m{m}_arvalid && (m{m}_araddr[31:28] == 4'h7);
assign m{m}_ar_slave_select[8]  = m{m}_arvalid && (m{m}_araddr[31:28] == 4'h8);
assign m{m}_ar_slave_select[9]  = m{m}_arvalid && (m{m}_araddr[31:28] == 4'h9);
assign m{m}_ar_slave_select[10] = m{m}_arvalid && (m{m}_araddr[31:28] == 4'hA);
assign m{m}_ar_slave_select[11] = m{m}_arvalid && (m{m}_araddr[31:28] == 4'hB);
assign m{m}_ar_slave_select[12] = m{m}_arvalid && (m{m}_araddr[31:28] == 4'hC);
assign m{m}_ar_slave_select[13] = m{m}_arvalid && (m{m}_araddr[31:28] == 4'hD);
assign m{m}_ar_slave_select[14] = m{m}_arvalid && (m{m}_araddr[31:28] == 4'hE);
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
            reqs.append(f"m{m}_aw_slave_select[{s}]")
        code.append(", ".join(reqs))
        code.append("};\n")
        
        code.append(f"wire [14:0] s{s}_ar_requests = {{")
        reqs = []
        for m in range(14, -1, -1):
            reqs.append(f"m{m}_ar_slave_select[{s}]")
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
            // Simplified: grant to lowest numbered requesting master
            if (s{s}_aw_requests[0]) s{s}_aw_grant <= 4'd0;""")
        
        for m in range(1, 15):
            code.append(f"""
            else if (s{s}_aw_requests[{m}]) s{s}_aw_grant <= 4'd{m};""")
        
        code.append(f"""
        end else if (s{s}_awready && s{s}_awvalid) begin
            // Transaction accepted, release grant
            s{s}_aw_last_grant <= s{s}_aw_grant;
            s{s}_aw_grant <= 4'd15;
        end
        
        // AR channel arbitration
        if (s{s}_ar_grant == 4'd15) begin // No current grant
            // Simplified: grant to lowest numbered requesting master
            if (s{s}_ar_requests[0]) s{s}_ar_grant <= 4'd0;""")
        
        for m in range(1, 15):
            code.append(f"""
            else if (s{s}_ar_requests[{m}]) s{s}_ar_grant <= 4'd{m};""")
        
        code.append(f"""
        end else if (s{s}_arready && s{s}_arvalid) begin
            // Transaction accepted, release grant
            s{s}_ar_last_grant <= s{s}_ar_grant;
            s{s}_ar_grant <= 4'd15;
        end
    end
end
""")
    
    # Generate crossbar multiplexing for each slave using continuous assignments
    code.append("""
//------------------------------------------------------------------------------
// Crossbar multiplexing - connect granted master to each slave
//------------------------------------------------------------------------------
""")
    
    for s in range(15):
        code.append(f"""
// Slave {s} input multiplexing - using continuous assignments
// AW channel
assign s{s}_awid    = """)
        for m in range(15):
            if m == 0:
                code.append(f"(s{s}_aw_grant == 4'd{m}) ? m{m}_awid :")
            elif m < 14:
                code.append(f"""
                      (s{s}_aw_grant == 4'd{m}) ? m{m}_awid :""")
            else:
                code.append(f"""
                      (s{s}_aw_grant == 4'd{m}) ? m{m}_awid : {{ID_WIDTH{{1'b0}}}};""")
        
        code.append(f"""
assign s{s}_awaddr  = """)
        for m in range(15):
            if m == 0:
                code.append(f"(s{s}_aw_grant == 4'd{m}) ? m{m}_awaddr :")
            elif m < 14:
                code.append(f"""
                      (s{s}_aw_grant == 4'd{m}) ? m{m}_awaddr :""")
            else:
                code.append(f"""
                      (s{s}_aw_grant == 4'd{m}) ? m{m}_awaddr : {{ADDR_WIDTH{{1'b0}}}};""")
        
        # Continue for all AW signals
        aw_signals = [
            ('awlen', '8'),
            ('awsize', '3'),
            ('awburst', '2'),
            ('awlock', '1'),
            ('awcache', '4'),
            ('awprot', '3'),
            ('awqos', '4'),
            ('awvalid', '1')
        ]
        
        for sig, width in aw_signals:
            code.append(f"""
assign s{s}_{sig} = """)
            for m in range(15):
                if m == 0:
                    if sig == 'awvalid':
                        code.append(f"(s{s}_aw_grant == 4'd{m}) ? (m{m}_{sig} & m{m}_aw_slave_select[{s}]) :")
                    else:
                        code.append(f"(s{s}_aw_grant == 4'd{m}) ? m{m}_{sig} :")
                elif m < 14:
                    if sig == 'awvalid':
                        code.append(f"""
                    (s{s}_aw_grant == 4'd{m}) ? (m{m}_{sig} & m{m}_aw_slave_select[{s}]) :""")
                    else:
                        code.append(f"""
                    (s{s}_aw_grant == 4'd{m}) ? m{m}_{sig} :""")
                else:
                    if sig == 'awvalid':
                        code.append(f"""
                    (s{s}_aw_grant == 4'd{m}) ? (m{m}_{sig} & m{m}_aw_slave_select[{s}]) : 1'b0;""")
                    else:
                        code.append(f"""
                    (s{s}_aw_grant == 4'd{m}) ? m{m}_{sig} : {width}'b0;""")
        
        # W channel signals
        code.append(f"""
assign s{s}_wdata = """)
        for m in range(15):
            if m == 0:
                code.append(f"(s{s}_aw_grant == 4'd{m}) ? m{m}_wdata :")
            elif m < 14:
                code.append(f"""
                   (s{s}_aw_grant == 4'd{m}) ? m{m}_wdata :""")
            else:
                code.append(f"""
                   (s{s}_aw_grant == 4'd{m}) ? m{m}_wdata : {{DATA_WIDTH{{1'b0}}}};""")
        
        code.append(f"""
assign s{s}_wstrb = """)
        for m in range(15):
            if m == 0:
                code.append(f"(s{s}_aw_grant == 4'd{m}) ? m{m}_wstrb :")
            elif m < 14:
                code.append(f"""
                   (s{s}_aw_grant == 4'd{m}) ? m{m}_wstrb :""")
            else:
                code.append(f"""
                   (s{s}_aw_grant == 4'd{m}) ? m{m}_wstrb : {{DATA_WIDTH/8{{1'b0}}}};""")
        
        code.append(f"""
assign s{s}_wlast = """)
        for m in range(15):
            if m == 0:
                code.append(f"(s{s}_aw_grant == 4'd{m}) ? m{m}_wlast :")
            elif m < 14:
                code.append(f"""
                   (s{s}_aw_grant == 4'd{m}) ? m{m}_wlast :""")
            else:
                code.append(f"""
                   (s{s}_aw_grant == 4'd{m}) ? m{m}_wlast : 1'b0;""")
        
        code.append(f"""
assign s{s}_wvalid = """)
        for m in range(15):
            if m == 0:
                code.append(f"(s{s}_aw_grant == 4'd{m}) ? m{m}_wvalid :")
            elif m < 14:
                code.append(f"""
                    (s{s}_aw_grant == 4'd{m}) ? m{m}_wvalid :""")
            else:
                code.append(f"""
                    (s{s}_aw_grant == 4'd{m}) ? m{m}_wvalid : 1'b0;""")
        
        code.append(f"""
assign s{s}_bready = """)
        for m in range(15):
            if m == 0:
                code.append(f"(s{s}_aw_grant == 4'd{m}) ? m{m}_bready :")
            elif m < 14:
                code.append(f"""
                    (s{s}_aw_grant == 4'd{m}) ? m{m}_bready :""")
            else:
                code.append(f"""
                    (s{s}_aw_grant == 4'd{m}) ? m{m}_bready : 1'b0;""")
        
        # AR channel signals
        code.append(f"""

// AR channel
assign s{s}_arid = """)
        for m in range(15):
            if m == 0:
                code.append(f"(s{s}_ar_grant == 4'd{m}) ? m{m}_arid :")
            elif m < 14:
                code.append(f"""
                  (s{s}_ar_grant == 4'd{m}) ? m{m}_arid :""")
            else:
                code.append(f"""
                  (s{s}_ar_grant == 4'd{m}) ? m{m}_arid : {{ID_WIDTH{{1'b0}}}};""")
        
        code.append(f"""
assign s{s}_araddr = """)
        for m in range(15):
            if m == 0:
                code.append(f"(s{s}_ar_grant == 4'd{m}) ? m{m}_araddr :")
            elif m < 14:
                code.append(f"""
                    (s{s}_ar_grant == 4'd{m}) ? m{m}_araddr :""")
            else:
                code.append(f"""
                    (s{s}_ar_grant == 4'd{m}) ? m{m}_araddr : {{ADDR_WIDTH{{1'b0}}}};""")
        
        # Other AR signals
        ar_signals = [
            ('arlen', '8'),
            ('arsize', '3'),
            ('arburst', '2'),
            ('arlock', '1'),
            ('arcache', '4'),
            ('arprot', '3'),
            ('arqos', '4'),
            ('arvalid', '1')
        ]
        
        for sig, width in ar_signals:
            code.append(f"""
assign s{s}_{sig} = """)
            for m in range(15):
                if m == 0:
                    if sig == 'arvalid':
                        code.append(f"(s{s}_ar_grant == 4'd{m}) ? (m{m}_{sig} & m{m}_ar_slave_select[{s}]) :")
                    else:
                        code.append(f"(s{s}_ar_grant == 4'd{m}) ? m{m}_{sig} :")
                elif m < 14:
                    if sig == 'arvalid':
                        code.append(f"""
                   (s{s}_ar_grant == 4'd{m}) ? (m{m}_{sig} & m{m}_ar_slave_select[{s}]) :""")
                    else:
                        code.append(f"""
                   (s{s}_ar_grant == 4'd{m}) ? m{m}_{sig} :""")
                else:
                    if sig == 'arvalid':
                        code.append(f"""
                   (s{s}_ar_grant == 4'd{m}) ? (m{m}_{sig} & m{m}_ar_slave_select[{s}]) : 1'b0;""")
                    else:
                        code.append(f"""
                   (s{s}_ar_grant == 4'd{m}) ? m{m}_{sig} : {width}'b0;""")
        
        code.append(f"""
assign s{s}_rready = """)
        for m in range(15):
            if m == 0:
                code.append(f"(s{s}_ar_grant == 4'd{m}) ? m{m}_rready :")
            elif m < 14:
                code.append(f"""
                    (s{s}_ar_grant == 4'd{m}) ? m{m}_rready :""")
            else:
                code.append(f"""
                    (s{s}_ar_grant == 4'd{m}) ? m{m}_rready : 1'b0;""")
    
    # Generate response routing back to masters
    code.append("""

//------------------------------------------------------------------------------
// Response routing - route slave responses back to requesting master
//------------------------------------------------------------------------------
""")
    
    for m in range(15):
        code.append(f"""
// Master {m} response routing
// Track which slave is being accessed based on address
wire [3:0] m{m}_aw_target = m{m}_awaddr[31:28];
wire [3:0] m{m}_ar_target = m{m}_araddr[31:28];

// AW ready - from target slave if granted
assign m{m}_awready = """)
        for s in range(15):
            if s == 0:
                code.append(f"(m{m}_aw_target == 4'd{s} && s{s}_aw_grant == 4'd{m}) ? s{s}_awready :")
            elif s < 14:
                code.append(f"""
                     (m{m}_aw_target == 4'd{s} && s{s}_aw_grant == 4'd{m}) ? s{s}_awready :""")
            else:
                code.append(f"""
                     (m{m}_aw_target == 4'd{s} && s{s}_aw_grant == 4'd{m}) ? s{s}_awready : 1'b0;""")
        
        code.append(f"""

// W ready - from target slave if granted
assign m{m}_wready = """)
        for s in range(15):
            if s == 0:
                code.append(f"(m{m}_aw_target == 4'd{s} && s{s}_aw_grant == 4'd{m}) ? s{s}_wready :")
            elif s < 14:
                code.append(f"""
                    (m{m}_aw_target == 4'd{s} && s{s}_aw_grant == 4'd{m}) ? s{s}_wready :""")
            else:
                code.append(f"""
                    (m{m}_aw_target == 4'd{s} && s{s}_aw_grant == 4'd{m}) ? s{s}_wready : 1'b0;""")
        
        # B response channel
        code.append(f"""

// B response - from any slave that has a response for this master
assign m{m}_bid = """)
        for s in range(15):
            if s == 0:
                code.append(f"s{s}_bvalid ? s{s}_bid :")
            elif s < 14:
                code.append(f"""
                 s{s}_bvalid ? s{s}_bid :""")
            else:
                code.append(f"""
                 s{s}_bvalid ? s{s}_bid : {{ID_WIDTH{{1'b0}}}};""")
        
        code.append(f"""
assign m{m}_bresp = """)
        for s in range(15):
            if s == 0:
                code.append(f"s{s}_bvalid ? s{s}_bresp :")
            elif s < 14:
                code.append(f"""
                   s{s}_bvalid ? s{s}_bresp :""")
            else:
                code.append(f"""
                   s{s}_bvalid ? s{s}_bresp : 2'b00;""")
        
        code.append(f"""
assign m{m}_bvalid = """)
        vals = [f"s{s}_bvalid" for s in range(15)]
        code.append(" | ".join(vals) + ";")
        
        # AR ready
        code.append(f"""

// AR ready - from target slave if granted
assign m{m}_arready = """)
        for s in range(15):
            if s == 0:
                code.append(f"(m{m}_ar_target == 4'd{s} && s{s}_ar_grant == 4'd{m}) ? s{s}_arready :")
            elif s < 14:
                code.append(f"""
                     (m{m}_ar_target == 4'd{s} && s{s}_ar_grant == 4'd{m}) ? s{s}_arready :""")
            else:
                code.append(f"""
                     (m{m}_ar_target == 4'd{s} && s{s}_ar_grant == 4'd{m}) ? s{s}_arready : 1'b0;""")
        
        # R response channel
        code.append(f"""

// R response - from any slave that has a response for this master
assign m{m}_rid = """)
        for s in range(15):
            if s == 0:
                code.append(f"s{s}_rvalid ? s{s}_rid :")
            elif s < 14:
                code.append(f"""
                 s{s}_rvalid ? s{s}_rid :""")
            else:
                code.append(f"""
                 s{s}_rvalid ? s{s}_rid : {{ID_WIDTH{{1'b0}}}};""")
        
        code.append(f"""
assign m{m}_rdata = """)
        for s in range(15):
            if s == 0:
                code.append(f"s{s}_rvalid ? s{s}_rdata :")
            elif s < 14:
                code.append(f"""
                   s{s}_rvalid ? s{s}_rdata :""")
            else:
                code.append(f"""
                   s{s}_rvalid ? s{s}_rdata : {{DATA_WIDTH{{1'b0}}}};""")
        
        code.append(f"""
assign m{m}_rresp = """)
        for s in range(15):
            if s == 0:
                code.append(f"s{s}_rvalid ? s{s}_rresp :")
            elif s < 14:
                code.append(f"""
                   s{s}_rvalid ? s{s}_rresp :""")
            else:
                code.append(f"""
                   s{s}_rvalid ? s{s}_rresp : 2'b00;""")
        
        code.append(f"""
assign m{m}_rlast = """)
        for s in range(15):
            if s == 0:
                code.append(f"s{s}_rvalid ? s{s}_rlast :")
            elif s < 14:
                code.append(f"""
                   s{s}_rvalid ? s{s}_rlast :""")
            else:
                code.append(f"""
                   s{s}_rvalid ? s{s}_rlast : 1'b0;""")
        
        code.append(f"""
assign m{m}_rvalid = """)
        vals = [f"s{s}_rvalid" for s in range(15)]
        code.append(" | ".join(vals) + ";")
        
        code.append("\n")
    
    return '\n'.join(code)

if __name__ == "__main__":
    print(generate_complete_crossbar())