#!/usr/bin/env python3
"""Generate 1:1 RTL connections for all 15 masters to 15 slaves"""

def generate_connections():
    connections = []
    
    # Generate for masters/slaves 2-14
    for i in range(2, 15):
        connections.append(f"""
// Slave {i} connections (from Master {i})
assign s{i}_awid    = m{i}_awid;
assign s{i}_awaddr  = m{i}_awaddr;
assign s{i}_awlen   = m{i}_awlen;
assign s{i}_awsize  = m{i}_awsize;
assign s{i}_awburst = m{i}_awburst;
assign s{i}_awlock  = m{i}_awlock;
assign s{i}_awcache = m{i}_awcache;
assign s{i}_awprot  = m{i}_awprot;
assign s{i}_awqos   = m{i}_awqos;
assign s{i}_awvalid = m{i}_awvalid;
assign m{i}_awready = s{i}_awready;

assign s{i}_wdata   = m{i}_wdata;
assign s{i}_wstrb   = m{i}_wstrb;
assign s{i}_wlast   = m{i}_wlast;
assign s{i}_wvalid  = m{i}_wvalid;
assign m{i}_wready  = s{i}_wready;

assign m{i}_bid     = s{i}_bid;
assign m{i}_bresp   = s{i}_bresp;
assign m{i}_bvalid  = s{i}_bvalid;
assign s{i}_bready  = m{i}_bready;

assign s{i}_arid    = m{i}_arid;
assign s{i}_araddr  = m{i}_araddr;
assign s{i}_arlen   = m{i}_arlen;
assign s{i}_arsize  = m{i}_arsize;
assign s{i}_arburst = m{i}_arburst;
assign s{i}_arlock  = m{i}_arlock;
assign s{i}_arcache = m{i}_arcache;
assign s{i}_arprot  = m{i}_arprot;
assign s{i}_arqos   = m{i}_arqos;
assign s{i}_arvalid = m{i}_arvalid;
assign m{i}_arready = s{i}_arready;

assign m{i}_rid     = s{i}_rid;
assign m{i}_rdata   = s{i}_rdata;
assign m{i}_rresp   = s{i}_rresp;
assign m{i}_rlast   = s{i}_rlast;
assign m{i}_rvalid  = s{i}_rvalid;
assign s{i}_rready  = m{i}_rready;""")
    
    return ''.join(connections)

if __name__ == "__main__":
    print(generate_connections())