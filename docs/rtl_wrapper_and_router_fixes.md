# RTL Wrapper and Router Fixes

## Overview
This document describes the fixes implemented to address two critical issues:
1. RTL wrapper not connecting all configured masters and slaves
2. Router module using non-synthesizable function blocks

## Issue 1: RTL Wrapper Multi-Master/Slave Support

### Problem
The original `dut_wrapper.sv` only connected master 0 and didn't properly handle multiple masters and slaves.

### Solution
The wrapper now:
- Declares internal signals for all masters and slaves
- Connects Master 0 to the VIP interface 
- Terminates additional masters with proper idle values
- Provides simple response logic for all slaves
- Generates connections based on actual configuration

### Key Features
1. **Dynamic Signal Generation**
   - Creates signals for exactly the number of masters/slaves configured
   - Proper bit widths based on configuration

2. **Master Handling**
   ```systemverilog
   // Master 0 connected to VIP
   .m0_awid(axi_if.awid),
   .m0_awaddr(axi_if.awaddr),
   // ... all signals connected
   
   // Master 1+ terminated
   assign m1_awvalid = 1'b0;
   assign m1_wvalid  = 1'b0;
   // ... etc
   ```

3. **Slave Response Logic**
   ```systemverilog
   // Each slave has simple handshaking
   always @(posedge clk) begin
       if (!rst_n) begin
           s0_awready <= 1'b0;
           // ... reset logic
       end else begin
           s0_awready <= 1'b1;  // Always ready
           // ... response generation
       end
   end
   ```

## Issue 2: Router Function Block Replacement

### Problem
The `axi4_router.v` used Verilog functions for:
- 4KB boundary checking
- Access permission checking
- Response generation

These function blocks are not synthesizable in many tools.

### Solution
Replaced all functions with synthesizable constructs:

1. **4KB Boundary Check**
   - Before: Function with local variables
   - After: Combinational assign statements
   ```verilog
   // Calculate end address
   assign aw_end_addr = m_awaddr[i*ADDR_WIDTH +: ADDR_WIDTH] + aw_bytes - 1;
   
   // Check if crossing 4KB boundary
   assign aw_boundary_cross = (m_awaddr[i*ADDR_WIDTH+12 +: ADDR_WIDTH-12] != 
                              aw_end_addr[12 +: ADDR_WIDTH-12]);
   ```

2. **Access Permission Check**
   - Before: Function with if-else logic
   - After: Simple combinational logic
   ```verilog
   assign aw_privileged = m_awprot[i*3 +: 1];
   assign aw_secure = !m_awprot[i*3+1 +: 1];
   assign aw_access_allowed = (!secure_only || secure) && 
                             (!privileged_only || privileged);
   ```

3. **Response Generation**
   - Before: Function returning response codes
   - After: Always blocks with case logic
   ```verilog
   always @(*) begin
       if (s_decode_error[i])
           bresp_gen = 2'b11;  // DECERR
       else if (!s_access_valid[i])
           bresp_gen = 2'b10;  // SLVERR
       else
           bresp_gen = 2'b00;  // OKAY
   end
   ```

## Benefits

### RTL Wrapper
- Supports any number of masters and slaves
- Automatically adapts to configuration
- Provides proper signal termination
- Ready for multi-master testing

### Router Module
- Fully synthesizable
- No tool compatibility issues
- Cleaner, more readable code
- Same functionality with better implementation

## Generated Files Structure

When using "Generate RTL with this Tool":
```
rtl_wrapper/
├── generated_rtl/
│   ├── axi4_interconnect_m2s3.v  # Main interconnect
│   ├── axi4_address_decoder.v    # Address decode logic
│   ├── axi4_arbiter.v           # Arbitration
│   └── axi4_router.v            # Fixed router (no functions)
└── dut_wrapper.sv               # Auto-generated wrapper
```

## Example: 2 Masters, 3 Slaves Configuration

The wrapper will:
1. Connect Master 0 to VIP for testing
2. Terminate Master 1 (idle)
3. Create response logic for all 3 slaves
4. Generate proper module instantiation:
   ```systemverilog
   axi4_interconnect_m2s3 #(
       .DATA_WIDTH(32),
       .ADDR_WIDTH(32),
       .ID_WIDTH(4)
   ) generated_interconnect (
       // All masters connected
       .m0_awid(axi_if.awid),
       .m1_awid(m1_awid),
       
       // All slaves connected
       .s0_awready(s0_awready),
       .s1_awready(s1_awready),
       .s2_awready(s2_awready),
       // ... etc
   );
   ```

## Testing

The generated environment is ready for:
- Single master testing (Master 0 via VIP)
- Multi-slave verification
- Protocol compliance checking
- Performance analysis

## Next Steps

1. Configure desired number of masters/slaves in GUI
2. Generate RTL with tool
3. Environment automatically handles all connections
4. Ready to compile and simulate