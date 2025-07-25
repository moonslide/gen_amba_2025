# RTL Generation Fix

## Issue
When selecting "Generate RTL with this Tool" option, the error "AXIVerilog object has no attribute 'generate_verilog'" occurred.

## Solution
Fixed the method name from `generate_verilog()` to `generate()` which is the correct method in AXIVerilogGenerator class.

## How it Works Now

### 1. RTL Generation Process
When you select "Generate RTL with this Tool":
- The tool calls `AXIVerilogGenerator.generate()`
- It generates a complete AXI4 interconnect based on your bus configuration
- Files are placed in `rtl_wrapper/generated_rtl/`

### 2. Generated Module Name
The generated interconnect module follows this naming convention:
```
axi4_interconnect_m{num_masters}s{num_slaves}
```

For example:
- 2 masters, 3 slaves → `axi4_interconnect_m2s3`
- 1 master, 2 slaves → `axi4_interconnect_m1s2`

### 3. Automatic Wrapper
The tool automatically generates a wrapper that:
- Instantiates the generated interconnect with correct module name
- Connects VIP to master port 0 (m0_axi_*) of the interconnect
- Properly maps all AXI4 signals
- Sets up parameters based on your configuration

### 4. Generated Files
```
rtl_integration_env/
├── rtl_wrapper/
│   ├── generated_rtl/
│   │   ├── axi4_interconnect_m2s3.v     # Main interconnect
│   │   ├── axi4_address_decoder.v       # Address decoder
│   │   ├── axi4_arbiter.v               # Arbitration logic
│   │   └── axi4_router.v                # Routing logic
│   └── dut_wrapper.sv                   # Auto-generated wrapper
```

### 5. Example Generated Wrapper
```systemverilog
module dut_wrapper #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH   = 4
) (
    input  logic clk,
    input  logic rst_n,
    axi4_if.slave axi_if  // tim_axi4_vip interface
);

    // Automated instantiation of generated interconnect
    axi4_interconnect_m2s3 #(
        .DATA_WIDTH(32),
        .ADDR_WIDTH(32),
        .ID_WIDTH(4)
    ) generated_interconnect (
        .clk(clk),
        .rst_n(rst_n),
        
        // Master 0 Interface (connected to VIP)
        .m0_axi_awid(axi_if.awid),
        .m0_axi_awaddr(axi_if.awaddr),
        // ... all signals connected ...
    );

endmodule
```

## Testing the Fix

1. Configure your bus matrix in the GUI
2. Open VIP panel and click "Create VIP Environment"
3. Select "RTL Integration Mode" → Next
4. Select "Generate RTL with this Tool" → Next
5. Choose output directory → Generate

The tool will now:
- Generate the RTL interconnect
- Create the wrapper automatically
- Set up the complete verification environment
- Be ready to compile and simulate

## Benefits
- No manual RTL coding required
- Automatic signal connections
- Correct module naming
- Complete working environment