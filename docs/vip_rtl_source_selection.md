# VIP RTL Source Selection Feature

## Overview

The VIP Environment Setup now includes an RTL source selection step when choosing RTL Integration Mode. This allows users to:

1. **Use External RTL IP** - For existing RTL designs that need verification
2. **Generate RTL with this Tool** - The tool generates Verilog RTL and automatically wraps it with VIP

## Workflow

### Step 1: Select RTL Integration Mode
When you choose "RTL Integration Mode" in the VIP Environment Setup dialog and click Next, you'll see the RTL Source Selection screen.

### Step 2: Choose RTL Source

#### Option 1: Use External RTL IP
- Select this if you have an existing RTL design
- Optionally browse to select the directory containing your RTL files
- The tool will generate a wrapper template for your RTL

#### Option 2: Generate RTL with this Tool
- The tool will generate Verilog RTL based on your bus configuration
- Automatically creates a fully connected wrapper
- No manual port connections needed

### Step 3: External RTL Directory (Optional)
If you selected "Use External RTL IP", you can:
- Browse to select your RTL directory
- Leave empty to manually add RTL files later
- The tool will copy your RTL files to the generated environment

### Step 4: Output Directory Selection
After RTL source selection, choose where to generate the VIP environment.

## Generated Wrapper Differences

### For External RTL
- Generic wrapper template with all AXI4 signals
- Placeholder module name "your_axi_dut"
- Comments guide you through customization
- All 60+ AXI4 signals pre-connected

### For Tool-Generated RTL
- Fully automated wrapper
- Correct module name (e.g., "axi4_interconnect")
- All connections pre-configured
- Ready to simulate without modifications

## Example: Tool-Generated RTL Wrapper

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

    // Automated instantiation of tool-generated interconnect
    axi4_interconnect #(
        .DATA_WIDTH(32),
        .ADDR_WIDTH(32),
        .ID_WIDTH(4),
        .USER_WIDTH(1)
    ) generated_interconnect (
        .clk(clk),
        .rst_n(rst_n),
        
        // All AXI4 signals auto-connected
        .m0_axi_awid(axi_if.awid),
        .m0_axi_awaddr(axi_if.awaddr),
        // ... 60+ signals pre-connected ...
    );

endmodule
```

## Benefits

1. **Flexibility** - Support both existing RTL and new designs
2. **Automation** - Tool-generated RTL is automatically wrapped
3. **Time Savings** - No manual port connections for generated RTL
4. **Error Reduction** - Automated connections prevent mistakes

## File Organization

When using tool-generated RTL:
```
rtl_integration_env/
├── rtl_wrapper/
│   ├── generated_rtl/      # Tool-generated Verilog files
│   │   └── axi4_interconnect.v
│   └── dut_wrapper.sv      # Auto-generated wrapper
```

When using external RTL:
```
rtl_integration_env/
├── rtl_wrapper/
│   ├── external_rtl/       # Your copied RTL files
│   │   └── your_design.v
│   └── dut_wrapper.sv      # Template wrapper to customize
```

## Quick Start

### For Tool-Generated RTL
1. Select "Generate RTL with this Tool"
2. Click Next, select output directory
3. Generate - everything is ready to simulate!

### For External RTL
1. Select "Use External RTL IP"
2. Browse to your RTL directory (optional)
3. Click Next, select output directory
4. Generate
5. Edit `dut_wrapper.sv` to match your module

## Tips

- The tool-generated RTL option is perfect for testing the VIP setup
- External RTL option supports any existing AXI4 design
- Generated wrappers include helpful comments and instructions
- All standard AXI4 signal names are supported