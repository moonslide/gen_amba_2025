#!/usr/bin/env python3
"""
Generate Integrated Top-Level Wrapper for AMBA AXI
This script creates a single top-level file that integrates all generated modules
"""

import os
import sys
import re
from datetime import datetime

def extract_module_info(verilog_file):
    """Extract module name and ports from a Verilog file"""
    with open(verilog_file, 'r') as f:
        content = f.read()
    
    # Find module declaration
    module_match = re.search(r'module\s+(\w+)\s*#?\s*\(([^)]*)\)', content, re.DOTALL)
    if not module_match:
        module_match = re.search(r'module\s+(\w+)', content)
        if not module_match:
            return None, None
    
    module_name = module_match.group(1)
    
    # Extract parameters if they exist
    param_match = re.search(r'#\s*\((.*?)\)\s*\(', content, re.DOTALL)
    parameters = param_match.group(1) if param_match else None
    
    # Extract ports
    port_match = re.search(r'module\s+\w+.*?\((.*?)\);', content, re.DOTALL)
    ports = port_match.group(1) if port_match else None
    
    return module_name, {'parameters': parameters, 'ports': ports}

def generate_integrated_top(rtl_dir, project_name, num_masters, num_slaves, features):
    """Generate integrated top-level wrapper"""
    
    # Find all generated modules
    modules = {}
    interconnect_file = None
    
    for file in os.listdir(rtl_dir):
        if file.endswith('.v'):
            filepath = os.path.join(rtl_dir, file)
            module_name, module_info = extract_module_info(filepath)
            if module_name:
                modules[module_name] = {
                    'file': file,
                    'info': module_info
                }
                if 'interconnect' in file:
                    interconnect_file = file
    
    if not interconnect_file:
        print("Error: No interconnect module found!")
        return False
    
    # Generate integrated top file
    top_file = os.path.join(rtl_dir, f"{project_name}_integrated_top.v")
    
    with open(top_file, 'w') as f:
        # Header
        f.write(f"""//------------------------------------------------------------------------------
// Integrated Top-Level Wrapper for {project_name}
// Generated on: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
// 
// This file integrates all generated AMBA AXI modules into a single top-level
// Number of Masters: {num_masters}
// Number of Slaves: {num_slaves}
//------------------------------------------------------------------------------

module {project_name}_integrated_top
    #(parameter NUM_MASTER  = {num_masters}
              , NUM_SLAVE   = {num_slaves}
              , WIDTH_ID    = 4
              , WIDTH_AD    = 32
              , WIDTH_DA    = 64
              , WIDTH_DS    = (WIDTH_DA/8)
""")
        
        # Add feature-specific parameters
        if features.get('enable_user'):
            f.write("""              , WIDTH_AWUSER = 8
              , WIDTH_WUSER  = 8
              , WIDTH_BUSER  = 8
              , WIDTH_ARUSER = 8
              , WIDTH_RUSER  = 8
""")
        
        if features.get('enable_qos'):
            f.write("              , WIDTH_QOS    = 4\n")
        
        if features.get('enable_region'):
            f.write("              , WIDTH_REGION = 4\n")
            
        # Add slave address parameters
        for i in range(num_slaves):
            f.write(f"              , SLAVE_EN{i} = 1\n")
            f.write(f"              , ADDR_BASE{i} = 32'h{i*0x2000:08X}\n")
            f.write(f"              , ADDR_LENGTH{i} = 12\n")
        
        f.write("    )\n")
        f.write("    (\n")
        f.write("      input  wire                     ARESETn\n")
        f.write("    , input  wire                     ACLK\n")
        
        # Generate master ports
        for m in range(num_masters):
            f.write(f"""
    //---------- Master {m} Interface ----------
    // Write Address Channel
    , input  wire [WIDTH_ID-1:0]    M{m}_AWID
    , input  wire [WIDTH_AD-1:0]    M{m}_AWADDR
    , input  wire [7:0]              M{m}_AWLEN
    , input  wire [2:0]              M{m}_AWSIZE
    , input  wire [1:0]              M{m}_AWBURST
    , input  wire                    M{m}_AWLOCK
    , input  wire [3:0]              M{m}_AWCACHE
    , input  wire [2:0]              M{m}_AWPROT
    , input  wire                    M{m}_AWVALID
    , output wire                    M{m}_AWREADY
""")
            if features.get('enable_qos'):
                f.write(f"    , input  wire [3:0]              M{m}_AWQOS\n")
                f.write(f"    , input  wire [3:0]              M{m}_AWREGION\n")
            if features.get('enable_user'):
                f.write(f"    , input  wire [WIDTH_AWUSER-1:0] M{m}_AWUSER\n")
            
            f.write(f"""    // Write Data Channel
    , input  wire [WIDTH_DA-1:0]    M{m}_WDATA
    , input  wire [WIDTH_DS-1:0]    M{m}_WSTRB
    , input  wire                    M{m}_WLAST
    , input  wire                    M{m}_WVALID
    , output wire                    M{m}_WREADY
""")
            if features.get('enable_user'):
                f.write(f"    , input  wire [WIDTH_WUSER-1:0]  M{m}_WUSER\n")
            
            f.write(f"""    // Write Response Channel
    , output wire [WIDTH_ID-1:0]    M{m}_BID
    , output wire [1:0]              M{m}_BRESP
    , output wire                    M{m}_BVALID
    , input  wire                    M{m}_BREADY
""")
            if features.get('enable_user'):
                f.write(f"    , output wire [WIDTH_BUSER-1:0]  M{m}_BUSER\n")
            
            f.write(f"""    // Read Address Channel
    , input  wire [WIDTH_ID-1:0]    M{m}_ARID
    , input  wire [WIDTH_AD-1:0]    M{m}_ARADDR
    , input  wire [7:0]              M{m}_ARLEN
    , input  wire [2:0]              M{m}_ARSIZE
    , input  wire [1:0]              M{m}_ARBURST
    , input  wire                    M{m}_ARLOCK
    , input  wire [3:0]              M{m}_ARCACHE
    , input  wire [2:0]              M{m}_ARPROT
    , input  wire                    M{m}_ARVALID
    , output wire                    M{m}_ARREADY
""")
            if features.get('enable_qos'):
                f.write(f"    , input  wire [3:0]              M{m}_ARQOS\n")
                f.write(f"    , input  wire [3:0]              M{m}_ARREGION\n")
            if features.get('enable_user'):
                f.write(f"    , input  wire [WIDTH_ARUSER-1:0] M{m}_ARUSER\n")
            
            f.write(f"""    // Read Data Channel
    , output wire [WIDTH_ID-1:0]    M{m}_RID
    , output wire [WIDTH_DA-1:0]    M{m}_RDATA
    , output wire [1:0]              M{m}_RRESP
    , output wire                    M{m}_RLAST
    , output wire                    M{m}_RVALID
    , input  wire                    M{m}_RREADY
""")
            if features.get('enable_user'):
                f.write(f"    , output wire [WIDTH_RUSER-1:0]  M{m}_RUSER\n")
        
        # Generate slave ports
        for s in range(num_slaves):
            f.write(f"""
    //---------- Slave {s} Interface ----------
    // Write Address Channel
    , output wire [WIDTH_ID+$clog2(NUM_MASTER)-1:0] S{s}_AWID
    , output wire [WIDTH_AD-1:0]    S{s}_AWADDR
    , output wire [7:0]              S{s}_AWLEN
    , output wire [2:0]              S{s}_AWSIZE
    , output wire [1:0]              S{s}_AWBURST
    , output wire                    S{s}_AWLOCK
    , output wire [3:0]              S{s}_AWCACHE
    , output wire [2:0]              S{s}_AWPROT
    , output wire                    S{s}_AWVALID
    , input  wire                    S{s}_AWREADY
""")
            if features.get('enable_qos'):
                f.write(f"    , output wire [3:0]              S{s}_AWQOS\n")
                f.write(f"    , output wire [3:0]              S{s}_AWREGION\n")
            if features.get('enable_user'):
                f.write(f"    , output wire [WIDTH_AWUSER-1:0] S{s}_AWUSER\n")
            
            f.write(f"""    // Write Data Channel
    , output wire [WIDTH_DA-1:0]    S{s}_WDATA
    , output wire [WIDTH_DS-1:0]    S{s}_WSTRB
    , output wire                    S{s}_WLAST
    , output wire                    S{s}_WVALID
    , input  wire                    S{s}_WREADY
""")
            if features.get('enable_user'):
                f.write(f"    , output wire [WIDTH_WUSER-1:0]  S{s}_WUSER\n")
            
            f.write(f"""    // Write Response Channel
    , input  wire [WIDTH_ID+$clog2(NUM_MASTER)-1:0] S{s}_BID
    , input  wire [1:0]              S{s}_BRESP
    , input  wire                    S{s}_BVALID
    , output wire                    S{s}_BREADY
""")
            if features.get('enable_user'):
                f.write(f"    , input  wire [WIDTH_BUSER-1:0]  S{s}_BUSER\n")
            
            f.write(f"""    // Read Address Channel
    , output wire [WIDTH_ID+$clog2(NUM_MASTER)-1:0] S{s}_ARID
    , output wire [WIDTH_AD-1:0]    S{s}_ARADDR
    , output wire [7:0]              S{s}_ARLEN
    , output wire [2:0]              S{s}_ARSIZE
    , output wire [1:0]              S{s}_ARBURST
    , output wire                    S{s}_ARLOCK
    , output wire [3:0]              S{s}_ARCACHE
    , output wire [2:0]              S{s}_ARPROT
    , output wire                    S{s}_ARVALID
    , input  wire                    S{s}_ARREADY
""")
            if features.get('enable_qos'):
                f.write(f"    , output wire [3:0]              S{s}_ARQOS\n")
                f.write(f"    , output wire [3:0]              S{s}_ARREGION\n")
            if features.get('enable_user'):
                f.write(f"    , output wire [WIDTH_ARUSER-1:0] S{s}_ARUSER\n")
            
            f.write(f"""    // Read Data Channel
    , input  wire [WIDTH_ID+$clog2(NUM_MASTER)-1:0] S{s}_RID
    , input  wire [WIDTH_DA-1:0]    S{s}_RDATA
    , input  wire [1:0]              S{s}_RRESP
    , input  wire                    S{s}_RLAST
    , input  wire                    S{s}_RVALID
    , output wire                    S{s}_RREADY
""")
            if features.get('enable_user'):
                f.write(f"    , input  wire [WIDTH_RUSER-1:0]  S{s}_RUSER\n")
        
        f.write("    );\n\n")
        
        # Include all module files
        f.write("    //--------------------------------------------------------------------------\n")
        f.write("    // Include all generated modules\n")
        f.write("    //--------------------------------------------------------------------------\n\n")
        
        for module_name, module_data in modules.items():
            f.write(f"    `include \"{module_data['file']}\"\n")
        
        f.write("\n")
        f.write("    //--------------------------------------------------------------------------\n")
        f.write("    // Instantiate main interconnect\n")
        f.write("    //--------------------------------------------------------------------------\n\n")
        
        # Find and instantiate the interconnect module
        interconnect_module = None
        for module_name in modules:
            if 'interconnect' in module_name:
                interconnect_module = module_name
                break
        
        if interconnect_module:
            f.write(f"    {interconnect_module} #(\n")
            f.write("        .NUM_MASTER(NUM_MASTER),\n")
            f.write("        .NUM_SLAVE(NUM_SLAVE),\n")
            f.write("        .WIDTH_ID(WIDTH_ID),\n")
            f.write("        .WIDTH_AD(WIDTH_AD),\n")
            f.write("        .WIDTH_DA(WIDTH_DA)\n")
            
            for i in range(num_slaves):
                f.write(f"        ,.SLAVE_EN{i}(SLAVE_EN{i})\n")
                f.write(f"        ,.ADDR_BASE{i}(ADDR_BASE{i})\n")
                f.write(f"        ,.ADDR_LENGTH{i}(ADDR_LENGTH{i})\n")
            
            f.write("    ) u_interconnect (\n")
            f.write("        .ARESETn(ARESETn),\n")
            f.write("        .ACLK(ACLK)")
            
            # Connect all master and slave ports
            for m in range(num_masters):
                for signal in ['AWID', 'AWADDR', 'AWLEN', 'AWSIZE', 'AWBURST', 'AWLOCK', 
                              'AWCACHE', 'AWPROT', 'AWVALID', 'AWREADY',
                              'WDATA', 'WSTRB', 'WLAST', 'WVALID', 'WREADY',
                              'BID', 'BRESP', 'BVALID', 'BREADY',
                              'ARID', 'ARADDR', 'ARLEN', 'ARSIZE', 'ARBURST', 'ARLOCK',
                              'ARCACHE', 'ARPROT', 'ARVALID', 'ARREADY',
                              'RID', 'RDATA', 'RRESP', 'RLAST', 'RVALID', 'RREADY']:
                    f.write(f",\n        .M{m}_{signal}(M{m}_{signal})")
                
                if features.get('enable_qos'):
                    f.write(f",\n        .M{m}_AWQOS(M{m}_AWQOS)")
                    f.write(f",\n        .M{m}_AWREGION(M{m}_AWREGION)")
                    f.write(f",\n        .M{m}_ARQOS(M{m}_ARQOS)")
                    f.write(f",\n        .M{m}_ARREGION(M{m}_ARREGION)")
                
                if features.get('enable_user'):
                    f.write(f",\n        .M{m}_AWUSER(M{m}_AWUSER)")
                    f.write(f",\n        .M{m}_WUSER(M{m}_WUSER)")
                    f.write(f",\n        .M{m}_BUSER(M{m}_BUSER)")
                    f.write(f",\n        .M{m}_ARUSER(M{m}_ARUSER)")
                    f.write(f",\n        .M{m}_RUSER(M{m}_RUSER)")
            
            for s in range(num_slaves):
                for signal in ['AWID', 'AWADDR', 'AWLEN', 'AWSIZE', 'AWBURST', 'AWLOCK',
                              'AWCACHE', 'AWPROT', 'AWVALID', 'AWREADY',
                              'WDATA', 'WSTRB', 'WLAST', 'WVALID', 'WREADY',
                              'BID', 'BRESP', 'BVALID', 'BREADY',
                              'ARID', 'ARADDR', 'ARLEN', 'ARSIZE', 'ARBURST', 'ARLOCK',
                              'ARCACHE', 'ARPROT', 'ARVALID', 'ARREADY',
                              'RID', 'RDATA', 'RRESP', 'RLAST', 'RVALID', 'RREADY']:
                    f.write(f",\n        .S{s}_{signal}(S{s}_{signal})")
                
                if features.get('enable_qos'):
                    f.write(f",\n        .S{s}_AWQOS(S{s}_AWQOS)")
                    f.write(f",\n        .S{s}_AWREGION(S{s}_AWREGION)")
                    f.write(f",\n        .S{s}_ARQOS(S{s}_ARQOS)")
                    f.write(f",\n        .S{s}_ARREGION(S{s}_ARREGION)")
                
                if features.get('enable_user'):
                    f.write(f",\n        .S{s}_AWUSER(S{s}_AWUSER)")
                    f.write(f",\n        .S{s}_WUSER(S{s}_WUSER)")
                    f.write(f",\n        .S{s}_BUSER(S{s}_BUSER)")
                    f.write(f",\n        .S{s}_ARUSER(S{s}_ARUSER)")
                    f.write(f",\n        .S{s}_RUSER(S{s}_RUSER)")
            
            f.write("\n    );\n\n")
        
        f.write("endmodule\n")
    
    print(f"✅ Generated integrated top file: {top_file}")
    
    # Update filelist.f
    filelist_file = os.path.join(rtl_dir, 'filelist.f')
    if os.path.exists(filelist_file):
        with open(filelist_file, 'a') as f:
            f.write(f"\n# Integrated top-level wrapper\n")
            f.write(f"{project_name}_integrated_top.v\n")
        print(f"✅ Updated filelist.f")
    
    return True

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 generate_integrated_top.py <rtl_directory> [options]")
        print("Options:")
        print("  --project=<name>     Project name (default: extracted from directory)")
        print("  --masters=<num>      Number of masters (default: 2)")
        print("  --slaves=<num>       Number of slaves (default: 2)")
        print("  --enable-qos         Enable QoS support")
        print("  --enable-region      Enable REGION support")
        print("  --enable-user        Enable USER signals")
        print("  --enable-firewall    Enable firewall")
        print("  --enable-cdc         Enable CDC")
        sys.exit(1)
    
    rtl_dir = sys.argv[1]
    if not os.path.exists(rtl_dir):
        print(f"Error: Directory {rtl_dir} does not exist!")
        sys.exit(1)
    
    # Parse options
    project_name = os.path.basename(os.path.dirname(rtl_dir))
    num_masters = 2
    num_slaves = 2
    features = {}
    
    for arg in sys.argv[2:]:
        if arg.startswith('--project='):
            project_name = arg.split('=')[1]
        elif arg.startswith('--masters='):
            num_masters = int(arg.split('=')[1])
        elif arg.startswith('--slaves='):
            num_slaves = int(arg.split('=')[1])
        elif arg == '--enable-qos':
            features['enable_qos'] = True
        elif arg == '--enable-region':
            features['enable_region'] = True
        elif arg == '--enable-user':
            features['enable_user'] = True
        elif arg == '--enable-firewall':
            features['enable_firewall'] = True
        elif arg == '--enable-cdc':
            features['enable_cdc'] = True
    
    print(f"Generating integrated top for project: {project_name}")
    print(f"Configuration: {num_masters} masters, {num_slaves} slaves")
    print(f"Features: {features}")
    
    success = generate_integrated_top(rtl_dir, project_name, num_masters, num_slaves, features)
    
    if success:
        print("\n✅ Integration complete!")
        print(f"Top file: {os.path.join(rtl_dir, project_name + '_integrated_top.v')}")
    else:
        print("\n❌ Integration failed!")
        sys.exit(1)

if __name__ == "__main__":
    main()