# AXI4 Modular Interconnect Architecture Design

## Current Problem
The existing RTL generator creates a single monolithic interconnect module with **3,393 lines** of Verilog code, making it:
- **Hard to debug** - All logic mixed together
- **Difficult to simulate** - Cannot isolate specific components
- **Hard to maintain** - Changes affect the entire design
- **Poor reusability** - Cannot use individual components separately

## Proposed Modular Architecture

### 1. Master Interface Modules (16 instances)
```verilog
module axi4_master_interface #(
    parameter MASTER_ID = 0,
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 64,
    parameter ID_WIDTH = 4
)(
    // Clock and Reset
    input wire aclk, aresetn,
    
    // External Master Interface
    input wire [ID_WIDTH-1:0] M_AWID, M_ARID,
    input wire [ADDR_WIDTH-1:0] M_AWADDR, M_ARADDR,
    // ... all AXI4 master signals
    
    // Internal Interconnect Interface
    output wire [ID_WIDTH-1:0] int_awid, int_arid,
    output wire [ADDR_WIDTH-1:0] int_awaddr, int_araddr,
    // ... internal signals to crossbar
);
```
**Features:**
- Protocol compliance checking
- Transaction buffering
- Master-specific configuration
- Debug ports and counters

### 2. Slave Interface Modules (16 instances) 
```verilog
module axi4_slave_interface #(
    parameter SLAVE_ID = 0,
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 64,
    parameter ID_WIDTH = 4
)(
    // Clock and Reset
    input wire aclk, aresetn,
    
    // Internal Interconnect Interface
    input wire [ID_WIDTH-1:0] int_awid, int_arid,
    input wire [ADDR_WIDTH-1:0] int_awaddr, int_araddr,
    // ... internal signals from crossbar
    
    // External Slave Interface
    output wire [ID_WIDTH-1:0] S_AWID, S_ARID,
    output wire [ADDR_WIDTH-1:0] S_AWADDR, S_ARADDR,
    // ... all AXI4 slave signals
);
```
**Features:**
- Response handling
- Outstanding transaction tracking
- Slave-specific configuration
- Performance monitoring

### 3. Address Decoder Module
```verilog
module axi4_address_decoder #(
    parameter NUM_MASTERS = 16,
    parameter NUM_SLAVES = 16,
    parameter ADDR_WIDTH = 32
)(
    // Address inputs from all masters
    input wire [ADDR_WIDTH-1:0] master_awaddr [NUM_MASTERS-1:0],
    input wire [ADDR_WIDTH-1:0] master_araddr [NUM_MASTERS-1:0],
    input wire [NUM_MASTERS-1:0] master_awvalid, master_arvalid,
    
    // Decode outputs
    output wire [NUM_SLAVES-1:0] aw_decode [NUM_MASTERS-1:0],
    output wire [NUM_SLAVES-1:0] ar_decode [NUM_MASTERS-1:0],
    output wire [NUM_MASTERS-1:0] decode_error_aw, decode_error_ar
);
```
**Features:**
- Configurable memory map
- Error detection for unmapped addresses
- 4KB boundary checking
- Debug visibility

### 4. Write Channel Arbiters (16 instances - one per slave)
```verilog
module axi4_write_arbiter #(
    parameter NUM_MASTERS = 16,
    parameter SLAVE_ID = 0,
    parameter ARB_SCHEME = 0  // 0=round-robin, 1=fixed priority
)(
    input wire aclk, aresetn,
    
    // Requests from masters
    input wire [NUM_MASTERS-1:0] aw_request,
    input wire [NUM_MASTERS-1:0] w_request,
    
    // Grant outputs
    output wire [NUM_MASTERS-1:0] aw_grant,
    output wire [NUM_MASTERS-1:0] w_grant,
    
    // Status and debug
    output wire [NUM_MASTERS-1:0] starvation_detected,
    output wire [$clog2(NUM_MASTERS)-1:0] current_master
);
```
**Features:**
- Multiple arbitration algorithms
- Starvation prevention
- QoS-based prioritization
- Performance counters

### 5. Read Channel Arbiters (16 instances - one per slave)
```verilog
module axi4_read_arbiter #(
    parameter NUM_MASTERS = 16,
    parameter SLAVE_ID = 0,
    parameter ARB_SCHEME = 0
)(
    input wire aclk, aresetn,
    
    // Requests from masters
    input wire [NUM_MASTERS-1:0] ar_request,
    
    // Grant outputs  
    output wire [NUM_MASTERS-1:0] ar_grant,
    
    // Status and debug
    output wire [NUM_MASTERS-1:0] starvation_detected,
    output wire [$clog2(NUM_MASTERS)-1:0] current_master
);
```

### 6. Write Data Crossbar
```verilog
module axi4_write_crossbar #(
    parameter NUM_MASTERS = 16,
    parameter NUM_SLAVES = 16,
    parameter DATA_WIDTH = 64
)(
    // Master write data inputs
    input wire [DATA_WIDTH-1:0] m_wdata [NUM_MASTERS-1:0],
    input wire [(DATA_WIDTH/8)-1:0] m_wstrb [NUM_MASTERS-1:0],
    input wire [NUM_MASTERS-1:0] m_wlast, m_wvalid,
    
    // Grant signals from arbiters
    input wire [NUM_MASTERS-1:0] w_grant [NUM_SLAVES-1:0],
    
    // Slave write data outputs
    output wire [DATA_WIDTH-1:0] s_wdata [NUM_SLAVES-1:0],
    output wire [(DATA_WIDTH/8)-1:0] s_wstrb [NUM_SLAVES-1:0],
    output wire [NUM_SLAVES-1:0] s_wlast, s_wvalid
);
```

### 7. Read Data Crossbar  
```verilog
module axi4_read_crossbar #(
    parameter NUM_MASTERS = 16,
    parameter NUM_SLAVES = 16,
    parameter DATA_WIDTH = 64,
    parameter ID_WIDTH = 4
)(
    // Slave read data inputs
    input wire [DATA_WIDTH-1:0] s_rdata [NUM_SLAVES-1:0],
    input wire [1:0] s_rresp [NUM_SLAVES-1:0],
    input wire [NUM_SLAVES-1:0] s_rlast, s_rvalid,
    input wire [ID_WIDTH-1:0] s_rid [NUM_SLAVES-1:0],
    
    // Master read data outputs (with routing)
    output wire [DATA_WIDTH-1:0] m_rdata [NUM_MASTERS-1:0],
    output wire [1:0] m_rresp [NUM_MASTERS-1:0],
    output wire [NUM_MASTERS-1:0] m_rlast, m_rvalid,
    output wire [ID_WIDTH-1:0] m_rid [NUM_MASTERS-1:0]
);
```

### 8. Write Response Crossbar
```verilog
module axi4_write_response_crossbar #(
    parameter NUM_MASTERS = 16,
    parameter NUM_SLAVES = 16,
    parameter ID_WIDTH = 4
)(
    // Slave write response inputs
    input wire [1:0] s_bresp [NUM_SLAVES-1:0],
    input wire [NUM_SLAVES-1:0] s_bvalid,
    input wire [ID_WIDTH-1:0] s_bid [NUM_SLAVES-1:0],
    
    // Master write response outputs (with routing)
    output wire [1:0] m_bresp [NUM_MASTERS-1:0],
    output wire [NUM_MASTERS-1:0] m_bvalid,
    output wire [ID_WIDTH-1:0] m_bid [NUM_MASTERS-1:0]
);
```

### 9. Pipeline Stage Modules (Optional)
```verilog
module axi4_pipeline_stage #(
    parameter DATA_WIDTH = 64,
    parameter ADDR_WIDTH = 32,
    parameter ID_WIDTH = 4,
    parameter STAGE_ID = 1
)(
    input wire aclk, aresetn,
    
    // Input stage
    input wire [ADDR_WIDTH-1:0] in_awaddr, in_araddr,
    input wire [DATA_WIDTH-1:0] in_wdata, in_rdata,
    // ... all AXI signals
    
    // Output stage  
    output wire [ADDR_WIDTH-1:0] out_awaddr, out_araddr,
    output wire [DATA_WIDTH-1:0] out_wdata, out_rdata,
    // ... all AXI signals
);
```

### 10. User Signal Processor Module
```verilog
module axi4_user_processor #(
    parameter USER_WIDTH = 6,
    parameter NUM_MASTERS = 16,
    parameter NUM_SLAVES = 16
)(
    input wire aclk, aresetn,
    
    // Master USER signals
    input wire [USER_WIDTH-1:0] m_awuser [NUM_MASTERS-1:0],
    input wire [USER_WIDTH-1:0] m_wuser [NUM_MASTERS-1:0],
    input wire [USER_WIDTH-1:0] m_aruser [NUM_MASTERS-1:0],
    
    // Processed USER signals to slaves
    output wire [USER_WIDTH-1:0] s_awuser [NUM_SLAVES-1:0],
    output wire [USER_WIDTH-1:0] s_wuser [NUM_SLAVES-1:0],
    output wire [USER_WIDTH-1:0] s_aruser [NUM_SLAVES-1:0],
    
    // Response USER signals
    input wire [USER_WIDTH-1:0] s_buser [NUM_SLAVES-1:0],
    input wire [USER_WIDTH-1:0] s_ruser [NUM_SLAVES-1:0],
    output wire [USER_WIDTH-1:0] m_buser [NUM_MASTERS-1:0],
    output wire [USER_WIDTH-1:0] m_ruser [NUM_MASTERS-1:0]
);
```

### 11. QoS Controller Module
```verilog
module axi4_qos_controller #(
    parameter NUM_MASTERS = 16,
    parameter NUM_SLAVES = 16,
    parameter QOS_WIDTH = 4
)(
    input wire aclk, aresetn,
    
    // QoS inputs from masters
    input wire [QOS_WIDTH-1:0] m_awqos [NUM_MASTERS-1:0],
    input wire [QOS_WIDTH-1:0] m_arqos [NUM_MASTERS-1:0],
    
    // Priority outputs to arbiters
    output wire [QOS_WIDTH-1:0] master_priority [NUM_MASTERS-1:0],
    output wire [NUM_MASTERS-1:0] urgent_request,
    
    // Configuration interface
    input wire qos_enable,
    input wire [1:0] qos_algorithm  // 0=strict, 1=weighted, 2=deficit
);
```

### 12. Exclusive Access Monitor
```verilog
module axi4_exclusive_monitor #(
    parameter NUM_MASTERS = 16,
    parameter ADDR_WIDTH = 32,
    parameter ID_WIDTH = 4,
    parameter MAX_MONITORS = 8
)(
    input wire aclk, aresetn,
    
    // Exclusive read tracking
    input wire [NUM_MASTERS-1:0] ar_lock,
    input wire [ADDR_WIDTH-1:0] ar_addr [NUM_MASTERS-1:0],
    input wire [ID_WIDTH-1:0] ar_id [NUM_MASTERS-1:0],
    input wire [NUM_MASTERS-1:0] ar_valid,
    
    // Exclusive write checking
    input wire [NUM_MASTERS-1:0] aw_lock,  
    input wire [ADDR_WIDTH-1:0] aw_addr [NUM_MASTERS-1:0],
    input wire [ID_WIDTH-1:0] aw_id [NUM_MASTERS-1:0],
    input wire [NUM_MASTERS-1:0] aw_valid,
    
    // Exclusive response
    output wire [NUM_MASTERS-1:0] exclusive_okay
);
```

### 13. Top-Level Interconnect (Integration Module)
```verilog
module axi4_project_interconnect_top #(
    parameter NUM_MASTERS = 16,
    parameter NUM_SLAVES = 16,
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 64,
    parameter ID_WIDTH = 4,
    parameter USER_WIDTH = 6
)(
    input wire aclk, aresetn,
    
    // External Master Interfaces (16 sets)
    input wire [ID_WIDTH-1:0] M0_AWID, M0_ARID,
    // ... all master signals M0-M15
    
    // External Slave Interfaces (16 sets)  
    output wire [ID_WIDTH-1:0] S0_AWID, S0_ARID,
    // ... all slave signals S0-S15
);

    // Internal interconnect signals
    wire [ADDR_WIDTH-1:0] int_master_awaddr [NUM_MASTERS-1:0];
    wire [ADDR_WIDTH-1:0] int_master_araddr [NUM_MASTERS-1:0];
    // ... internal buses
    
    // Master interface instances
    genvar gm;
    generate
        for (gm = 0; gm < NUM_MASTERS; gm = gm + 1) begin : master_if
            axi4_master_interface #(
                .MASTER_ID(gm),
                .ADDR_WIDTH(ADDR_WIDTH),
                .DATA_WIDTH(DATA_WIDTH),
                .ID_WIDTH(ID_WIDTH)
            ) u_master_if (
                .aclk(aclk),
                .aresetn(aresetn),
                // Connect external and internal signals
                // ... port connections
            );
        end
    endgenerate
    
    // Slave interface instances  
    genvar gs;
    generate
        for (gs = 0; gs < NUM_SLAVES; gs = gs + 1) begin : slave_if
            axi4_slave_interface #(
                .SLAVE_ID(gs),
                .ADDR_WIDTH(ADDR_WIDTH), 
                .DATA_WIDTH(DATA_WIDTH),
                .ID_WIDTH(ID_WIDTH)
            ) u_slave_if (
                .aclk(aclk),
                .aresetn(aresetn),
                // Connect internal and external signals
                // ... port connections  
            );
        end
    endgenerate
    
    // Address decoder
    axi4_address_decoder #(
        .NUM_MASTERS(NUM_MASTERS),
        .NUM_SLAVES(NUM_SLAVES),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) u_addr_decoder (
        .master_awaddr(int_master_awaddr),
        .master_araddr(int_master_araddr),
        // ... connections
    );
    
    // Write arbiters for each slave
    generate
        for (gs = 0; gs < NUM_SLAVES; gs = gs + 1) begin : write_arb
            axi4_write_arbiter #(
                .NUM_MASTERS(NUM_MASTERS),
                .SLAVE_ID(gs)
            ) u_write_arbiter (
                .aclk(aclk),
                .aresetn(aresetn),
                // ... connections
            );
        end
    endgenerate
    
    // Read arbiters for each slave
    generate  
        for (gs = 0; gs < NUM_SLAVES; gs = gs + 1) begin : read_arb
            axi4_read_arbiter #(
                .NUM_MASTERS(NUM_MASTERS),
                .SLAVE_ID(gs)
            ) u_read_arbiter (
                .aclk(aclk),
                .aresetn(aresetn),
                // ... connections
            );
        end
    endgenerate
    
    // Data crossbars
    axi4_write_crossbar #(
        .NUM_MASTERS(NUM_MASTERS),
        .NUM_SLAVES(NUM_SLAVES),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_write_crossbar (
        // ... connections
    );
    
    axi4_read_crossbar #(
        .NUM_MASTERS(NUM_MASTERS),
        .NUM_SLAVES(NUM_SLAVES), 
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH)
    ) u_read_crossbar (
        // ... connections
    );
    
    axi4_write_response_crossbar #(
        .NUM_MASTERS(NUM_MASTERS),
        .NUM_SLAVES(NUM_SLAVES),
        .ID_WIDTH(ID_WIDTH)
    ) u_bresp_crossbar (
        // ... connections
    );
    
    // Optional feature modules
    generate
        if (USER_WIDTH > 0) begin : user_proc
            axi4_user_processor #(
                .USER_WIDTH(USER_WIDTH),
                .NUM_MASTERS(NUM_MASTERS),
                .NUM_SLAVES(NUM_SLAVES)
            ) u_user_processor (
                // ... connections
            );
        end
    endgenerate
    
    // QoS controller
    axi4_qos_controller #(
        .NUM_MASTERS(NUM_MASTERS),
        .NUM_SLAVES(NUM_SLAVES)
    ) u_qos_controller (
        // ... connections  
    );
    
    // Exclusive access monitor
    axi4_exclusive_monitor #(
        .NUM_MASTERS(NUM_MASTERS),
        .ADDR_WIDTH(ADDR_WIDTH),
        .ID_WIDTH(ID_WIDTH)
    ) u_exclusive_monitor (
        // ... connections
    );

endmodule
```

## File Structure
```
rtl_out/
├── filelist.f                              # Master filelist
├── axi4_project_interconnect_top.v         # Top-level integration (~500 lines)
├── interfaces/
│   ├── axi4_master_interface.v             # Master interface (~200 lines each)
│   ├── axi4_slave_interface.v              # Slave interface (~200 lines each)
├── decoders/
│   └── axi4_address_decoder.v              # Address decoder (~300 lines)
├── arbiters/
│   ├── axi4_write_arbiter.v                # Write arbiter (~250 lines)
│   └── axi4_read_arbiter.v                 # Read arbiter (~200 lines)
├── crossbars/
│   ├── axi4_write_crossbar.v               # Write data crossbar (~300 lines)
│   ├── axi4_read_crossbar.v                # Read data crossbar (~300 lines)
│   └── axi4_write_response_crossbar.v      # Write response crossbar (~200 lines)
├── features/
│   ├── axi4_user_processor.v               # USER signal processor (~150 lines)
│   ├── axi4_qos_controller.v               # QoS controller (~250 lines)
│   ├── axi4_exclusive_monitor.v            # Exclusive access (~200 lines)
└── pipeline/
    └── axi4_pipeline_stage.v               # Pipeline stage (~200 lines)
```

## Benefits of Modular Architecture

### 1. **Debugging Advantages**
- **Isolated Testing**: Test each module independently
- **Clear Boundaries**: Easy to identify which module has issues  
- **Waveform Analysis**: Focus on specific module signals
- **Unit Testing**: Each module can be tested separately

### 2. **Simulation Advantages**  
- **Faster Compilation**: Only recompile changed modules
- **Selective Simulation**: Simulate specific paths
- **Better Performance**: Smaller modules simulate faster
- **Parallel Development**: Multiple engineers can work on different modules

### 3. **Maintenance Advantages**
- **Modular Updates**: Change individual modules without affecting others
- **Code Reuse**: Use modules in different configurations
- **Documentation**: Each module has focused documentation
- **Version Control**: Track changes per module

### 4. **Synthesis Advantages**
- **Better Optimization**: Tools can optimize each module separately
- **Timing Closure**: Easier to meet timing per module
- **Resource Usage**: Clear resource usage per function
- **Physical Design**: Better floorplanning with module boundaries

## Implementation Plan

### Phase 1: Core Infrastructure
1. Create modular C generator functions
2. Implement basic module templates
3. Generate master/slave interfaces
4. Create address decoder module

### Phase 2: Arbitration & Crossbars
1. Implement write/read arbiters
2. Create data crossbar modules
3. Add response routing
4. Test basic connectivity

### Phase 3: Advanced Features
1. Add QoS controller
2. Implement USER signal processor
3. Create exclusive access monitor
4. Add pipeline stages

### Phase 4: Integration & Testing
1. Create top-level integration
2. Generate comprehensive filelist
3. Test modular compilation
4. Verify functionality

## Debug Features Per Module

Each module will include:
- **Debug ports**: Status and error signals
- **Performance counters**: Transaction counts, latency metrics
- **Configuration interfaces**: Runtime programmable parameters
- **Assertion coverage**: Built-in protocol checks
- **Simulation helpers**: Display tasks and debug functions

This modular approach transforms a 3,393-line monolithic module into ~13 focused modules of 150-300 lines each, making the design much more manageable for debugging and maintenance.