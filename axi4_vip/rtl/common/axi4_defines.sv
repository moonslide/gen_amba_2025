//==============================================================================
// AXI4 Common Definitions and Parameters
// 
// Description: Common definitions for AXI4 VIP components
// Based on ARM IHI 0022D AMBA AXI Protocol Specification
//==============================================================================

`ifndef AXI4_DEFINES_SV
`define AXI4_DEFINES_SV

// AXI4 Burst Types
typedef enum logic [1:0] {
    AXI4_BURST_FIXED = 2'b00,
    AXI4_BURST_INCR  = 2'b01,
    AXI4_BURST_WRAP  = 2'b10,
    AXI4_BURST_RSVD  = 2'b11
} axi4_burst_t;

// AXI4 Response Types
typedef enum logic [1:0] {
    AXI4_RESP_OKAY   = 2'b00,
    AXI4_RESP_EXOKAY = 2'b01,
    AXI4_RESP_SLVERR = 2'b10,
    AXI4_RESP_DECERR = 2'b11
} axi4_resp_t;

// AXI4 Lock Types
typedef enum logic {
    AXI4_LOCK_NORMAL    = 1'b0,
    AXI4_LOCK_EXCLUSIVE = 1'b1
} axi4_lock_t;

// AXI4 Protection Attributes
typedef struct packed {
    logic       instruction;  // [2] 0=data, 1=instruction
    logic       nonsecure;    // [1] 0=secure, 1=non-secure  
    logic       privileged;   // [0] 0=unprivileged, 1=privileged
} axi4_prot_t;

// AXI4 Cache Attributes
typedef struct packed {
    logic       allocate;     // [3] Write/Read allocate
    logic       other_alloc;  // [2] Other allocate
    logic       modifiable;   // [1] 0=non-modifiable, 1=modifiable
    logic       bufferable;   // [0] 0=non-bufferable, 1=bufferable
} axi4_cache_t;

// AXI4 QoS field width
`define AXI4_QOS_WIDTH 4

// AXI4 Region field width
`define AXI4_REGION_WIDTH 4

// Maximum burst lengths
`define AXI4_MAX_BURST_LEN_INCR 256
`define AXI4_MAX_BURST_LEN_OTHER 16

// 4KB boundary
`define AXI4_4KB_BOUNDARY 4096

// Exclusive access constraints
`define AXI4_EXCLUSIVE_MAX_BYTES 128

// Valid data bus widths (in bits)
`define AXI4_VALID_DATA_WIDTHS {8, 16, 32, 64, 128, 256, 512, 1024}

// AXI4 Channel IDs
typedef enum {
    AXI4_AW_CHANNEL,
    AXI4_W_CHANNEL,
    AXI4_B_CHANNEL,
    AXI4_AR_CHANNEL,
    AXI4_R_CHANNEL
} axi4_channel_t;

// Configuration structure for AXI4 components
typedef struct {
    int unsigned ADDR_WIDTH;
    int unsigned DATA_WIDTH;
    int unsigned ID_WIDTH;
    int unsigned AWUSER_WIDTH;
    int unsigned WUSER_WIDTH;
    int unsigned BUSER_WIDTH;
    int unsigned ARUSER_WIDTH;
    int unsigned RUSER_WIDTH;
    bit          SUPPORT_USER_SIGNALS;
    bit          SUPPORT_REGION;
    bit          SUPPORT_QOS;
    bit          SUPPORT_EXCLUSIVE;
} axi4_config_t;

// Transaction type for internal use
typedef struct {
    // Address channel
    logic [63:0]    addr;
    logic [7:0]     len;
    logic [2:0]     size;
    axi4_burst_t    burst;
    axi4_lock_t     lock;
    axi4_prot_t     prot;
    axi4_cache_t    cache;
    logic [3:0]     qos;
    logic [3:0]     region;
    logic [15:0]    id;
    
    // Data
    logic [1023:0]  data[];  // Dynamic array for burst data
    logic [127:0]   strb[];  // Write strobes
    
    // Response
    axi4_resp_t     resp[];  // Response for each beat
    
    // User signals
    logic [63:0]    awuser;
    logic [63:0]    wuser[];
    logic [63:0]    buser;
    logic [63:0]    aruser;
    logic [63:0]    ruser[];
    
    // Control
    bit             is_write;
    realtime        start_time;
    realtime        end_time;
} axi4_transaction_t;

// Utility functions
function automatic int axi4_addr_aligned(logic [63:0] addr, int size);
    return (addr % (1 << size)) == 0;
endfunction

function automatic bit axi4_crosses_4kb(logic [63:0] addr, int len, int size);
    logic [63:0] start_addr = addr;
    logic [63:0] end_addr = addr + (len * (1 << size)) - 1;
    return (start_addr[31:12] != end_addr[31:12]);
endfunction

function automatic logic [63:0] axi4_wrap_addr(logic [63:0] addr, int len, int size);
    logic [63:0] wrap_boundary;
    logic [63:0] upper_wrap_boundary;
    logic [63:0] total_bytes;
    
    total_bytes = len * (1 << size);
    wrap_boundary = (addr / total_bytes) * total_bytes;
    upper_wrap_boundary = wrap_boundary + total_bytes;
    
    if (addr >= upper_wrap_boundary) begin
        return wrap_boundary + (addr % total_bytes);
    end else begin
        return addr;
    end
endfunction

`endif // AXI4_DEFINES_SV