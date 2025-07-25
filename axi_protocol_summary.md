# AMBA AXI Protocol Specification - Key Technical Information

## 1. Protocol Version Information

### AXI3
- Original version described in Issue B of the specification
- Supports burst lengths of 1 to 16 transfers for all burst types
- Includes write data interleaving support with WID signal
- AWLEN[3:0] - 4-bit burst length field

### AXI4
- Extended version introduced in Issue C/D of the specification
- Extends burst length support for INCR burst type to 1 to 256 transfers
- Removes write data interleaving support (no WID signal)
- AWLEN[7:0] - 8-bit burst length field
- Adds QoS (Quality of Service) signaling
- Adds Region signaling for multiple address decode regions
- Adds User-defined signals (AxUSER, xUSER)

### AXI4-Lite
- Simplified subset for control register-style interfaces
- All transactions are single data transfer (burst length = 1)
- Data bus width limited to 32 or 64 bits
- No burst support, no ID signals

## 2. Key Signal Definitions and Purposes

### Global Signals
- **ACLK**: Global clock signal (all signals sampled on rising edge)
- **ARESETn**: Global reset signal (active LOW)

### Write Address Channel (AW)
- **AWID**: Write address ID (transaction identifier)
- **AWADDR**: Write address (first transfer in burst)
- **AWLEN**: Burst length (number of transfers minus 1)
- **AWSIZE**: Burst size (bytes per transfer, encoded as 2^AWSIZE)
- **AWBURST**: Burst type (FIXED, INCR, WRAP)
- **AWLOCK**: Lock type (exclusive access)
- **AWCACHE**: Memory type attributes
- **AWPROT**: Protection type (privilege/security/data/instruction)
- **AWQOS**: Quality of Service (AXI4 only)
- **AWREGION**: Region identifier (AXI4 only)
- **AWVALID/AWREADY**: Handshake signals

### Write Data Channel (W)
- **WID**: Write ID tag (AXI3 only, removed in AXI4)
- **WDATA**: Write data
- **WSTRB**: Write strobes (byte enables)
- **WLAST**: Last transfer in write burst
- **WUSER**: User-defined signal (AXI4 only)
- **WVALID/WREADY**: Handshake signals

### Write Response Channel (B)
- **BID**: Response ID
- **BRESP**: Write response (OKAY, EXOKAY, SLVERR, DECERR)
- **BUSER**: User-defined signal (AXI4 only)
- **BVALID/BREADY**: Handshake signals

### Read Address Channel (AR)
- **ARID**: Read address ID
- **ARADDR**: Read address
- **ARLEN**: Burst length
- **ARSIZE**: Burst size
- **ARBURST**: Burst type
- **ARLOCK**: Lock type
- **ARCACHE**: Memory type attributes
- **ARPROT**: Protection type
- **ARQOS**: Quality of Service (AXI4 only)
- **ARREGION**: Region identifier (AXI4 only)
- **ARVALID/ARREADY**: Handshake signals

### Read Data Channel (R)
- **RID**: Read ID tag
- **RDATA**: Read data
- **RRESP**: Read response
- **RLAST**: Last transfer in read burst
- **RUSER**: User-defined signal (AXI4 only)
- **RVALID/RREADY**: Handshake signals

## 3. Transaction Types and Burst Modes

### Burst Types
1. **FIXED (0b00)**
   - Address remains constant for every transfer
   - Used for FIFO access

2. **INCR (0b01)**
   - Incrementing burst
   - Address increments by transfer size
   - Most common for sequential memory access
   - AXI3: 1-16 transfers
   - AXI4: 1-256 transfers

3. **WRAP (0b10)**
   - Similar to INCR but wraps at address boundary
   - Burst length must be 2, 4, 8, or 16
   - Start address must be aligned to transfer size
   - Used for cache line accesses

### Burst Size Encoding (AxSIZE)
- 0b000: 1 byte per transfer
- 0b001: 2 bytes per transfer
- 0b010: 4 bytes per transfer
- 0b011: 8 bytes per transfer
- 0b100: 16 bytes per transfer
- 0b101: 32 bytes per transfer
- 0b110: 64 bytes per transfer
- 0b111: 128 bytes per transfer

### Data Bus Width Support
- 8, 16, 32, 64, 128, 256, 512, or 1024 bits

## 4. Ordering Rules and ID Usage

### Transaction ID Rules
- All transactions with same ID must remain ordered
- Transactions with different IDs can complete out-of-order
- Enables multiple outstanding transactions

### Ordering Requirements
1. **Read Ordering**
   - Read data with same ARID must return in address issue order

2. **Write Ordering**
   - Write data must be in same order as write addresses
   - Write responses with same AWID complete in address issue order

3. **AXI4 Ordering Model**
   - Transactions with same ID to same peripheral must arrive in order
   - Memory transactions with same ID to overlapping addresses must arrive in order
   - No ordering between read and write transactions

### Write Data Interleaving
- **AXI3**: Supports interleaved write data with different AWID values
- **AXI4**: Removed - all write data must be consecutive

## 5. Critical Implementation Requirements

### Address Constraints
1. **4KB Boundary Rule**
   - No burst can cross a 4KB (4096 byte) address boundary
   - Prevents crossing between different slaves
   - Limits address increment calculations

2. **Alignment Requirements**
   - WRAP bursts: start address must be aligned to transfer size
   - Unaligned transfers supported for INCR bursts

### Burst Constraints
1. **Early Termination**
   - Not supported - all transfers must complete
   - Master can deassert write strobes but must complete transfers
   - Master can discard read data but must complete transfers

2. **Burst Length Rules**
   - WRAP bursts: must be 2, 4, 8, or 16 transfers
   - FIXED/INCR in AXI3: 1-16 transfers
   - INCR in AXI4: 1-256 transfers

### Channel Independence
- All five channels are independent
- No fixed timing relationship between channels
- Enables register slice insertion for timing closure

### Response Requirements
- All write transactions require response on B channel
- Read responses include per-transfer RRESP
- Error responses: SLVERR (slave error), DECERR (decode error)

## 6. Memory Types and Attributes

### AXI3 Memory Types (AxCACHE)
- Bufferable/Non-bufferable
- Cacheable/Non-cacheable
- Read-allocate/Write-allocate

### AXI4 Memory Types
- Device (Non-bufferable, Bufferable)
- Normal (Non-cacheable, Write-through, Write-back)
- Updated encoding for better consistency

### Protection Attributes (AxPROT)
- Bit 0: Privileged/Unprivileged access
- Bit 1: Secure/Non-secure access
- Bit 2: Instruction/Data access

## 7. Additional Constraints and Limitations

### Maximum Outstanding Transactions
- Implementation specific
- Limited by ID width and system resources

### Exclusive Access
- Special atomic operations using AxLOCK
- AXI3: Exclusive and locked transfers
- AXI4: Only exclusive transfers (locked removed)

### Quality of Service (AXI4)
- 4-bit QoS identifier per transaction
- Implementation specific interpretation

### Region Support (AXI4)
- 4-bit region identifier
- Allows up to 16 decode regions per slave
- Enables different attributes per region

## 8. Key Implementation Considerations

1. **Interconnect Design**
   - Must maintain ordering per ID
   - Can reorder between different IDs
   - Must handle protocol width conversions

2. **Slave Interface**
   - Must calculate burst addresses
   - Must handle narrow transfers
   - Must generate appropriate responses

3. **Master Interface**
   - Must not exceed 4KB boundaries
   - Must handle response reordering
   - Must complete all burst transfers

4. **Clock Domain Crossing**
   - Each channel can have register slices
   - Asynchronous bridges possible
   - Must maintain protocol compliance