# ACE-Lite Implementation TODO List

## Overview
This document tracks the implementation progress for completing ACE-Lite (AXI Coherency Extensions Lite) support in the gen_amba_2025 project. The current implementation provides basic structural foundation but lacks critical coherency mechanisms.

**Current Implementation Status: ~30% complete**
- ✅ Basic module structure and domain/snoop signals
- ❌ Missing all actual coherency mechanisms
- ❌ No SD_xUSER signal support
- ❌ No coherency channels implementation

## Core Signal Infrastructure ⏳

### 1. Implement SD_xUSER signal generation for ACE-Lite
- [ ] Add SD_AWUSER, SD_WUSER, SD_BUSER, SD_ARUSER, SD_RUSER to generator
- [ ] Define coherency-specific bit field encoding
- [ ] Integrate with existing USER signal infrastructure
- [ ] Update `gen_axi_ace_lite.c` to include SD_xUSER ports
- [ ] Add coherency attribute encoding documentation

**Files to modify:**
- `gen_amba_axi/src/gen_axi_ace_lite.c`
- `gen_amba_axi/src/gen_amba_axi.h`

### 2. Add coherency channels (ACADDR, CRRESP, CDDATA) to ACE-Lite generator
- [ ] Implement ACADDR snoop address channel (interconnect → master)
- [ ] Add CRRESP coherency response channel (master → interconnect)
- [ ] Create CDDATA coherency data channel (master → interconnect)
- [ ] Ensure proper handshake timing compliance
- [ ] Add channel width parameters

**Signal Details:**
```systemverilog
// Snoop Address Channel
input  [ADDR_WIDTH-1:0] ACADDR    // Snoop address
input                   ACVALID   // Address valid
output                  ACREADY   // Address ready

// Coherency Response Channel
output [4:0]           CRRESP     // Snoop response
output                 CRVALID    // Response valid
input                  CRREADY    // Response ready

// Coherency Data Channel
output [DATA_WIDTH-1:0] CDDATA    // Snoop data
output                  CDVALID   // Data valid
input                   CDREADY   // Data ready
```

## Cache Coherency Logic ⏳

### 3. Implement MOESI cache state management logic
- [ ] Create 5-state cache model (Modified, Owned, Exclusive, Shared, Invalid)
- [ ] Add state transition logic for each cache line
- [ ] Implement cache line tracking per master ID
- [ ] Add state lookup tables and management functions
- [ ] Create cache state update mechanisms

**Files to create/modify:**
- `gen_amba_axi/src/ace_lite/coherency/gen_ace_lite_cache_states.c`

### 4. Create snoop invalidation mechanism in snoop filter
- [ ] Add write-invalidate protocol implementation
- [ ] Create address-based snoop broadcasting
- [ ] Implement selective snooping optimization
- [ ] Add cache line invalidation on write conflicts
- [ ] Enhance existing `gen_ace_lite_snoop_filter.c`

**Features needed:**
- Address range tracking
- Master cache state directory
- Invalidation broadcast logic
- Snoop response aggregation

## Transaction Management ⏳

### 5. Add ACE-Lite transaction type validation
- [ ] Restrict to Non-shared, Non-cached transactions only
- [ ] Add Cache Maintenance transaction support (CleanShared, CleanInvalid, MakeInvalid)
- [ ] Validate transaction compliance at generation time
- [ ] Add error reporting for invalid transaction types
- [ ] Update argument parser to validate ACE-Lite constraints

**Transaction types allowed in ACE-Lite:**
- ReadNoSnoop
- WriteNoSnoop  
- CleanShared
- CleanInvalid
- MakeInvalid

### 6. Implement barrier synchronization for memory ordering
- [ ] Add memory barrier transaction support
- [ ] Create ordering constraint enforcement
- [ ] Implement barrier completion tracking
- [ ] Add synchronization point management
- [ ] Update `gen_ace_lite_barrier_sync.c`

## Advanced Features ⏳

### 7. Add exclusive access monitoring for ACE-Lite masters
- [ ] Create exclusive access tracking per address/ID pair
- [ ] Implement EXOKAY/OKAY response logic
- [ ] Add exclusive state clearing on intervening writes
- [ ] Validate exclusive access alignment and size constraints
- [ ] Add exclusive monitor state machine

### 8. Create coherency controller state machine
- [ ] Implement central coherency management
- [ ] Add snoop request distribution logic
- [ ] Create response aggregation mechanism
- [ ] Add deadlock prevention logic
- [ ] Enhance `gen_ace_lite_coherency_controller.c`

## Performance Optimizations ⏳

### 9. Implement direct master-to-master data transfer optimization
- [ ] Add cache-to-cache transfer capability
- [ ] Bypass memory for clean shared data
- [ ] Implement speculative read support
- [ ] Add latency reduction optimizations
- [ ] Create master-to-master routing logic

## Integration & Testing ⏳

### 10. Add ACE-Lite VIP integration to existing GUI framework
- [ ] Extend VIP generator with ACE-Lite support
- [ ] Add coherency test sequence library
- [ ] Create ACE-Lite specific verification components
- [ ] Integrate with existing AXI4 VIP infrastructure
- [ ] Add ACE-Lite GUI configuration options

**Files to enhance:**
- `axi4_vip/gui/src/vip_gui_integration.py`
- `axi4_vip/gui/src/vip_environment_generator.py`

---

## Implementation Priority

### Phase 1: Foundation (Critical) 🔴
1. **SD_xUSER signal generation** - Required for coherency attributes
2. **Coherency channels implementation** - Core snoop communication
3. **MOESI state management** - Essential for cache coherency

### Phase 2: Core Functionality (High) 🟡  
4. **Snoop invalidation mechanism** - Write-invalidate protocol
5. **Transaction type validation** - Protocol compliance
6. **Barrier synchronization** - Memory ordering

### Phase 3: Advanced Features (Medium) 🟢
7. **Exclusive access monitoring** - Atomic operations
8. **Coherency controller** - Central management
9. **Performance optimizations** - Direct transfers

### Phase 4: DVM and System-Level Features (High) 🔴
10. **DVM (Distributed Virtual Memory) Transaction Support** - Virtual memory coherency
11. **Advanced Cache Maintenance Operations** - Complete cache ops with tracking
12. **System-Level Coordination** - Global coherency management
13. **TLB Invalidation** - Distributed virtual memory management

### Phase 5: Integration (Low) 🔵
14. **VIP integration** - Testing and verification

---

## Phase 4: DVM and System-Level Implementation Details

### 10. DVM (Distributed Virtual Memory) Transaction Support
- [ ] Implement DVM message transaction types (DVM_MESSAGE, DVM_COMPLETE)
- [ ] Add DVM synchronization logic across all masters
- [ ] Create DVM message routing and distribution
- [ ] Add virtual-to-physical address translation coherency
- [ ] Implement DVM completion tracking and acknowledgment
- [ ] Add timeout handling for DVM operations

**DVM Transaction Types:**
```systemverilog
// DVM Message Types
localparam [7:0] DVM_TLBI_ALL       = 8'h00; // Invalidate all TLB entries
localparam [7:0] DVM_TLBI_ASID      = 8'h01; // Invalidate by ASID
localparam [7:0] DVM_TLBI_VA        = 8'h02; // Invalidate by VA
localparam [7:0] DVM_TLBI_VAA       = 8'h03; // Invalidate by VA and ASID
```

**Files to create/modify:**
- `gen_amba_axi/src/ace_lite/dvm/gen_ace_lite_dvm_controller.c`

### 11. Advanced Cache Maintenance Operations
- [ ] Implement comprehensive cache maintenance transaction types
- [ ] Add cache maintenance completion tracking per master
- [ ] Create cache maintenance result aggregation
- [ ] Add cache maintenance timeout and error handling
- [ ] Implement maintenance operation queuing and scheduling
- [ ] Add maintenance operation conflict resolution

**Advanced Cache Operations:**
```systemverilog
// Enhanced Cache Maintenance Types
localparam [3:0] MAINT_CLEAN_POC           = 4'h0; // Clean to Point of Coherency
localparam [3:0] MAINT_CLEAN_POU           = 4'h1; // Clean to Point of Unification
localparam [3:0] MAINT_CLEAN_INV_POC       = 4'h2; // Clean and Invalidate to PoC
localparam [3:0] MAINT_INV_POC             = 4'h3; // Invalidate to PoC
```

**Files to enhance:**
- `gen_amba_axi/src/ace_lite/cache_ops/gen_ace_lite_cache_ops.c`

### 12. System-Level Coordination
- [ ] Implement global barrier coordination across all masters
- [ ] Add system-level transaction ordering enforcement
- [ ] Create inter-master communication channels
- [ ] Add global coherency state management
- [ ] Implement system-wide deadlock prevention
- [ ] Add global performance monitoring and statistics

**System Coordination Features:**
- Global barrier synchronization points
- Cross-master dependency tracking
- System-wide coherency violation detection
- Global transaction ordering enforcement

**Files to create/modify:**
- `gen_amba_axi/src/ace_lite/system/gen_ace_lite_system_coordinator.c`

### 13. TLB Invalidation Support
- [ ] Implement TLB invalidation message distribution
- [ ] Add per-master TLB invalidation tracking
- [ ] Create TLB invalidation completion acknowledgment
- [ ] Add ASID (Address Space ID) management
- [ ] Implement virtual address range invalidation
- [ ] Add TLB maintenance operation scheduling

**TLB Invalidation Features:**
```systemverilog
// TLB Invalidation Types
localparam [2:0] TLB_INV_ALL        = 3'b000; // Invalidate all entries
localparam [2:0] TLB_INV_ASID       = 3'b001; // Invalidate by ASID
localparam [2:0] TLB_INV_VA         = 3'b010; // Invalidate by Virtual Address
localparam [2:0] TLB_INV_VA_ASID    = 3'b011; // Invalidate by VA and ASID
```

**Files to create/modify:**
- `gen_amba_axi/src/ace_lite/dvm/gen_ace_lite_tlb_manager.c`

---

## Key References

- **ARM IHI0022D**: AMBA AXI and ACE Protocol Specification
- **Current ACE-Lite files**: `gen_amba_axi/src/ace_lite/`
- **Existing snoop filter**: `ace_lite/coherency/gen_ace_lite_snoop_filter.c`
- **Main ACE-Lite generator**: `gen_amba_axi/src/gen_axi_ace_lite.c`

---

## Notes

- **Missing Critical Components**: SD_xUSER signals, coherency channels (ACADDR/CRRESP/CDDATA)
- **Partial Implementation**: Basic module structure exists but no actual coherency logic
- **Integration Point**: ACE-Lite should integrate with existing AXI4 VIP framework
- **Testing Strategy**: Need comprehensive coherency test sequences for validation

**Last Updated**: 2025-09-05  
**Status**: Planning phase - ready for implementation