//==============================================================================
// AXI4 Transaction Item - Complete UVM sequence item implementation
// Supports all AXI4 protocol features including QoS, regions, exclusive access
//==============================================================================

class axi4_transaction extends uvm_sequence_item;
    
    // Factory registration
    `uvm_object_utils(axi4_transaction)
    
    // Transaction parameters (set by test environment)
    parameter int ADDR_WIDTH = 32;
    parameter int DATA_WIDTH = 64;
    parameter int ID_WIDTH   = 4;
    parameter int USER_WIDTH = 1;
    parameter int WSTRB_WIDTH = DATA_WIDTH/8;
    
    // Transaction type enumeration
    typedef enum {READ_TRANS, WRITE_TRANS} trans_type_e;
    typedef enum {FIXED, INCR, WRAP, RESERVED} burst_type_e;
    typedef enum {OKAY, EXOKAY, SLVERR, DECERR} resp_type_e;
    typedef enum {UNPRIVILEGED, PRIVILEGED} privilege_e;
    typedef enum {SECURE, NON_SECURE} security_e;
    typedef enum {DATA_ACCESS, INSTRUCTION_ACCESS} access_type_e;
    
    // Primary transaction fields
    rand trans_type_e   trans_type;
    rand bit [ADDR_WIDTH-1:0] addr;
    rand bit [ID_WIDTH-1:0]   id;
    rand bit [7:0]            len;          // 0-255 (1-256 transfers)
    rand bit [2:0]            size;         // 1,2,4,8,16,32,64,128 bytes
    rand burst_type_e         burst_type;
    
    // AXI4 specific signals
    rand bit                  lock;         // Always 0 for AXI4
    rand bit [3:0]            cache;        // Cache attributes
    rand privilege_e          privilege;    // Protection[0]
    rand security_e           security;     // Protection[1] 
    rand access_type_e        access_type;  // Protection[2]
    rand bit [3:0]            qos;          // Quality of Service
    rand bit [3:0]            region;       // Region identifier
    rand bit [USER_WIDTH-1:0] user;         // User signals
    
    // Data payload
    rand bit [DATA_WIDTH-1:0] data[];       // Write data
    rand bit [WSTRB_WIDTH-1:0] strb[];      // Write strobes
    rand bit [USER_WIDTH-1:0] wuser[];      // Write user signals
    
    // Response information (populated by slave)
    resp_type_e bresp, rresp[];             // Response codes
    bit [DATA_WIDTH-1:0] rdata[];           // Read data
    bit [USER_WIDTH-1:0] ruser[], buser;    // Response user signals
    
    // Timing information
    rand int addr_delay;                    // Cycles before address valid
    rand int data_delay[];                  // Cycles before each data beat
    rand int resp_delay[];                  // Cycles before response ready
    
    // Exclusive access tracking
    rand bit exclusive_access;              // Mark as exclusive transaction
    bit exclusive_okay;                     // Set by monitor for exclusive success
    
    // Error injection controls
    rand bit inject_addr_error;             // Force address phase error
    rand bit inject_data_error;             // Force data phase error
    rand bit inject_4kb_violation;          // Force 4KB boundary crossing
    
    //==========================================================================
    // Constraints
    //==========================================================================
    
    // Basic AXI4 protocol constraints
    constraint c_basic_protocol {
        // Burst length constraints
        len inside {[0:255]};
        
        // Size must be power of 2, max 128 bytes
        size inside {0, 1, 2, 3, 4, 5, 6, 7}; // 1,2,4,8,16,32,64,128 bytes
        
        // Burst type constraints
        burst_type != RESERVED;
        
        // Lock is always 0 for AXI4
        lock == 1'b0;
        
        // QoS and region valid ranges
        qos inside {[0:15]};
        region inside {[0:15]};
    }
    
    // WRAP burst specific constraints
    constraint c_wrap_burst {
        if (burst_type == WRAP) {
            // WRAP burst length must be 2, 4, 8, or 16
            len inside {1, 3, 7, 15}; // len+1 = 2,4,8,16
            
            // Address must be aligned to wrap boundary
            (addr % ((len + 1) * (1 << size))) == 0;
        }
    }
    
    // 4KB boundary constraint (critical for AXI4)
    constraint c_4kb_boundary {
        if (!inject_4kb_violation) {
            // Ensure transaction doesn't cross 4KB boundary
            (addr & 12'hFFF) + ((len + 1) * (1 << size)) <= 4096;
        }
    }
    
    // Data array sizing constraint
    constraint c_data_size {
        data.size() == len + 1;
        strb.size() == len + 1;
        wuser.size() == len + 1;
        data_delay.size() == len + 1;
        
        // Response arrays for read transactions
        if (trans_type == READ_TRANS) {
            rdata.size() == len + 1;
            rresp.size() == len + 1;
            ruser.size() == len + 1;
            resp_delay.size() == len + 1;
        }
    }
    
    // Realistic timing constraints
    constraint c_timing {
        addr_delay inside {[0:10]};
        foreach (data_delay[i]) {
            data_delay[i] inside {[0:5]};
        }
        foreach (resp_delay[i]) {
            resp_delay[i] inside {[0:10]};
        }
    }
    
    // Error injection probability (low probability for normal testing)
    constraint c_error_injection {
        inject_addr_error dist {0 := 95, 1 := 5};
        inject_data_error dist {0 := 95, 1 := 5};
        inject_4kb_violation dist {0 := 98, 1 := 2};
    }
    
    // Strobe constraint - must be contiguous for normal operation
    constraint c_strobe_pattern {
        if (!inject_data_error) {
            foreach (strb[i]) {
                $countones(strb[i]) > 0; // At least one byte enabled
                // For aligned transfers, strobes should be contiguous
                if ((addr + i * (1 << size)) % (1 << size) == 0) {
                    strb[i] == (1 << (1 << size)) - 1;
                }
            }
        }
    }
    
    //==========================================================================
    // Constructor
    //==========================================================================
    
    function new(string name = "axi4_transaction");
        super.new(name);
    endfunction
    
    //==========================================================================
    // Utility Functions
    //==========================================================================
    
    // Calculate total transfer size in bytes
    function int get_total_bytes();
        return (len + 1) * (1 << size);
    endfunction
    
    // Get aligned address for transfer
    function bit [ADDR_WIDTH-1:0] get_aligned_addr();
        return addr & ~((1 << size) - 1);
    endfunction
    
    // Check if transaction crosses 4KB boundary
    function bit crosses_4kb_boundary();
        bit [ADDR_WIDTH-1:0] start_addr = addr;
        bit [ADDR_WIDTH-1:0] end_addr = addr + get_total_bytes() - 1;
        return (start_addr[ADDR_WIDTH-1:12] != end_addr[ADDR_WIDTH-1:12]);
    endfunction
    
    // Generate AxPROT value
    function bit [2:0] get_prot();
        return {access_type, security, privilege};
    endfunction
    
    // Randomize with specific constraints for different test scenarios
    function bit randomize_basic();
        return this.randomize() with {
            trans_type dist {READ_TRANS := 50, WRITE_TRANS := 50};
            burst_type dist {INCR := 70, FIXED := 20, WRAP := 10};
            len inside {[0:15]}; // Shorter bursts for basic testing
            size inside {[0:3]}; // Up to 8-byte transfers
            inject_addr_error == 0;
            inject_data_error == 0;
            inject_4kb_violation == 0;
        };
    endfunction
    
    function bit randomize_burst();
        return this.randomize() with {
            len inside {[8:255]};  // Longer bursts
            burst_type dist {INCR := 60, WRAP := 40};
            size inside {[2:6]};   // 4-64 byte transfers
        };
    endfunction
    
    function bit randomize_exclusive();
        return this.randomize() with {
            exclusive_access == 1;
            len inside {[0:7]};    // Shorter for exclusive
            burst_type == INCR;    // INCR only for exclusive
        };
    endfunction
    
    //==========================================================================
    // UVM Methods
    //==========================================================================
    
    virtual function void do_copy(uvm_object rhs);
        axi4_transaction rhs_;
        if (!$cast(rhs_, rhs)) begin
            `uvm_fatal("DO_COPY", "Cast failed")
        end
        
        super.do_copy(rhs);
        
        this.trans_type = rhs_.trans_type;
        this.addr = rhs_.addr;
        this.id = rhs_.id;
        this.len = rhs_.len;
        this.size = rhs_.size;
        this.burst_type = rhs_.burst_type;
        this.lock = rhs_.lock;
        this.cache = rhs_.cache;
        this.privilege = rhs_.privilege;
        this.security = rhs_.security;
        this.access_type = rhs_.access_type;
        this.qos = rhs_.qos;
        this.region = rhs_.region;
        this.user = rhs_.user;
        
        this.data = rhs_.data;
        this.strb = rhs_.strb;
        this.wuser = rhs_.wuser;
        this.bresp = rhs_.bresp;
        this.rresp = rhs_.rresp;
        this.rdata = rhs_.rdata;
        this.ruser = rhs_.ruser;
        this.buser = rhs_.buser;
        
        this.addr_delay = rhs_.addr_delay;
        this.data_delay = rhs_.data_delay;
        this.resp_delay = rhs_.resp_delay;
        
        this.exclusive_access = rhs_.exclusive_access;
        this.exclusive_okay = rhs_.exclusive_okay;
        
        this.inject_addr_error = rhs_.inject_addr_error;
        this.inject_data_error = rhs_.inject_data_error;
        this.inject_4kb_violation = rhs_.inject_4kb_violation;
    endfunction
    
    virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        axi4_transaction rhs_;
        if (!$cast(rhs_, rhs)) return 0;
        
        return (super.do_compare(rhs, comparer) &&
                (this.trans_type == rhs_.trans_type) &&
                (this.addr == rhs_.addr) &&
                (this.id == rhs_.id) &&
                (this.len == rhs_.len) &&
                (this.size == rhs_.size) &&
                (this.burst_type == rhs_.burst_type) &&
                (this.data == rhs_.data) &&
                (this.strb == rhs_.strb));
    endfunction
    
    virtual function string convert2string();
        string s;
        s = $sformatf("AXI4_TRANS: %s, ID=0x%0h, Addr=0x%0h, Len=%0d, Size=%0d, Burst=%s",
                      trans_type.name(), id, addr, len+1, 1<<size, burst_type.name());
        
        if (trans_type == WRITE_TRANS) begin
            s = {s, $sformatf(", Data[0]=0x%0h", data[0])};
        end
        
        if (exclusive_access) begin
            s = {s, ", EXCLUSIVE"};
        end
        
        if (crosses_4kb_boundary()) begin
            s = {s, ", [4KB_VIOLATION]"};
        end
        
        return s;
    endfunction
    
endclass : axi4_transaction