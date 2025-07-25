//==============================================================================
// AXI4 Stress Test Sequences
// 
// Description: Stress test sequences for AXI4 verification
// Includes high throughput, random, multi-master contention tests
//==============================================================================

`include "../../rtl/common/axi4_defines.sv"

// High throughput stress sequence
class axi4_high_throughput_sequence;
    
    axi4_config_t cfg;
    int num_masters;
    int trans_per_master;
    int max_outstanding;
    
    function new(axi4_config_t config, int masters = 4);
        this.cfg = config;
        this.num_masters = masters;
        this.trans_per_master = 100;
        this.max_outstanding = 16;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        int total_trans = num_masters * trans_per_master;
        int idx = 0;
        
        trans_array = new[total_trans];
        
        for (int m = 0; m < num_masters; m++) begin
            for (int t = 0; t < trans_per_master; t++) begin
                axi4_transaction_t trans;
                
                trans.id = (m * max_outstanding) + (t % max_outstanding);
                trans.addr = 32'h1000_0000 + (m * 32'h100_0000) + (t * 32'h1000);
                trans.len = 255;  // Maximum burst length
                trans.size = $clog2(cfg.DATA_WIDTH/8);  // Maximum size
                trans.burst = AXI4_BURST_INCR;
                trans.is_write = (t % 2 == 0);
                trans.lock = AXI4_LOCK_NORMAL;
                trans.prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
                trans.cache = '{allocate: 1'b1, other_alloc: 1'b1, modifiable: 1'b1, bufferable: 1'b1};
                trans.qos = 15;  // Highest priority
                trans.region = m % 16;
                
                trans.data = new[trans.len + 1];
                trans.strb = new[trans.len + 1];
                trans.resp = new[trans.len + 1];
                
                if (trans.is_write) begin
                    for (int i = 0; i <= trans.len; i++) begin
                        trans.data[i] = {m[7:0], t[7:0], i[15:0]};
                        trans.strb[i] = '1;
                    end
                end
                
                trans_array[idx++] = trans;
            end
        end
        
        return trans_array;
    endfunction
    
endclass : axi4_high_throughput_sequence

// Fully randomized stress sequence
class axi4_random_stress_sequence;
    
    axi4_config_t cfg;
    int num_transactions;
    
    function new(axi4_config_t config);
        this.cfg = config;
        this.num_transactions = 1000;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        
        trans_array = new[num_transactions];
        
        for (int i = 0; i < num_transactions; i++) begin
            trans_array[i] = generate_random_trans();
        end
        
        return trans_array;
    endfunction
    
    function axi4_transaction_t generate_random_trans();
        axi4_transaction_t trans;
        
        trans.id = $urandom_range((1 << cfg.ID_WIDTH) - 1, 0);
        trans.addr = $urandom;
        trans.burst = axi4_burst_t'($urandom_range(2, 0));
        
        // Constrain length based on burst type
        case (trans.burst)
            AXI4_BURST_FIXED: trans.len = $urandom_range(15, 0);
            AXI4_BURST_INCR: trans.len = $urandom_range(255, 0);
            AXI4_BURST_WRAP: trans.len = (1 << $urandom_range(4, 1)) - 1;  // 1, 3, 7, 15
        endcase
        
        trans.size = $urandom_range($clog2(cfg.DATA_WIDTH/8), 0);
        trans.is_write = ($urandom_range(1, 0) == 1);
        trans.lock = ($urandom_range(100, 0) < 5) ? AXI4_LOCK_EXCLUSIVE : AXI4_LOCK_NORMAL;
        
        trans.prot.privileged = $urandom_range(1, 0);
        trans.prot.nonsecure = $urandom_range(1, 0);
        trans.prot.instruction = $urandom_range(1, 0);
        
        trans.cache.allocate = $urandom_range(1, 0);
        trans.cache.other_alloc = $urandom_range(1, 0);
        trans.cache.modifiable = $urandom_range(1, 0);
        trans.cache.bufferable = $urandom_range(1, 0);
        
        trans.qos = $urandom_range(15, 0);
        trans.region = $urandom_range(15, 0);
        
        // Ensure no 4KB crossing
        logic [63:0] end_addr = trans.addr + ((trans.len + 1) << trans.size) - 1;
        if (trans.addr[31:12] != end_addr[31:12]) begin
            // Adjust length to prevent 4KB crossing
            int max_bytes = 32'h1000 - (trans.addr & 32'hFFF);
            int max_beats = max_bytes >> trans.size;
            if (max_beats > 0) begin
                trans.len = max_beats - 1;
                if (trans.len > 255) trans.len = 255;
            end else begin
                trans.len = 0;
            end
        end
        
        // Align WRAP bursts
        if (trans.burst == AXI4_BURST_WRAP) begin
            int total_bytes = (trans.len + 1) << trans.size;
            trans.addr = (trans.addr / total_bytes) * total_bytes;
        end
        
        trans.data = new[trans.len + 1];
        trans.strb = new[trans.len + 1];
        trans.resp = new[trans.len + 1];
        
        if (trans.is_write) begin
            for (int i = 0; i <= trans.len; i++) begin
                trans.data[i] = $random;
                trans.strb[i] = $urandom_range(100, 0) < 90 ? '1 : $random;
            end
        end
        
        return trans;
    endfunction
    
endclass : axi4_random_stress_sequence

// Multi-master contention sequence
class axi4_contention_sequence;
    
    axi4_config_t cfg;
    int num_masters;
    logic [31:0] contention_addr;
    
    function new(axi4_config_t config, int masters = 4);
        this.cfg = config;
        this.num_masters = masters;
        this.contention_addr = 32'h5000_0000;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        int trans_per_master = 20;
        int idx = 0;
        
        trans_array = new[num_masters * trans_per_master];
        
        // All masters access same address range to create contention
        for (int m = 0; m < num_masters; m++) begin
            for (int t = 0; t < trans_per_master; t++) begin
                axi4_transaction_t trans;
                
                trans.id = m;  // Each master uses its own ID
                trans.addr = contention_addr + ((t % 4) * 64);  // 4 cachelines
                trans.len = 7;  // 8-beat burst
                trans.size = 3;  // 8 bytes
                trans.burst = AXI4_BURST_INCR;
                trans.is_write = (t % 2 == 0);
                trans.lock = AXI4_LOCK_NORMAL;
                trans.prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
                trans.cache = '{allocate: 1'b1, other_alloc: 1'b1, modifiable: 1'b1, bufferable: 1'b0};
                trans.qos = m;  // Different QoS per master
                trans.region = 0;
                
                trans.data = new[trans.len + 1];
                trans.strb = new[trans.len + 1];
                trans.resp = new[trans.len + 1];
                
                if (trans.is_write) begin
                    for (int i = 0; i <= trans.len; i++) begin
                        trans.data[i] = {m[7:0], t[7:0], i[7:0], 8'h00};
                        trans.strb[i] = '1;
                    end
                end
                
                trans_array[idx++] = trans;
            end
        end
        
        // Shuffle to interleave masters
        for (int i = trans_array.size() - 1; i > 0; i--) begin
            int j = $urandom_range(i, 0);
            axi4_transaction_t temp = trans_array[i];
            trans_array[i] = trans_array[j];
            trans_array[j] = temp;
        end
        
        return trans_array;
    endfunction
    
endclass : axi4_contention_sequence

// Corner case stress sequence
class axi4_corner_case_sequence;
    
    axi4_config_t cfg;
    
    function new(axi4_config_t config);
        this.cfg = config;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        int idx = 0;
        
        trans_array = new[50];
        
        // Single byte transfers
        trans_array[idx++] = create_corner_trans(0, 0, AXI4_BURST_FIXED);
        
        // Maximum size single transfer
        trans_array[idx++] = create_corner_trans(0, $clog2(cfg.DATA_WIDTH/8), AXI4_BURST_INCR);
        
        // Minimum WRAP burst (2 beats)
        trans_array[idx++] = create_corner_trans(1, 2, AXI4_BURST_WRAP);
        
        // Maximum WRAP burst (16 beats)
        trans_array[idx++] = create_corner_trans(15, 3, AXI4_BURST_WRAP);
        
        // Near 4KB boundary - single beat
        trans_array[idx++] = create_near_4kb_trans(0);
        
        // Near 4KB boundary - maximum burst without crossing
        trans_array[idx++] = create_near_4kb_trans(15);
        
        // All possible sizes
        for (int size = 0; size <= $clog2(cfg.DATA_WIDTH/8); size++) begin
            trans_array[idx++] = create_corner_trans(0, size, AXI4_BURST_INCR);
        end
        
        // Exclusive access corner cases
        trans_array[idx++] = create_exclusive_corner(1, 0);   // 1 byte
        trans_array[idx++] = create_exclusive_corner(2, 1);   // 2 bytes
        trans_array[idx++] = create_exclusive_corner(4, 2);   // 4 bytes
        trans_array[idx++] = create_exclusive_corner(8, 3);   // 8 bytes
        trans_array[idx++] = create_exclusive_corner(16, 4);  // 16 bytes
        trans_array[idx++] = create_exclusive_corner(32, 5);  // 32 bytes
        trans_array[idx++] = create_exclusive_corner(64, 6);  // 64 bytes
        trans_array[idx++] = create_exclusive_corner(128, 7); // 128 bytes (max)
        
        // Zero strobe (write with no bytes enabled)
        trans_array[idx++] = create_zero_strobe_trans();
        
        // Sparse strobe patterns
        trans_array[idx++] = create_sparse_strobe_trans();
        
        // Rapid ID switching
        for (int i = 0; i < 10; i++) begin
            trans_array[idx++] = create_id_switch_trans(i % (1 << cfg.ID_WIDTH));
        end
        
        // Resize array to actual size
        trans_array = trans_array[0:idx-1];
        
        return trans_array;
    endfunction
    
    function axi4_transaction_t create_corner_trans(int len, int size, axi4_burst_t burst);
        axi4_transaction_t trans;
        
        trans.id = $urandom_range((1 << cfg.ID_WIDTH) - 1, 0);
        trans.addr = 32'h6000_0000 + $urandom_range(32'hFFFF, 0);
        trans.len = len;
        trans.size = size;
        trans.burst = burst;
        trans.is_write = ($urandom_range(1, 0) == 1);
        trans.lock = AXI4_LOCK_NORMAL;
        trans.prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
        trans.cache = '{allocate: 1'b0, other_alloc: 1'b0, modifiable: 1'b0, bufferable: 1'b0};
        trans.qos = $urandom_range(15, 0);
        trans.region = $urandom_range(15, 0);
        
        // Align for WRAP
        if (burst == AXI4_BURST_WRAP) begin
            int total_bytes = (len + 1) << size;
            trans.addr = (trans.addr / total_bytes) * total_bytes;
        end
        
        trans.data = new[trans.len + 1];
        trans.strb = new[trans.len + 1];
        trans.resp = new[trans.len + 1];
        
        if (trans.is_write) begin
            for (int i = 0; i <= trans.len; i++) begin
                trans.data[i] = i;
                trans.strb[i] = '1;
            end
        end
        
        return trans;
    endfunction
    
    function axi4_transaction_t create_near_4kb_trans(int len);
        axi4_transaction_t trans;
        
        trans = create_corner_trans(len, 3, AXI4_BURST_INCR);
        
        // Place near 4KB boundary
        int bytes_from_boundary = ((len + 1) * 8) + 8;  // Leave some margin
        trans.addr = 32'h7000_1000 - bytes_from_boundary;
        
        return trans;
    endfunction
    
    function axi4_transaction_t create_exclusive_corner(int total_bytes, int size);
        axi4_transaction_t trans;
        int len = (total_bytes >> size) - 1;
        
        trans = create_corner_trans(len, size, AXI4_BURST_INCR);
        trans.lock = AXI4_LOCK_EXCLUSIVE;
        trans.addr = (trans.addr / total_bytes) * total_bytes;  // Align
        
        return trans;
    endfunction
    
    function axi4_transaction_t create_zero_strobe_trans();
        axi4_transaction_t trans;
        
        trans = create_corner_trans(3, 3, AXI4_BURST_INCR);
        trans.is_write = 1'b1;
        
        // All strobes disabled
        for (int i = 0; i <= trans.len; i++) begin
            trans.strb[i] = '0;
        end
        
        return trans;
    endfunction
    
    function axi4_transaction_t create_sparse_strobe_trans();
        axi4_transaction_t trans;
        
        trans = create_corner_trans(7, 3, AXI4_BURST_INCR);
        trans.is_write = 1'b1;
        
        // Different strobe pattern each beat
        for (int i = 0; i <= trans.len; i++) begin
            trans.strb[i] = 1 << i;  // Only one byte enabled, rotating
        end
        
        return trans;
    endfunction
    
    function axi4_transaction_t create_id_switch_trans(int id);
        axi4_transaction_t trans;
        
        trans = create_corner_trans(0, 2, AXI4_BURST_INCR);
        trans.id = id;
        trans.addr = 32'h8000_0000 + (id * 32'h100);
        
        return trans;
    endfunction
    
endclass : axi4_corner_case_sequence

// Memory coherency stress sequence
class axi4_coherency_stress_sequence;
    
    axi4_config_t cfg;
    int num_masters;
    logic [31:0] shared_addr;
    
    function new(axi4_config_t config, int masters = 4);
        this.cfg = config;
        this.num_masters = masters;
        this.shared_addr = 32'h9000_0000;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        int idx = 0;
        
        trans_array = new[num_masters * 10];
        
        // Pattern: Read-Modify-Write from multiple masters
        for (int iteration = 0; iteration < 5; iteration++) begin
            for (int m = 0; m < num_masters; m++) begin
                // Read
                trans_array[idx++] = create_coherent_trans(m, shared_addr, 1'b0, 1'b0);
                
                // Write (modify)
                trans_array[idx++] = create_coherent_trans(m, shared_addr, 1'b1, 1'b0);
            end
        end
        
        return trans_array;
    endfunction
    
    function axi4_transaction_t create_coherent_trans(int master_id, logic [31:0] addr, bit is_write, bit exclusive);
        axi4_transaction_t trans;
        
        trans.id = master_id;
        trans.addr = addr;
        trans.len = 0;  // Single beat
        trans.size = 3;  // 8 bytes
        trans.burst = AXI4_BURST_INCR;
        trans.is_write = is_write;
        trans.lock = exclusive ? AXI4_LOCK_EXCLUSIVE : AXI4_LOCK_NORMAL;
        trans.prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
        trans.cache = '{allocate: 1'b1, other_alloc: 1'b1, modifiable: 1'b1, bufferable: 1'b0};
        trans.qos = 15;  // High priority for coherency
        trans.region = 0;
        
        trans.data = new[1];
        trans.strb = new[1];
        trans.resp = new[1];
        
        if (is_write) begin
            trans.data[0] = {master_id[31:0], $time[31:0]};
            trans.strb[0] = '1;
        end
        
        return trans;
    endfunction
    
endclass : axi4_coherency_stress_sequence