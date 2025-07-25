//==============================================================================
// AXI4 Advanced Test Sequences
// 
// Description: Advanced transaction sequences for AXI4 verification
// Includes out-of-order, exclusive access, QoS, and region tests
//==============================================================================

`include "../../rtl/common/axi4_defines.sv"

// Out-of-order transaction sequence
class axi4_out_of_order_sequence;
    
    axi4_config_t cfg;
    int num_ids;
    int trans_per_id;
    
    function new(axi4_config_t config);
        this.cfg = config;
        this.num_ids = (1 << config.ID_WIDTH) / 2;  // Use half available IDs
        this.trans_per_id = 4;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        int total_trans = num_ids * trans_per_id;
        int trans_idx = 0;
        
        trans_array = new[total_trans];
        
        // Generate transactions with different IDs
        for (int id = 0; id < num_ids; id++) begin
            for (int i = 0; i < trans_per_id; i++) begin
                axi4_transaction_t trans;
                
                trans.id = id;
                trans.addr = 32'h1000_0000 + (id * 32'h1000) + (i * 32'h100);
                trans.len = $urandom_range(3, 0);
                trans.size = $clog2(cfg.DATA_WIDTH/8);
                trans.burst = AXI4_BURST_INCR;
                trans.is_write = ($urandom_range(1, 0) == 1);
                trans.lock = AXI4_LOCK_NORMAL;
                trans.prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
                trans.cache = '{allocate: 1'b0, other_alloc: 1'b0, modifiable: 1'b1, bufferable: 1'b0};
                trans.qos = id % 16;  // Different QoS for each ID
                trans.region = 0;
                
                // Allocate data arrays
                trans.data = new[trans.len + 1];
                trans.strb = new[trans.len + 1];
                trans.resp = new[trans.len + 1];
                
                if (trans.is_write) begin
                    for (int j = 0; j <= trans.len; j++) begin
                        trans.data[j] = {id[15:0], i[7:0], j[7:0]};
                        trans.strb[j] = '1;
                    end
                end
                
                trans_array[trans_idx++] = trans;
            end
        end
        
        // Shuffle array to create out-of-order pattern
        for (int i = total_trans - 1; i > 0; i--) begin
            int j = $urandom_range(i, 0);
            axi4_transaction_t temp = trans_array[i];
            trans_array[i] = trans_array[j];
            trans_array[j] = temp;
        end
        
        return trans_array;
    endfunction
    
endclass : axi4_out_of_order_sequence

// Same ID ordering test sequence
class axi4_same_id_ordering_sequence;
    
    axi4_config_t cfg;
    int test_id;
    int num_transactions;
    
    function new(axi4_config_t config);
        this.cfg = config;
        this.test_id = 1;
        this.num_transactions = 10;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        
        trans_array = new[num_transactions];
        
        // All transactions use same ID
        for (int i = 0; i < num_transactions; i++) begin
            axi4_transaction_t trans;
            
            trans.id = test_id;
            trans.addr = 32'h2000_0000 + (i * 32'h40);
            trans.len = 0;  // Single beat
            trans.size = 3;  // 8 bytes
            trans.burst = AXI4_BURST_INCR;
            trans.is_write = (i < num_transactions/2);  // First half writes, second half reads
            trans.lock = AXI4_LOCK_NORMAL;
            trans.prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
            trans.cache = '{allocate: 1'b0, other_alloc: 1'b0, modifiable: 1'b0, bufferable: 1'b0};
            trans.qos = 0;
            trans.region = 0;
            
            trans.data = new[1];
            trans.strb = new[1];
            trans.resp = new[1];
            
            if (trans.is_write) begin
                trans.data[0] = i;
                trans.strb[0] = '1;
            end
            
            trans_array[i] = trans;
        end
        
        return trans_array;
    endfunction
    
endclass : axi4_same_id_ordering_sequence

// Exclusive access sequence
class axi4_exclusive_access_sequence;
    
    axi4_config_t cfg;
    logic [63:0] exclusive_addr;
    int exclusive_id;
    
    function new(axi4_config_t config);
        this.cfg = config;
        this.exclusive_addr = 32'h3000_0000;
        this.exclusive_id = 5;
    endfunction
    
    // Generate exclusive read-write pair
    virtual function axi4_transaction_t[] generate_exclusive_pair();
        axi4_transaction_t trans_array[];
        
        trans_array = new[2];
        
        // Exclusive read
        trans_array[0].id = exclusive_id;
        trans_array[0].addr = exclusive_addr;
        trans_array[0].len = 0;  // Single beat
        trans_array[0].size = 3;  // 8 bytes
        trans_array[0].burst = AXI4_BURST_INCR;
        trans_array[0].is_write = 1'b0;
        trans_array[0].lock = AXI4_LOCK_EXCLUSIVE;
        trans_array[0].prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
        trans_array[0].cache = '{allocate: 1'b0, other_alloc: 1'b0, modifiable: 1'b0, bufferable: 1'b0};
        trans_array[0].qos = 0;
        trans_array[0].region = 0;
        trans_array[0].data = new[1];
        trans_array[0].strb = new[1];
        trans_array[0].resp = new[1];
        
        // Exclusive write
        trans_array[1].id = exclusive_id;
        trans_array[1].addr = exclusive_addr;
        trans_array[1].len = 0;  // Single beat
        trans_array[1].size = 3;  // 8 bytes
        trans_array[1].burst = AXI4_BURST_INCR;
        trans_array[1].is_write = 1'b1;
        trans_array[1].lock = AXI4_LOCK_EXCLUSIVE;
        trans_array[1].prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
        trans_array[1].cache = '{allocate: 1'b0, other_alloc: 1'b0, modifiable: 1'b0, bufferable: 1'b0};
        trans_array[1].qos = 0;
        trans_array[1].region = 0;
        trans_array[1].data = new[1];
        trans_array[1].strb = new[1];
        trans_array[1].resp = new[1];
        trans_array[1].data[0] = 64'hDEAD_BEEF_CAFE_BABE;
        trans_array[1].strb[0] = '1;
        
        return trans_array;
    endfunction
    
    // Generate exclusive failure scenario
    virtual function axi4_transaction_t[] generate_exclusive_failure();
        axi4_transaction_t trans_array[];
        
        trans_array = new[4];
        
        // Master A: Exclusive read
        trans_array[0] = create_exclusive_trans(0, exclusive_addr, 1'b0);
        
        // Master B: Exclusive read (same address)
        trans_array[1] = create_exclusive_trans(1, exclusive_addr, 1'b0);
        
        // Master B: Normal write (clears exclusive)
        trans_array[2] = create_normal_trans(1, exclusive_addr, 1'b1);
        
        // Master A: Exclusive write (should fail)
        trans_array[3] = create_exclusive_trans(0, exclusive_addr, 1'b1);
        
        return trans_array;
    endfunction
    
    function axi4_transaction_t create_exclusive_trans(int id, logic [63:0] addr, bit is_write);
        axi4_transaction_t trans;
        
        trans.id = id;
        trans.addr = addr;
        trans.len = 0;
        trans.size = 3;
        trans.burst = AXI4_BURST_INCR;
        trans.is_write = is_write;
        trans.lock = AXI4_LOCK_EXCLUSIVE;
        trans.prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
        trans.cache = '{allocate: 1'b0, other_alloc: 1'b0, modifiable: 1'b0, bufferable: 1'b0};
        trans.qos = 0;
        trans.region = 0;
        trans.data = new[1];
        trans.strb = new[1];
        trans.resp = new[1];
        
        if (is_write) begin
            trans.data[0] = {32'h0, id[15:0], 16'hEEEE};
            trans.strb[0] = '1;
        end
        
        return trans;
    endfunction
    
    function axi4_transaction_t create_normal_trans(int id, logic [63:0] addr, bit is_write);
        axi4_transaction_t trans;
        
        trans = create_exclusive_trans(id, addr, is_write);
        trans.lock = AXI4_LOCK_NORMAL;
        
        return trans;
    endfunction
    
endclass : axi4_exclusive_access_sequence

// QoS variation sequence
class axi4_qos_test_sequence;
    
    axi4_config_t cfg;
    
    function new(axi4_config_t config);
        this.cfg = config;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        int num_qos_levels = 16;
        
        trans_array = new[num_qos_levels];
        
        // Generate transaction for each QoS level
        for (int qos = 0; qos < num_qos_levels; qos++) begin
            axi4_transaction_t trans;
            
            trans.id = qos % (1 << cfg.ID_WIDTH);
            trans.addr = 32'h4000_0000 + (qos * 32'h100);
            trans.len = $urandom_range(15, 0);
            trans.size = $urandom_range($clog2(cfg.DATA_WIDTH/8), 0);
            trans.burst = AXI4_BURST_INCR;
            trans.is_write = ($urandom_range(1, 0) == 1);
            trans.lock = AXI4_LOCK_NORMAL;
            trans.prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
            trans.cache = '{allocate: 1'b0, other_alloc: 1'b0, modifiable: 1'b1, bufferable: 1'b0};
            trans.qos = qos;
            trans.region = 0;
            
            trans.data = new[trans.len + 1];
            trans.strb = new[trans.len + 1];
            trans.resp = new[trans.len + 1];
            
            if (trans.is_write) begin
                for (int i = 0; i <= trans.len; i++) begin
                    trans.data[i] = {qos[3:0], i[27:0]};
                    trans.strb[i] = '1;
                end
            end
            
            trans_array[qos] = trans;
        end
        
        return trans_array;
    endfunction
    
endclass : axi4_qos_test_sequence

// REGION test sequence
class axi4_region_test_sequence;
    
    axi4_config_t cfg;
    
    function new(axi4_config_t config);
        this.cfg = config;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        int num_regions = cfg.SUPPORT_REGION ? 16 : 1;
        
        trans_array = new[num_regions * 2];  // Read and write for each region
        
        for (int region = 0; region < num_regions; region++) begin
            // Write transaction
            trans_array[region*2] = create_region_trans(region, 1'b1);
            
            // Read transaction
            trans_array[region*2 + 1] = create_region_trans(region, 1'b0);
        end
        
        return trans_array;
    endfunction
    
    function axi4_transaction_t create_region_trans(int region, bit is_write);
        axi4_transaction_t trans;
        
        trans.id = region % (1 << cfg.ID_WIDTH);
        trans.addr = 32'h5000_0000 + (region * 32'h10_0000);  // Each region 1MB apart
        trans.len = 3;  // 4-beat burst
        trans.size = 3;  // 8 bytes
        trans.burst = AXI4_BURST_INCR;
        trans.is_write = is_write;
        trans.lock = AXI4_LOCK_NORMAL;
        trans.prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
        trans.cache = '{allocate: 1'b0, other_alloc: 1'b0, modifiable: 1'b0, bufferable: 1'b0};
        trans.qos = 0;
        trans.region = region;
        
        trans.data = new[trans.len + 1];
        trans.strb = new[trans.len + 1];
        trans.resp = new[trans.len + 1];
        
        if (is_write) begin
            for (int i = 0; i <= trans.len; i++) begin
                trans.data[i] = {region[3:0], 28'h0, i[31:0]};
                trans.strb[i] = '1;
            end
        end
        
        return trans;
    endfunction
    
endclass : axi4_region_test_sequence

// Protection attribute test sequence
class axi4_prot_test_sequence;
    
    axi4_config_t cfg;
    
    function new(axi4_config_t config);
        this.cfg = config;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        int trans_idx = 0;
        
        // Test all 8 combinations of PROT
        trans_array = new[8 * 2];  // Read and write for each PROT value
        
        for (int prot_val = 0; prot_val < 8; prot_val++) begin
            axi4_prot_t prot;
            prot.privileged = prot_val[0];
            prot.nonsecure = prot_val[1];
            prot.instruction = prot_val[2];
            
            // Write with this PROT
            trans_array[trans_idx++] = create_prot_trans(prot, 1'b1);
            
            // Read with this PROT
            trans_array[trans_idx++] = create_prot_trans(prot, 1'b0);
        end
        
        return trans_array;
    endfunction
    
    function axi4_transaction_t create_prot_trans(axi4_prot_t prot, bit is_write);
        axi4_transaction_t trans;
        
        trans.id = {prot.instruction, prot.nonsecure, prot.privileged};
        trans.addr = 32'h6000_0000 + ({prot.instruction, prot.nonsecure, prot.privileged} * 32'h1000);
        trans.len = 0;
        trans.size = 2;  // 4 bytes
        trans.burst = AXI4_BURST_INCR;
        trans.is_write = is_write;
        trans.lock = AXI4_LOCK_NORMAL;
        trans.prot = prot;
        trans.cache = '{allocate: 1'b0, other_alloc: 1'b0, modifiable: 1'b0, bufferable: 1'b0};
        trans.qos = 0;
        trans.region = 0;
        
        trans.data = new[1];
        trans.strb = new[1];
        trans.resp = new[1];
        
        if (is_write) begin
            trans.data[0] = {prot.instruction, prot.nonsecure, prot.privileged, 29'h0};
            trans.strb[0] = '1;
        end
        
        return trans;
    endfunction
    
endclass : axi4_prot_test_sequence

// Cache attribute test sequence
class axi4_cache_test_sequence;
    
    axi4_config_t cfg;
    
    function new(axi4_config_t config);
        this.cfg = config;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        int trans_idx = 0;
        
        // Test key cache attribute combinations
        trans_array = new[8];
        
        // Non-modifiable, non-bufferable
        trans_array[trans_idx++] = create_cache_trans(4'b0000, 1'b1);
        
        // Non-modifiable, bufferable
        trans_array[trans_idx++] = create_cache_trans(4'b0001, 1'b1);
        
        // Modifiable, non-bufferable
        trans_array[trans_idx++] = create_cache_trans(4'b0010, 1'b1);
        
        // Modifiable, bufferable
        trans_array[trans_idx++] = create_cache_trans(4'b0011, 1'b1);
        
        // Write-through cacheable
        trans_array[trans_idx++] = create_cache_trans(4'b0110, 1'b1);
        
        // Write-back cacheable
        trans_array[trans_idx++] = create_cache_trans(4'b0111, 1'b1);
        
        // Write allocate
        trans_array[trans_idx++] = create_cache_trans(4'b1110, 1'b1);
        
        // Read allocate
        trans_array[trans_idx++] = create_cache_trans(4'b1010, 1'b0);
        
        return trans_array;
    endfunction
    
    function axi4_transaction_t create_cache_trans(logic [3:0] cache_val, bit is_write);
        axi4_transaction_t trans;
        
        trans.id = cache_val;
        trans.addr = 32'h7000_0000 + (cache_val * 32'h1000);
        trans.len = 7;  // 8-beat burst
        trans.size = 3;  // 8 bytes
        trans.burst = AXI4_BURST_INCR;
        trans.is_write = is_write;
        trans.lock = AXI4_LOCK_NORMAL;
        trans.prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
        trans.cache = '{allocate: cache_val[3], 
                       other_alloc: cache_val[2],
                       modifiable: cache_val[1], 
                       bufferable: cache_val[0]};
        trans.qos = 0;
        trans.region = 0;
        
        trans.data = new[trans.len + 1];
        trans.strb = new[trans.len + 1];
        trans.resp = new[trans.len + 1];
        
        if (is_write) begin
            for (int i = 0; i <= trans.len; i++) begin
                trans.data[i] = {cache_val, 28'h0, i[31:0]};
                trans.strb[i] = '1;
            end
        end
        
        return trans;
    endfunction
    
endclass : axi4_cache_test_sequence