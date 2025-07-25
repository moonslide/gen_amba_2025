//==============================================================================
// AXI4 Error Injection Sequences
// 
// Description: Error injection sequences for AXI4 verification
// Includes protocol violations, error responses, and illegal transactions
//==============================================================================

`include "../../rtl/common/axi4_defines.sv"

// Base error sequence class
class axi4_error_base_sequence;
    
    axi4_config_t cfg;
    string error_description;
    
    function new(axi4_config_t config);
        this.cfg = config;
    endfunction
    
    virtual function axi4_transaction_t create_base_trans();
        axi4_transaction_t trans;
        
        trans.id = $urandom_range((1 << cfg.ID_WIDTH) - 1, 0);
        trans.addr = 32'h8000_0000;
        trans.len = 0;
        trans.size = 3;
        trans.burst = AXI4_BURST_INCR;
        trans.lock = AXI4_LOCK_NORMAL;
        trans.prot = '{privileged: 1'b1, nonsecure: 1'b0, instruction: 1'b0};
        trans.cache = '{allocate: 1'b0, other_alloc: 1'b0, modifiable: 1'b0, bufferable: 1'b0};
        trans.qos = 0;
        trans.region = 0;
        trans.is_write = 1'b1;
        
        trans.data = new[trans.len + 1];
        trans.strb = new[trans.len + 1];
        trans.resp = new[trans.len + 1];
        
        trans.data[0] = 64'hDEAD_BEEF_BAD_F00D;
        trans.strb[0] = '1;
        
        return trans;
    endfunction
    
endclass : axi4_error_base_sequence

// 4KB boundary crossing sequence
class axi4_4kb_cross_sequence extends axi4_error_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
        error_description = "4KB boundary crossing error";
    endfunction
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        trans = create_base_trans();
        
        // Set address near 4KB boundary
        trans.addr = 32'h8000_0FF0;  // 16 bytes before 4KB boundary
        trans.len = 15;  // 16 beats
        trans.size = 3;   // 8 bytes per beat = 128 bytes total
        trans.burst = AXI4_BURST_INCR;
        
        // This will cross from 0x8000_0FF0 to 0x8000_1070 (crosses 4KB at 0x8000_1000)
        
        trans.data = new[trans.len + 1];
        trans.strb = new[trans.len + 1];
        
        for (int i = 0; i <= trans.len; i++) begin
            trans.data[i] = i;
            trans.strb[i] = '1;
        end
        
        return trans;
    endfunction
    
endclass : axi4_4kb_cross_sequence

// Invalid WRAP burst length sequence
class axi4_invalid_wrap_len_sequence extends axi4_error_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
        error_description = "Invalid WRAP burst length";
    endfunction
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        int invalid_lengths[] = '{2, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14};
        
        trans = create_base_trans();
        
        trans.burst = AXI4_BURST_WRAP;
        trans.len = invalid_lengths[$urandom_range(invalid_lengths.size()-1, 0)];
        trans.addr = 32'h9000_0000;
        trans.size = 3;
        
        trans.data = new[trans.len + 1];
        trans.strb = new[trans.len + 1];
        
        for (int i = 0; i <= trans.len; i++) begin
            trans.data[i] = i;
            trans.strb[i] = '1;
        end
        
        return trans;
    endfunction
    
endclass : axi4_invalid_wrap_len_sequence

// Unaligned exclusive access sequence
class axi4_unaligned_exclusive_sequence extends axi4_error_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
        error_description = "Unaligned exclusive access";
    endfunction
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        trans = create_base_trans();
        
        trans.lock = AXI4_LOCK_EXCLUSIVE;
        trans.addr = 32'hA000_0003;  // Unaligned address
        trans.len = 0;
        trans.size = 3;  // 8 bytes - requires 8-byte alignment
        trans.is_write = 1'b0;  // Exclusive read
        
        return trans;
    endfunction
    
endclass : axi4_unaligned_exclusive_sequence

// Exclusive access size violation sequence
class axi4_exclusive_size_violation_sequence extends axi4_error_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
        error_description = "Exclusive access exceeds 128 bytes";
    endfunction
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        trans = create_base_trans();
        
        trans.lock = AXI4_LOCK_EXCLUSIVE;
        trans.addr = 32'hB000_0000;
        trans.len = 31;   // 32 beats
        trans.size = 3;    // 8 bytes per beat = 256 bytes total (exceeds 128)
        trans.is_write = 1'b0;
        
        return trans;
    endfunction
    
endclass : axi4_exclusive_size_violation_sequence

// Unmapped address sequence (triggers DECERR)
class axi4_unmapped_addr_sequence extends axi4_error_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
        error_description = "Access to unmapped address";
    endfunction
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        trans = create_base_trans();
        
        // Use very high address likely to be unmapped
        trans.addr = 32'hFFFF_F000;
        trans.len = 3;
        trans.size = 2;
        trans.is_write = ($urandom_range(1, 0) == 1);
        
        trans.data = new[trans.len + 1];
        trans.strb = new[trans.len + 1];
        
        if (trans.is_write) begin
            for (int i = 0; i <= trans.len; i++) begin
                trans.data[i] = 32'hDEC_ERR00 + i;
                trans.strb[i] = '1;
            end
        end
        
        return trans;
    endfunction
    
endclass : axi4_unmapped_addr_sequence

// Protected region access violation sequence
class axi4_prot_violation_sequence extends axi4_error_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
        error_description = "Protection violation";
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        
        trans_array = new[4];
        
        // Unprivileged access to privileged region
        trans_array[0] = create_base_trans();
        trans_array[0].addr = 32'hC000_0000;  // Assume privileged region
        trans_array[0].prot.privileged = 1'b0;  // Unprivileged
        trans_array[0].prot.nonsecure = 1'b0;
        trans_array[0].prot.instruction = 1'b0;
        
        // Non-secure access to secure region
        trans_array[1] = create_base_trans();
        trans_array[1].addr = 32'hC100_0000;  // Assume secure region
        trans_array[1].prot.privileged = 1'b1;
        trans_array[1].prot.nonsecure = 1'b1;   // Non-secure
        trans_array[1].prot.instruction = 1'b0;
        
        // Instruction fetch from data-only region
        trans_array[2] = create_base_trans();
        trans_array[2].addr = 32'hC200_0000;  // Assume data-only region
        trans_array[2].prot.privileged = 1'b1;
        trans_array[2].prot.nonsecure = 1'b0;
        trans_array[2].prot.instruction = 1'b1;  // Instruction fetch
        trans_array[2].is_write = 1'b0;  // Read
        
        // Write to read-only region
        trans_array[3] = create_base_trans();
        trans_array[3].addr = 32'hC300_0000;  // Assume read-only region
        trans_array[3].prot.privileged = 1'b1;
        trans_array[3].prot.nonsecure = 1'b0;
        trans_array[3].prot.instruction = 1'b0;
        trans_array[3].is_write = 1'b1;  // Write to RO region
        
        return trans_array;
    endfunction
    
endclass : axi4_prot_violation_sequence

// Invalid burst type sequence
class axi4_invalid_burst_type_sequence extends axi4_error_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
        error_description = "Invalid burst type (reserved value)";
    endfunction
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        trans = create_base_trans();
        
        trans.burst = AXI4_BURST_RSVD;  // Reserved burst type (2'b11)
        trans.addr = 32'hD000_0000;
        trans.len = 3;
        trans.size = 2;
        
        trans.data = new[trans.len + 1];
        trans.strb = new[trans.len + 1];
        
        for (int i = 0; i <= trans.len; i++) begin
            trans.data[i] = i;
            trans.strb[i] = '1;
        end
        
        return trans;
    endfunction
    
endclass : axi4_invalid_burst_type_sequence

// Narrow transfer with incorrect strobes
class axi4_invalid_strobe_sequence extends axi4_error_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
        error_description = "Invalid write strobes for narrow transfer";
    endfunction
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        trans = create_base_trans();
        
        trans.addr = 32'hE000_0000;
        trans.len = 3;
        trans.size = 1;  // 2-byte transfer
        trans.is_write = 1'b1;
        
        trans.data = new[trans.len + 1];
        trans.strb = new[trans.len + 1];
        
        for (int i = 0; i <= trans.len; i++) begin
            trans.data[i] = i;
            // Invalid strobe - enables bytes outside transfer size
            trans.strb[i] = 8'hFF;  // All bytes enabled for 2-byte transfer
        end
        
        return trans;
    endfunction
    
endclass : axi4_invalid_strobe_sequence

// Multiple outstanding exclusive sequence
class axi4_multiple_exclusive_sequence extends axi4_error_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
        error_description = "Multiple outstanding exclusive accesses";
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        
        trans_array = new[4];
        
        // First exclusive read
        trans_array[0] = create_base_trans();
        trans_array[0].id = 0;
        trans_array[0].addr = 32'hF000_0000;
        trans_array[0].lock = AXI4_LOCK_EXCLUSIVE;
        trans_array[0].is_write = 1'b0;
        
        // Second exclusive read (same ID, different address)
        trans_array[1] = create_base_trans();
        trans_array[1].id = 0;
        trans_array[1].addr = 32'hF000_1000;
        trans_array[1].lock = AXI4_LOCK_EXCLUSIVE;
        trans_array[1].is_write = 1'b0;
        
        // Exclusive write to first address (may fail)
        trans_array[2] = create_base_trans();
        trans_array[2].id = 0;
        trans_array[2].addr = 32'hF000_0000;
        trans_array[2].lock = AXI4_LOCK_EXCLUSIVE;
        trans_array[2].is_write = 1'b1;
        
        // Exclusive write to second address
        trans_array[3] = create_base_trans();
        trans_array[3].id = 0;
        trans_array[3].addr = 32'hF000_1000;
        trans_array[3].lock = AXI4_LOCK_EXCLUSIVE;
        trans_array[3].is_write = 1'b1;
        
        return trans_array;
    endfunction
    
endclass : axi4_multiple_exclusive_sequence

// Write interleaving attempt (illegal in AXI4)
class axi4_write_interleave_sequence extends axi4_error_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
        error_description = "Write data interleaving attempt (AXI4 violation)";
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        
        trans_array = new[2];
        
        // First write transaction
        trans_array[0] = create_base_trans();
        trans_array[0].id = 1;
        trans_array[0].addr = 32'hF100_0000;
        trans_array[0].len = 7;  // 8 beats
        trans_array[0].is_write = 1'b1;
        
        trans_array[0].data = new[8];
        trans_array[0].strb = new[8];
        for (int i = 0; i < 8; i++) begin
            trans_array[0].data[i] = {16'h1111, i[15:0]};
            trans_array[0].strb[i] = '1;
        end
        
        // Second write transaction (attempt to interleave)
        trans_array[1] = create_base_trans();
        trans_array[1].id = 2;
        trans_array[1].addr = 32'hF200_0000;
        trans_array[1].len = 7;  // 8 beats
        trans_array[1].is_write = 1'b1;
        
        trans_array[1].data = new[8];
        trans_array[1].strb = new[8];
        for (int i = 0; i < 8; i++) begin
            trans_array[1].data[i] = {16'h2222, i[15:0]};
            trans_array[1].strb[i] = '1;
        end
        
        return trans_array;
    endfunction
    
endclass : axi4_write_interleave_sequence