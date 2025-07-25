//==============================================================================
// AXI4 Basic Test Sequences
// 
// Description: Basic transaction sequences for AXI4 verification
// Includes single read/write, all burst types, and data width tests
//==============================================================================

`include "../../rtl/common/axi4_defines.sv"

class axi4_base_sequence;
    
    // Random constraints
    rand bit [63:0] addr;
    rand bit [7:0] len;
    rand bit [2:0] size;
    rand axi4_burst_t burst_type;
    rand bit [15:0] id;
    rand bit [3:0] qos;
    rand bit [3:0] region;
    rand axi4_prot_t prot;
    rand axi4_cache_t cache;
    
    // Configuration
    axi4_config_t cfg;
    
    // Constructor
    function new(axi4_config_t config);
        this.cfg = config;
    endfunction
    
    // Basic constraints
    constraint addr_c {
        addr[1:0] == 2'b00;  // Word aligned
        addr < 32'h1000_0000;  // Within reasonable range
    }
    
    constraint size_c {
        size <= $clog2(cfg.DATA_WIDTH/8);
    }
    
    constraint len_c {
        if (burst_type == AXI4_BURST_WRAP) {
            len inside {1, 3, 7, 15};
        } else if (burst_type == AXI4_BURST_INCR) {
            len <= 255;
        } else {
            len <= 15;
        }
    }
    
    constraint id_c {
        id < (1 << cfg.ID_WIDTH);
    }
    
    // Generate basic transaction
    virtual function axi4_transaction_t create_transaction();
        axi4_transaction_t trans;
        
        trans.addr = this.addr;
        trans.len = this.len;
        trans.size = this.size;
        trans.burst = this.burst_type;
        trans.id = this.id;
        trans.qos = this.qos;
        trans.region = this.region;
        trans.prot = this.prot;
        trans.cache = this.cache;
        trans.lock = AXI4_LOCK_NORMAL;
        
        // Allocate data arrays
        trans.data = new[len + 1];
        trans.strb = new[len + 1];
        trans.resp = new[len + 1];
        
        return trans;
    endfunction
    
endclass : axi4_base_sequence

// Single write sequence
class axi4_single_write_sequence extends axi4_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
    endfunction
    
    constraint single_c {
        len == 0;
        burst_type == AXI4_BURST_INCR;
    }
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        if (!this.randomize()) begin
            $error("Failed to randomize single write sequence");
        end
        
        trans = create_transaction();
        trans.is_write = 1'b1;
        
        // Generate random data
        for (int i = 0; i <= trans.len; i++) begin
            trans.data[i] = $random;
            trans.strb[i] = '1;  // All bytes valid
        end
        
        return trans;
    endfunction
    
endclass : axi4_single_write_sequence

// Single read sequence
class axi4_single_read_sequence extends axi4_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
    endfunction
    
    constraint single_c {
        len == 0;
        burst_type == AXI4_BURST_INCR;
    }
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        if (!this.randomize()) begin
            $error("Failed to randomize single read sequence");
        end
        
        trans = create_transaction();
        trans.is_write = 1'b0;
        
        return trans;
    endfunction
    
endclass : axi4_single_read_sequence

// Burst write sequence
class axi4_burst_write_sequence extends axi4_base_sequence;
    
    rand int burst_length;
    
    function new(axi4_config_t config);
        super.new(config);
    endfunction
    
    constraint burst_len_c {
        burst_length inside {4, 8, 16, 32, 64, 128, 256};
        len == burst_length - 1;
    }
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        if (!this.randomize()) begin
            $error("Failed to randomize burst write sequence");
        end
        
        trans = create_transaction();
        trans.is_write = 1'b1;
        
        // Generate sequential data pattern
        for (int i = 0; i <= trans.len; i++) begin
            trans.data[i] = {trans.addr[31:0], i[31:0]};
            trans.strb[i] = '1;
        end
        
        return trans;
    endfunction
    
endclass : axi4_burst_write_sequence

// WRAP burst sequence
class axi4_wrap_burst_sequence extends axi4_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
    endfunction
    
    constraint wrap_c {
        burst_type == AXI4_BURST_WRAP;
        len inside {3, 7, 15};  // 4, 8, 16 beat bursts
        // Ensure address is aligned to total burst size
        addr % ((len + 1) * (1 << size)) == 0;
    }
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        if (!this.randomize()) begin
            $error("Failed to randomize WRAP burst sequence");
        end
        
        trans = create_transaction();
        trans.is_write = ($urandom_range(1, 0) == 1);
        
        if (trans.is_write) begin
            for (int i = 0; i <= trans.len; i++) begin
                trans.data[i] = i;
                trans.strb[i] = '1;
            end
        end
        
        return trans;
    endfunction
    
endclass : axi4_wrap_burst_sequence

// Unaligned transfer sequence
class axi4_unaligned_sequence extends axi4_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
    endfunction
    
    constraint unaligned_c {
        // Force unaligned address
        addr[2:0] != 3'b000;
        len == 0;  // Single transfer
        burst_type == AXI4_BURST_INCR;
    }
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        if (!this.randomize()) begin
            $error("Failed to randomize unaligned sequence");
        end
        
        trans = create_transaction();
        trans.is_write = 1'b1;
        
        // Generate data with appropriate strobes
        trans.data[0] = $random;
        
        // Calculate strobes based on address alignment
        int start_byte = trans.addr % (cfg.DATA_WIDTH/8);
        int num_bytes = 1 << trans.size;
        
        trans.strb[0] = '0;
        for (int i = 0; i < num_bytes; i++) begin
            if (start_byte + i < cfg.DATA_WIDTH/8) begin
                trans.strb[0][start_byte + i] = 1'b1;
            end
        end
        
        return trans;
    endfunction
    
endclass : axi4_unaligned_sequence

// Back-to-back transactions sequence
class axi4_back_to_back_sequence extends axi4_base_sequence;
    
    int num_transactions;
    
    function new(axi4_config_t config);
        super.new(config);
        num_transactions = 10;
    endfunction
    
    virtual function axi4_transaction_t[] generate_sequence();
        axi4_transaction_t trans_array[];
        
        trans_array = new[num_transactions];
        
        for (int i = 0; i < num_transactions; i++) begin
            if (!this.randomize()) begin
                $error("Failed to randomize transaction %0d", i);
            end
            
            trans_array[i] = create_transaction();
            trans_array[i].is_write = (i % 2 == 0);
            
            if (trans_array[i].is_write) begin
                for (int j = 0; j <= trans_array[i].len; j++) begin
                    trans_array[i].data[j] = {i[31:0], j[31:0]};
                    trans_array[i].strb[j] = '1;
                end
            end
        end
        
        return trans_array;
    endfunction
    
endclass : axi4_back_to_back_sequence

// Maximum size burst sequence
class axi4_max_burst_sequence extends axi4_base_sequence;
    
    function new(axi4_config_t config);
        super.new(config);
    endfunction
    
    constraint max_burst_c {
        burst_type == AXI4_BURST_INCR;
        len == 255;  // Maximum burst length for INCR
        size == $clog2(cfg.DATA_WIDTH/8);  // Maximum size
        // Ensure doesn't cross 4KB
        addr[11:0] == 12'h000;
    }
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        
        if (!this.randomize()) begin
            $error("Failed to randomize max burst sequence");
        end
        
        trans = create_transaction();
        trans.is_write = 1'b1;
        
        // Generate incrementing data pattern
        for (int i = 0; i <= trans.len; i++) begin
            trans.data[i] = i;
            trans.strb[i] = '1;
        end
        
        return trans;
    endfunction
    
endclass : axi4_max_burst_sequence

// Different STRB pattern sequence
class axi4_strb_pattern_sequence extends axi4_base_sequence;
    
    typedef enum {
        STRB_ALL_BYTES,
        STRB_ALTERNATING,
        STRB_FIRST_LAST,
        STRB_RANDOM
    } strb_pattern_e;
    
    rand strb_pattern_e strb_pattern;
    
    function new(axi4_config_t config);
        super.new(config);
    endfunction
    
    virtual function axi4_transaction_t generate();
        axi4_transaction_t trans;
        int strb_width = cfg.DATA_WIDTH / 8;
        
        if (!this.randomize()) begin
            $error("Failed to randomize STRB pattern sequence");
        end
        
        trans = create_transaction();
        trans.is_write = 1'b1;
        
        for (int i = 0; i <= trans.len; i++) begin
            trans.data[i] = $random;
            
            case (strb_pattern)
                STRB_ALL_BYTES: trans.strb[i] = '1;
                STRB_ALTERNATING: begin
                    for (int j = 0; j < strb_width; j++) begin
                        trans.strb[i][j] = (j % 2);
                    end
                end
                STRB_FIRST_LAST: begin
                    trans.strb[i] = '0;
                    trans.strb[i][0] = 1'b1;
                    trans.strb[i][strb_width-1] = 1'b1;
                end
                STRB_RANDOM: trans.strb[i] = $random;
            endcase
        end
        
        return trans;
    endfunction
    
endclass : axi4_strb_pattern_sequence