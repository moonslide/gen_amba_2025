// AXI4 Transaction Class
import axi4_vip_pkg::*;

class axi4_transaction extends uvm_sequence_item;
    `uvm_object_utils(axi4_transaction)
    
    // Transaction type
    typedef enum {READ, WRITE} trans_type_e;
    rand trans_type_e trans_type;
    
    // Address channel
    rand bit [31:0] addr;
    rand bit [7:0] len;      // Burst length
    rand bit [2:0] size;     // Burst size
    rand bit [1:0] burst;    // Burst type
    rand bit [3:0] id;
    
    // Data
    rand bit [63:0] data[];
    rand bit [7:0] strb[];
    
    // Response
    bit [1:0] resp;
    
    // QoS and other signals
    rand bit [3:0] qos_aw;
    rand bit [3:0] qos_ar;
    rand bit [3:0] region;
    rand bit [3:0] cache;
    rand bit [2:0] prot;
    
    // Constraints
    constraint c_len {
        len inside {[0:255]};
    }
    
    constraint c_size {
        size inside {[0:$clog2(8)]}; 
    }
    
    constraint c_burst {
        burst inside {0, 1, 2}; // FIXED, INCR, WRAP
    }
    
    constraint c_data_size {
        data.size() == len + 1;
        strb.size() == len + 1;
    }
    
    function new(string name = "axi4_transaction");
        super.new(name);
    endfunction
    
    function void post_randomize();
        // Ensure data array is properly sized
        if(data.size() != len + 1) begin
            data = new[len + 1];
            strb = new[len + 1];
            foreach(data[i]) begin
                data[i] = $urandom();
                strb[i] = '1;
            end
        end
    endfunction
    
endclass
