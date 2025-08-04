#!/usr/bin/env python3
"""Fix sequence classes to have configurable properties expected by tests"""

import re

# Read the generator file
with open('/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_environment_generator.py', 'r') as f:
    content = f.read()

# Fix axi4_master_write_seq
old_write_seq = '''class axi4_master_write_seq extends axi4_master_base_seq;
    
    `uvm_object_utils(axi4_master_write_seq)
    
    // Constructor
    function new(string name = "axi4_master_write_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_tx tx;
        
        repeat(num_trans) begin
            `uvm_do_with(tx, {{
                tx.tx_type == axi4_master_tx::WRITE;
                tx.awburst == axi4_globals_pkg::INCR;
                tx.awsize == axi4_globals_pkg::SIZE_4B;
                tx.awlen == 0;  // Single beat
            }})
        end
    endtask : body
    
endclass : axi4_master_write_seq'''

new_write_seq = '''class axi4_master_write_seq extends axi4_master_base_seq;
    
    `uvm_object_utils(axi4_master_write_seq)
    
    // Configurable parameters
    rand bit [63:0] start_address = 64'h0;
    rand int unsigned burst_length = 1;
    rand int unsigned burst_size = 4;  // Default 4 bytes
    rand bit [1:0] burst_type = 2'b01; // INCR
    
    // Constructor
    function new(string name = "axi4_master_write_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_tx tx;
        
        repeat(num_trans) begin
            `uvm_do_with(tx, {{
                tx.tx_type == axi4_master_tx::WRITE;
                tx.awaddr == start_address;
                tx.awburst == burst_type;
                tx.awsize == $clog2(burst_size);
                tx.awlen == burst_length - 1;
            }})
        end
    endtask : body
    
endclass : axi4_master_write_seq'''

content = content.replace(old_write_seq, new_write_seq)

# Fix axi4_master_read_seq
old_read_seq = '''class axi4_master_read_seq extends axi4_master_base_seq;
    
    `uvm_object_utils(axi4_master_read_seq)
    
    // Constructor
    function new(string name = "axi4_master_read_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_tx tx;
        
        repeat(num_trans) begin
            `uvm_do_with(tx, {{
                tx.tx_type == axi4_master_tx::READ;
                tx.arburst == axi4_globals_pkg::INCR;
                tx.arsize == axi4_globals_pkg::SIZE_4B;
                tx.arlen == 0;  // Single beat
            }})
        end
    endtask : body
    
endclass : axi4_master_read_seq'''

new_read_seq = '''class axi4_master_read_seq extends axi4_master_base_seq;
    
    `uvm_object_utils(axi4_master_read_seq)
    
    // Configurable parameters
    rand bit [63:0] start_address = 64'h0;
    rand int unsigned burst_length = 1;
    rand int unsigned burst_size = 4;  // Default 4 bytes
    rand bit [1:0] burst_type = 2'b01; // INCR
    
    // Constructor
    function new(string name = "axi4_master_read_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_tx tx;
        
        repeat(num_trans) begin
            `uvm_do_with(tx, {{
                tx.tx_type == axi4_master_tx::READ;
                tx.araddr == start_address;
                tx.arburst == burst_type;
                tx.arsize == $clog2(burst_size);
                tx.arlen == burst_length - 1;
            }})
        end
    endtask : body
    
endclass : axi4_master_read_seq'''

content = content.replace(old_read_seq, new_read_seq)

# Fix axi4_master_burst_seq
old_burst_seq = '''class axi4_master_burst_seq extends axi4_master_base_seq;
    
    `uvm_object_utils(axi4_master_burst_seq)
    
    // Burst parameters
    rand axi4_globals_pkg::burst_type_t burst_type;
    rand int unsigned burst_length;
    
    constraint valid_burst_c {{
        burst_length inside {{[1:256]}};
        (burst_type == axi4_globals_pkg::WRAP) -> burst_length inside {{2, 4, 8, 16}};
    }}
    
    // Constructor
    function new(string name = "axi4_master_burst_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_tx tx;
        
        `uvm_do_with(tx, {{
            tx.tx_type inside {{axi4_master_tx::WRITE, axi4_master_tx::READ}};
            if (tx.tx_type == axi4_master_tx::WRITE) {{
                tx.awburst == burst_type;
                tx.awlen == burst_length - 1;
            }} else {{
                tx.arburst == burst_type;
                tx.arlen == burst_length - 1;
            }}
        }})
    endtask : body
    
endclass : axi4_master_burst_seq'''

new_burst_seq = '''class axi4_master_burst_seq extends axi4_master_base_seq;
    
    `uvm_object_utils(axi4_master_burst_seq)
    
    // Burst parameters
    rand axi4_globals_pkg::burst_type_t burst_type;
    rand int unsigned burst_length;
    rand int unsigned burst_size = 4;  // Default 4 bytes
    rand bit [63:0] start_address = 64'h0;
    
    constraint valid_burst_c {{
        burst_length inside {{[1:256]}};
        (burst_type == axi4_globals_pkg::WRAP) -> burst_length inside {{2, 4, 8, 16}};
    }}
    
    // Constructor
    function new(string name = "axi4_master_burst_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_tx tx;
        
        `uvm_do_with(tx, {{
            tx.tx_type inside {{axi4_master_tx::WRITE, axi4_master_tx::READ}};
            if (tx.tx_type == axi4_master_tx::WRITE) {{
                tx.awaddr == start_address;
                tx.awburst == burst_type;
                tx.awlen == burst_length - 1;
                tx.awsize == $clog2(burst_size);
            }} else {{
                tx.araddr == start_address;
                tx.arburst == burst_type;
                tx.arlen == burst_length - 1;
                tx.arsize == $clog2(burst_size);
            }}
        }})
    endtask : body
    
endclass : axi4_master_burst_seq'''

content = content.replace(old_burst_seq, new_burst_seq)

# Write the fixed content back
with open('/home/timtim01/eda_test/project/gen_amba_2025/axi4_vip/gui/src/vip_environment_generator.py', 'w') as f:
    f.write(content)

print("Fixed sequence properties in generator file")