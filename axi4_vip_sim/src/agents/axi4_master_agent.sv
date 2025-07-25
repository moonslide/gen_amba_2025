//==============================================================================
// AXI4 Master Agent - Integrates master driver, monitor, and sequencer
// Configurable as active or passive agent
//==============================================================================

class axi4_master_agent extends uvm_agent;
    
    // Factory registration
    `uvm_component_utils(axi4_master_agent)
    
    // Agent components
    axi4_master_driver m_driver;
    axi4_monitor m_monitor;
    uvm_sequencer #(axi4_transaction) m_sequencer;
    
    // Virtual interface handles
    virtual axi4_if.master master_vif;
    virtual axi4_if.monitor monitor_vif;
    
    // Analysis port for monitor transactions
    uvm_analysis_port #(axi4_transaction) ap;
    
    // Configuration
    bit is_active = UVM_ACTIVE;
    string agent_name = "master_agent";
    
    // Constructor
    function new(string name = "axi4_master_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        uvm_config_db#(bit)::get(this, "", "is_active", is_active);
        uvm_config_db#(string)::get(this, "", "agent_name", agent_name);
        
        // Get virtual interfaces
        if (!uvm_config_db#(virtual axi4_if.master)::get(this, "", "master_vif", master_vif)) begin
            `uvm_fatal("NOVIF", "Master virtual interface must be set for: " + get_full_name())
        end
        
        if (!uvm_config_db#(virtual axi4_if.monitor)::get(this, "", "monitor_vif", monitor_vif)) begin
            `uvm_fatal("NOVIF", "Monitor virtual interface must be set for: " + get_full_name())
        end
        
        // Create monitor (always present)
        m_monitor = axi4_monitor::type_id::create("m_monitor", this);
        uvm_config_db#(virtual axi4_if.monitor)::set(this, "m_monitor", "vif", monitor_vif);
        
        // Create active components if needed
        if (is_active == UVM_ACTIVE) begin
            m_driver = axi4_master_driver::type_id::create("m_driver", this);
            m_sequencer = uvm_sequencer#(axi4_transaction)::type_id::create("m_sequencer", this);
            
            // Set virtual interface for driver
            uvm_config_db#(virtual axi4_if.master)::set(this, "m_driver", "vif", master_vif);
        end
        
        `uvm_info(get_type_name(), $sformatf("Master agent %s created in %s mode", 
                                             agent_name, (is_active == UVM_ACTIVE) ? "ACTIVE" : "PASSIVE"), UVM_MEDIUM)
    endfunction
    
    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect monitor analysis port
        ap = m_monitor.ap;
        
        // Connect driver and sequencer if active
        if (is_active == UVM_ACTIVE) begin
            m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
        end
        
        `uvm_info(get_type_name(), $sformatf("Master agent %s connections completed", agent_name), UVM_MEDIUM)
    endfunction
    
    // Convenience function to start default sequence
    virtual task start_default_sequence();
        if (is_active == UVM_ACTIVE) begin
            axi4_basic_sequence basic_seq;
            basic_seq = axi4_basic_sequence::type_id::create("basic_seq");
            basic_seq.start(m_sequencer);
        end else begin
            `uvm_warning(get_type_name(), "Cannot start sequence on passive agent")
        end
    endtask
    
    // Convenience function to start specific sequence
    virtual task start_sequence(uvm_sequence_base seq);
        if (is_active == UVM_ACTIVE) begin
            seq.start(m_sequencer);
        end else begin
            `uvm_warning(get_type_name(), "Cannot start sequence on passive agent")
        end
    endtask
    
    // Get sequencer handle
    virtual function uvm_sequencer_base get_sequencer();
        if (is_active == UVM_ACTIVE) begin
            return m_sequencer;
        end else begin
            `uvm_warning(get_type_name(), "Sequencer not available in passive agent")
            return null;
        end
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), $sformatf("Master agent %s report:", agent_name), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Mode: %s", (is_active == UVM_ACTIVE) ? "ACTIVE" : "PASSIVE"), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Components: Driver=%s, Monitor=%s, Sequencer=%s", 
                                             (m_driver != null) ? "YES" : "NO",
                                             (m_monitor != null) ? "YES" : "NO", 
                                             (m_sequencer != null) ? "YES" : "NO"), UVM_LOW)
    endfunction
    
endclass : axi4_master_agent


//==============================================================================
// AXI4 Slave Agent - Integrates slave driver and monitor
// Configurable as active or passive agent
//==============================================================================

class axi4_slave_agent extends uvm_agent;
    
    // Factory registration
    `uvm_component_utils(axi4_slave_agent)
    
    // Agent components
    axi4_slave_driver s_driver;
    axi4_monitor s_monitor;
    
    // Virtual interface handles
    virtual axi4_if.slave slave_vif;
    virtual axi4_if.monitor monitor_vif;
    
    // Analysis port for monitor transactions
    uvm_analysis_port #(axi4_transaction) ap;
    
    // Configuration
    bit is_active = UVM_ACTIVE;
    string agent_name = "slave_agent";
    bit [63:0] base_address = 64'h1000_0000;
    bit [63:0] size_bytes = 64'h1000_0000;
    
    // Constructor
    function new(string name = "axi4_slave_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        uvm_config_db#(bit)::get(this, "", "is_active", is_active);
        uvm_config_db#(string)::get(this, "", "agent_name", agent_name);
        uvm_config_db#(bit [63:0])::get(this, "", "base_address", base_address);
        uvm_config_db#(bit [63:0])::get(this, "", "size_bytes", size_bytes);
        
        // Get virtual interfaces
        if (!uvm_config_db#(virtual axi4_if.slave)::get(this, "", "slave_vif", slave_vif)) begin
            `uvm_fatal("NOVIF", "Slave virtual interface must be set for: " + get_full_name())
        end
        
        if (!uvm_config_db#(virtual axi4_if.monitor)::get(this, "", "monitor_vif", monitor_vif)) begin
            `uvm_fatal("NOVIF", "Monitor virtual interface must be set for: " + get_full_name())
        end
        
        // Create monitor (always present)
        s_monitor = axi4_monitor::type_id::create("s_monitor", this);
        uvm_config_db#(virtual axi4_if.monitor)::set(this, "s_monitor", "vif", monitor_vif);
        
        // Create active components if needed
        if (is_active == UVM_ACTIVE) begin
            s_driver = axi4_slave_driver::type_id::create("s_driver", this);
            
            // Set virtual interface and configuration for driver
            uvm_config_db#(virtual axi4_if.slave)::set(this, "s_driver", "vif", slave_vif);
            uvm_config_db#(bit [63:0])::set(this, "s_driver", "base_address", base_address);
            uvm_config_db#(bit [63:0])::set(this, "s_driver", "size_bytes", size_bytes);
        end
        
        `uvm_info(get_type_name(), $sformatf("Slave agent %s created in %s mode, Address range: 0x%0h-0x%0h", 
                                             agent_name, (is_active == UVM_ACTIVE) ? "ACTIVE" : "PASSIVE",
                                             base_address, base_address + size_bytes - 1), UVM_MEDIUM)
    endfunction
    
    // Connect phase
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect monitor analysis port
        ap = s_monitor.ap;
        
        `uvm_info(get_type_name(), $sformatf("Slave agent %s connections completed", agent_name), UVM_MEDIUM)
    endfunction
    
    // Configuration functions
    virtual function void set_address_range(bit [63:0] base, bit [63:0] size);
        base_address = base;
        size_bytes = size;
        if (s_driver != null) begin
            // Update driver configuration at runtime
            s_driver.base_address = base;
            s_driver.size_bytes = size;
        end
        `uvm_info(get_type_name(), $sformatf("Address range updated: 0x%0h-0x%0h", base, base + size - 1), UVM_MEDIUM)
    endfunction
    
    virtual function void set_error_rate(int percent);
        if (s_driver != null) begin
            s_driver.error_rate_percent = percent;
            `uvm_info(get_type_name(), $sformatf("Error rate set to %0d%%", percent), UVM_MEDIUM)
        end
    endfunction
    
    virtual function void set_latency_range(int read_min, int read_max, int write_min, int write_max);
        if (s_driver != null) begin
            s_driver.read_latency_min = read_min;
            s_driver.read_latency_max = read_max;
            s_driver.write_latency_min = write_min;
            s_driver.write_latency_max = write_max;
            `uvm_info(get_type_name(), $sformatf("Latency ranges updated: Read[%0d:%0d], Write[%0d:%0d]", 
                                                 read_min, read_max, write_min, write_max), UVM_MEDIUM)
        end
    endfunction
    
    // Memory access functions
    virtual function void write_memory(bit [63:0] addr, bit [7:0] data);
        if (s_driver != null) begin
            s_driver.memory[addr] = data;
            `uvm_info(get_type_name(), $sformatf("Memory initialized: Addr=0x%0h, Data=0x%02h", addr, data), UVM_HIGH)
        end
    endfunction
    
    virtual function bit [7:0] read_memory(bit [63:0] addr);
        if (s_driver != null && s_driver.memory.exists(addr)) begin
            return s_driver.memory[addr];
        end else begin
            return 8'h00;
        end
    endfunction
    
    virtual function void clear_memory();
        if (s_driver != null) begin
            s_driver.memory.delete();
            `uvm_info(get_type_name(), "Memory cleared", UVM_MEDIUM)
        end
    endfunction
    
    // Report phase
    virtual function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), $sformatf("Slave agent %s report:", agent_name), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Mode: %s", (is_active == UVM_ACTIVE) ? "ACTIVE" : "PASSIVE"), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Address Range: 0x%0h - 0x%0h", base_address, base_address + size_bytes - 1), UVM_LOW)
        `uvm_info(get_type_name(), $sformatf("  Components: Driver=%s, Monitor=%s", 
                                             (s_driver != null) ? "YES" : "NO",
                                             (s_monitor != null) ? "YES" : "NO"), UVM_LOW)
        if (s_driver != null) begin
            `uvm_info(get_type_name(), $sformatf("  Memory Entries: %0d", s_driver.memory.size()), UVM_LOW)
        end
    endfunction
    
endclass : axi4_slave_agent