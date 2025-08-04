#!/usr/bin/env python3
"""
VIP Environment Generator following tim_axi4_vip structure
Generates a complete UVM-based AXI4 VIP environment with proper folder hierarchy
"""

import os
import json
from datetime import datetime
from dataclasses import asdict

class VIPEnvironmentGenerator:
    """Generate VIP environment following tim_axi4_vip structure"""
    
    def __init__(self, gui_config, mode, simulator="vcs"):
        self.config = gui_config
        self.mode = mode  # "rtl_integration" or "vip_standalone"
        self.simulator = simulator
        self.timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        self.warnings = []  # Collect configuration warnings
        
    def _validate_configuration(self):
        """Validate configuration and collect warnings"""
        self.warnings = []
        
        if self.config.masters:
            # Check ID width consistency
            id_widths = [master.id_width for master in self.config.masters]
            if len(set(id_widths)) > 1:
                self.warnings.append(f"WARNING: Masters have different ID widths: {', '.join([f'{m.name}={m.id_width}' for m in self.config.masters])}")
                self.warnings.append(f"         Using maximum ID width ({max(id_widths)}) for interconnect")
            
            # Check USER width consistency
            user_widths = [master.user_width for master in self.config.masters]
            if len(set(user_widths)) > 1:
                self.warnings.append(f"WARNING: Masters have different USER widths: {', '.join([f'{m.name}={m.user_width}' for m in self.config.masters])}")
                self.warnings.append(f"         Using maximum USER width ({max(user_widths)}) for interconnect")
        
        return self.warnings
    
    def _format_warnings(self):
        """Format warnings for documentation"""
        if not self.warnings:
            return ""
        
        warning_text = "\n### Configuration Warnings\n"
        for warning in self.warnings:
            warning_text += f"- {warning}\n"
        warning_text += "\n"
        return warning_text
    
    def generate_environment(self, output_dir):
        """Generate complete VIP environment"""
        # Validate configuration first
        self._validate_configuration()
        
        # Print warnings to console
        if self.warnings:
            print("\n⚠️  Configuration Warnings:")
            for warning in self.warnings:
                print(f"   {warning}")
            print()
        
        env_name = f"axi4_vip_env_{self.mode}"
        env_path = os.path.join(output_dir, env_name)
        
        # Create tim_axi4_vip-like directory structure
        self._create_directory_structure(env_path)
        
        # Generate all files
        self._generate_package_files(env_path)
        self._generate_interface_files(env_path)
        self._generate_agent_files(env_path)
        self._generate_sequence_files(env_path)
        self._generate_environment_files(env_path)
        self._generate_test_files(env_path)
        self._generate_top_files(env_path)
        self._generate_simulation_files(env_path)
        self._generate_documentation(env_path)
        
        # Generate Verdi integration features
        self._generate_verdi_integration(env_path)
        
        # For RTL integration, generate wrapper
        if self.mode == "rtl_integration":
            self._generate_rtl_wrapper(env_path)
            
        return env_path
    
    def _create_directory_structure(self, base_path):
        """Create tim_axi4_vip-like directory structure"""
        dirs = [
            # Core UVM component directories
            "agent",
            "agent/master_agent_bfm",
            "agent/slave_agent_bfm",
            "assertions",
            "bm",  # Bus matrix components
            "doc",
            "env",
            "include",
            "intf",
            "intf/axi4_interface",
            "master",
            "pkg",
            "seq",
            "seq/master_sequences",
            "seq/slave_sequences",
            "sim",
            "sim/scripts",
            "sim/results",
            "sim/logs",
            "sim/waves",
            "sim/coverage",
            "slave",
            "test",
            "testlists",
            "top",
            "virtual_seq",
            "virtual_seqr",
        ]
        
        # Add RTL-specific directories if in RTL integration mode
        if self.mode == "rtl_integration":
            dirs.extend([
                "rtl_wrapper",
                "rtl_wrapper/generated_rtl",
            ])
        
        for dir_path in dirs:
            os.makedirs(os.path.join(base_path, dir_path), exist_ok=True)
    
    def _generate_package_files(self, base_path):
        """Generate package definition files"""
        # Get maximum ID width from all masters (interconnect must support largest ID)
        if self.config.masters:
            id_widths = [master.id_width for master in self.config.masters]
            id_width = max(id_widths)
            # Check if all masters have same ID width
            if len(set(id_widths)) > 1:
                id_comment = f"  // Max of master ID widths: {id_widths}"
            else:
                id_comment = "  // All masters use same ID width"
        else:
            id_width = 4
            id_comment = "  // Default (no masters configured)"
            
        # Get maximum USER width from all masters  
        if self.config.masters:
            user_widths = [master.user_width for master in self.config.masters]
            user_width = max(user_widths)
            # Check if all masters have same USER width
            if len(set(user_widths)) > 1:
                user_comment = f"  // Max of master USER widths: {user_widths}"
            else:
                user_comment = "  // All masters use same USER width"
        else:
            user_width = 1
            user_comment = "  // Default (no masters configured)"
        
        # axi4_globals_pkg.sv
        with open(os.path.join(base_path, "pkg/axi4_globals_pkg.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Global Package
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

package axi4_globals_pkg;
    
    // Import UVM package
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Global parameters from GUI configuration
    parameter NO_OF_MASTERS    = {len(self.config.masters)};
    parameter NO_OF_SLAVES     = {len(self.config.slaves)};
    parameter ADDRESS_WIDTH    = {self.config.addr_width};
    parameter DATA_WIDTH       = {self.config.data_width};
    parameter ID_WIDTH         = {id_width};{id_comment}
    parameter STRB_WIDTH       = DATA_WIDTH/8;
    parameter USER_WIDTH       = {user_width};{user_comment}
    
    // Slave memory configuration
    parameter SLAVE_MEMORY_SIZE = 12288;  // 12KB default
    parameter MEMORY_WIDTH      = 8;
    parameter SLAVE_MEMORY_DEPTH = SLAVE_MEMORY_SIZE/MEMORY_WIDTH;
    
    // Transaction types
    typedef enum bit [1:0] {{
        FIXED = 2'b00,
        INCR  = 2'b01,
        WRAP  = 2'b10,
        RSVD  = 2'b11
    }} axi4_burst_type_e;
    
    // Response types
    typedef enum bit [1:0] {{
        OKAY   = 2'b00,
        EXOKAY = 2'b01,
        SLVERR = 2'b10,
        DECERR = 2'b11
    }} axi4_response_type_e;
    
    // Lock types
    typedef enum bit {{
        NORMAL    = 1'b0,
        EXCLUSIVE = 1'b1
    }} axi4_lock_type_e;
    
    // Size encoding
    typedef enum bit [2:0] {{
        SIZE_1B   = 3'b000,
        SIZE_2B   = 3'b001,
        SIZE_4B   = 3'b010,
        SIZE_8B   = 3'b011,
        SIZE_16B  = 3'b100,
        SIZE_32B  = 3'b101,
        SIZE_64B  = 3'b110,
        SIZE_128B = 3'b111
    }} axi4_size_e;
    
    // Cache encoding
    typedef struct packed {{
        bit allocate;
        bit other_allocate;
        bit modifiable;
        bit bufferable;
    }} axi4_cache_t;
    
    // Protection encoding
    typedef struct packed {{
        bit instruction;
        bit nonsecure;
        bit privileged;
    }} axi4_prot_t;
    
    // Slave configuration from GUI
    typedef struct {{
        string name;
        bit [ADDRESS_WIDTH-1:0] base_addr;
        bit [ADDRESS_WIDTH-1:0] end_addr;
        int memory_size;
    }} slave_config_t;
    
    // Master configuration from GUI
    typedef struct {{
        string name;
        int id_width;
        bit qos_support;
        bit exclusive_support;
    }} master_config_t;
    
    // Generated configurations
""")
            # Add master configurations
            f.write("    master_config_t master_configs[NO_OF_MASTERS] = '{\n")
            for i, master in enumerate(self.config.masters):
                f.write(f"        '{{\"{master.name}\", {master.id_width}, {int(master.qos_support)}, {int(master.exclusive_support)}}}")
                if i < len(self.config.masters) - 1:
                    f.write(",")
                f.write("\n")
            f.write("    };\n\n")
            
            # Add slave configurations
            f.write("    slave_config_t slave_configs[NO_OF_SLAVES] = '{\n")
            for i, slave in enumerate(self.config.slaves):
                end_addr = slave.base_address + (slave.size * 1024) - 1
                memory_size = slave.size * 1024
                # Use 64-bit size specifier for large memory sizes
                if memory_size > 2147483647:  # > 2GB
                    f.write(f"        '{{\"{slave.name}\", 'h{slave.base_address:X}, 'h{end_addr:X}, 64'd{memory_size}}}")
                else:
                    f.write(f"        '{{\"{slave.name}\", 'h{slave.base_address:X}, 'h{end_addr:X}, 32'd{memory_size}}}")
                if i < len(self.config.slaves) - 1:
                    f.write(",")
                f.write("\n")
            f.write("    };\n\n")
            
            f.write("""endpackage : axi4_globals_pkg
""")
    
    def _generate_interface_files(self, base_path):
        """Generate interface files"""
        # Get maximum ID width from all masters (interconnect must support largest ID)
        if self.config.masters:
            id_widths = [master.id_width for master in self.config.masters]
            id_width = max(id_widths)
        else:
            id_width = 4
            
        # Get maximum USER width from all masters  
        if self.config.masters:
            user_widths = [master.user_width for master in self.config.masters]
            user_width = max(user_widths)
        else:
            user_width = 1
        
        # axi4_if.sv
        with open(os.path.join(base_path, "intf/axi4_interface/axi4_if.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Interface
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

interface axi4_if #(
    parameter ADDR_WIDTH = {self.config.addr_width},
    parameter DATA_WIDTH = {self.config.data_width},
    parameter ID_WIDTH   = {id_width},
    parameter USER_WIDTH = {user_width}
)(
    input logic aclk,
    input logic aresetn
);

    // Import global package
    import axi4_globals_pkg::*;
    
    // Write Address Channel
    logic [ID_WIDTH-1:0]     awid;
    logic [ADDR_WIDTH-1:0]   awaddr;
    logic [7:0]              awlen;
    logic [2:0]              awsize;
    logic [1:0]              awburst;
    logic                    awlock;
    logic [3:0]              awcache;
    logic [2:0]              awprot;
    logic [3:0]              awqos;
    logic [3:0]              awregion;
    logic [USER_WIDTH-1:0]   awuser;
    logic                    awvalid;
    logic                    awready;
    
    // Write Data Channel
    logic [DATA_WIDTH-1:0]   wdata;
    logic [STRB_WIDTH-1:0]   wstrb;
    logic                    wlast;
    logic [USER_WIDTH-1:0]   wuser;
    logic                    wvalid;
    logic                    wready;
    
    // Write Response Channel
    logic [ID_WIDTH-1:0]     bid;
    logic [1:0]              bresp;
    logic [USER_WIDTH-1:0]   buser;
    logic                    bvalid;
    logic                    bready;
    
    // Read Address Channel
    logic [ID_WIDTH-1:0]     arid;
    logic [ADDR_WIDTH-1:0]   araddr;
    logic [7:0]              arlen;
    logic [2:0]              arsize;
    logic [1:0]              arburst;
    logic                    arlock;
    logic [3:0]              arcache;
    logic [2:0]              arprot;
    logic [3:0]              arqos;
    logic [3:0]              arregion;
    logic [USER_WIDTH-1:0]   aruser;
    logic                    arvalid;
    logic                    arready;
    
    // Read Data Channel
    logic [ID_WIDTH-1:0]     rid;
    logic [DATA_WIDTH-1:0]   rdata;
    logic [1:0]              rresp;
    logic                    rlast;
    logic [USER_WIDTH-1:0]   ruser;
    logic                    rvalid;
    logic                    rready;
    
    // Modports
    modport master (
        input  aclk, aresetn,
        output awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid,
        input  awready,
        output wdata, wstrb, wlast, wuser, wvalid,
        input  wready,
        input  bid, bresp, buser, bvalid,
        output bready,
        output arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser, arvalid,
        input  arready,
        input  rid, rdata, rresp, rlast, ruser, rvalid,
        output rready
    );
    
    modport slave (
        input  aclk, aresetn,
        input  awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid,
        output awready,
        input  wdata, wstrb, wlast, wuser, wvalid,
        output wready,
        output bid, bresp, buser, bvalid,
        input  bready,
        input  arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser, arvalid,
        output arready,
        output rid, rdata, rresp, rlast, ruser, rvalid,
        input  rready
    );
    
    modport monitor (
        input aclk, aresetn,
        input awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser, awvalid, awready,
        input wdata, wstrb, wlast, wuser, wvalid, wready,
        input bid, bresp, buser, bvalid, bready,
        input arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser, arvalid, arready,
        input rid, rdata, rresp, rlast, ruser, rvalid, rready
    );

endinterface : axi4_if
""")
    
    def _generate_agent_files(self, base_path):
        """Generate agent BFM files"""
        # Master agent BFM
        with open(os.path.join(base_path, "agent/master_agent_bfm/axi4_master_agent_bfm.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Master Agent BFM
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

interface axi4_master_agent_bfm #(
    parameter ADDR_WIDTH = {self.config.addr_width},
    parameter DATA_WIDTH = {self.config.data_width},
    parameter ID_WIDTH   = 4
)(
    input aclk,
    input aresetn
);

    import axi4_globals_pkg::*;
    
    // Master driver BFM instance (interface instantiation)
    axi4_master_driver_bfm master_driver_bfm_h(aclk, aresetn);
    
    // Master monitor BFM instance (interface instantiation)
    axi4_master_monitor_bfm master_monitor_bfm_h(aclk, aresetn);

endinterface : axi4_master_agent_bfm
""")
        
        # Create stub driver and monitor BFMs
        with open(os.path.join(base_path, "agent/master_agent_bfm/axi4_master_driver_bfm.sv"), "w") as f:
            f.write(f"""// Stub master driver BFM - replace with actual implementation
interface axi4_master_driver_bfm(input aclk, input aresetn);
endinterface
""")
        
        with open(os.path.join(base_path, "agent/master_agent_bfm/axi4_master_monitor_bfm.sv"), "w") as f:
            f.write(f"""// Stub master monitor BFM - replace with actual implementation
interface axi4_master_monitor_bfm(input aclk, input aresetn);
endinterface
""")
        
        # Similarly generate slave agent BFM
        with open(os.path.join(base_path, "agent/slave_agent_bfm/axi4_slave_agent_bfm.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Slave Agent BFM
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

interface axi4_slave_agent_bfm #(
    parameter ADDR_WIDTH = {self.config.addr_width},
    parameter DATA_WIDTH = {self.config.data_width},
    parameter ID_WIDTH   = 4
)(
    input aclk,
    input aresetn
);

    import axi4_globals_pkg::*;
    
    // Slave driver BFM instance (interface instantiation)
    axi4_slave_driver_bfm slave_driver_bfm_h(aclk, aresetn);
    
    // Slave monitor BFM instance (interface instantiation) 
    axi4_slave_monitor_bfm slave_monitor_bfm_h(aclk, aresetn);

endinterface : axi4_slave_agent_bfm
""")
        
        # Create stub slave driver and monitor BFMs
        with open(os.path.join(base_path, "agent/slave_agent_bfm/axi4_slave_driver_bfm.sv"), "w") as f:
            f.write(f"""// Stub slave driver BFM - replace with actual implementation
interface axi4_slave_driver_bfm(input aclk, input aresetn);
endinterface
""")
        
        with open(os.path.join(base_path, "agent/slave_agent_bfm/axi4_slave_monitor_bfm.sv"), "w") as f:
            f.write(f"""// Stub slave monitor BFM - replace with actual implementation  
interface axi4_slave_monitor_bfm(input aclk, input aresetn);
endinterface
""")
    
    def _generate_agent_packages(self, base_path):
        """Generate agent package files"""
        # Master package
        with open(os.path.join(base_path, "master/axi4_master_pkg.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Master Package
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

package axi4_master_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    
    // Transaction class
    class axi4_master_tx extends uvm_sequence_item;
        `uvm_object_utils(axi4_master_tx)
        
        // Transaction type
        typedef enum {{WRITE, READ}} tx_type_e;
        rand tx_type_e tx_type;
        
        // Address channel
        rand bit [ADDRESS_WIDTH-1:0] awaddr;
        rand bit [7:0] awlen;
        rand bit [2:0] awsize;
        rand bit [1:0] awburst;
        rand bit [3:0] awid;
        rand bit [3:0] awqos;
        rand bit [3:0] awregion;
        rand bit awlock;
        rand bit [3:0] awcache;
        rand bit [2:0] awprot;
        
        // Data channel
        rand bit [DATA_WIDTH-1:0] wdata[];
        
        // Read address channel  
        rand bit [ADDRESS_WIDTH-1:0] araddr;
        rand bit [7:0] arlen;
        rand bit [2:0] arsize;
        rand bit [1:0] arburst;
        rand bit [3:0] arid;
        rand bit [3:0] arqos;
        rand bit [3:0] arregion;
        rand bit arlock;
        rand bit [3:0] arcache;
        rand bit [2:0] arprot;
        
        // Read data
        bit [DATA_WIDTH-1:0] rdata[];
        bit [1:0] rresp[];
        
        function new(string name = "axi4_master_tx");
            super.new(name);
        endfunction
    endclass
    
    // Master agent config
    class axi4_master_agent_config extends uvm_object;
        `uvm_object_utils(axi4_master_agent_config)
        
        bit is_active = UVM_ACTIVE;
        
        function new(string name = "axi4_master_agent_config");
            super.new(name);
        endfunction
    endclass
    
    // Sequencer class
    class axi4_master_sequencer extends uvm_sequencer #(axi4_master_tx);
        `uvm_component_utils(axi4_master_sequencer)
        
        function new(string name = "axi4_master_sequencer", uvm_component parent = null);
            super.new(name, parent);
        endfunction
    endclass
    
    // Driver class (stub)
    class axi4_master_driver extends uvm_driver #(axi4_master_tx);
        `uvm_component_utils(axi4_master_driver)
        
        function new(string name = "axi4_master_driver", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            `uvm_info(get_type_name(), "Starting master driver run_phase", UVM_LOW)
            forever begin
                `uvm_info(get_type_name(), "Waiting for next transaction from sequencer", UVM_HIGH)
                seq_item_port.get_next_item(req);
                
                `uvm_info(get_type_name(), $sformatf("Got %s transaction - addr=0x%0h, len=%0d, size=%0d, burst=%0d", 
                    req.tx_type.name(), 
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awaddr : req.araddr,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awlen : req.arlen,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awsize : req.arsize,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awburst : req.arburst), UVM_MEDIUM)
                
                `uvm_info(get_type_name(), $sformatf("Transaction details - id=%0d, qos=%0d, region=%0d, cache=0x%0h, prot=%0d",
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awid : req.arid,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awqos : req.arqos,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awregion : req.arregion,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awcache : req.arcache,
                    (req.tx_type == axi4_master_tx::WRITE) ? req.awprot : req.arprot), UVM_HIGH)
                
                if (req.tx_type == axi4_master_tx::WRITE && req.wdata.size() > 0) begin
                    `uvm_info(get_type_name(), $sformatf("Write data: %0d beats, first_data=0x%0h", 
                        req.wdata.size(), req.wdata[0]), UVM_HIGH)
                end
                
                `uvm_info(get_type_name(), "Driving transaction to BFM interface", UVM_HIGH)
                #100ns;
                
                `uvm_info(get_type_name(), "Transaction completed, signaling item_done", UVM_HIGH)
                seq_item_port.item_done();
            end
        endtask
    endclass
    
    // Monitor class - FIXED: No direct interface access
    class axi4_master_monitor extends uvm_monitor;
        `uvm_component_utils(axi4_master_monitor)
        
        uvm_analysis_port #(axi4_master_tx) item_collected_port;
        
        function new(string name = "axi4_master_monitor", uvm_component parent = null);
            super.new(name, parent);
            item_collected_port = new("item_collected_port", this);
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            `uvm_info(get_type_name(), "Starting master monitor run_phase", UVM_LOW)
            `uvm_info(get_type_name(), "Monitoring AXI4 master interface for transactions", UVM_MEDIUM)
            
            // Monitor stub - just log activity without interface access
            forever begin
                #100ns;
                `uvm_info(get_type_name(), "Monitor active - checking for transactions", UVM_HIGH)
            end
        endtask
    endclass
    
    // Agent class
    class axi4_master_agent extends uvm_agent;
        `uvm_component_utils(axi4_master_agent)
        
        axi4_master_agent_config cfg;
        axi4_master_sequencer sequencer;
        axi4_master_driver driver;
        axi4_master_monitor monitor;
        
        function new(string name = "axi4_master_agent", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            `uvm_info(get_type_name(), "Building master agent components", UVM_LOW)
            
            // Get configuration
            if(!uvm_config_db#(axi4_master_agent_config)::get(this, "", "cfg", cfg))
                `uvm_fatal("CONFIG", "Cannot get master agent config from uvm_config_db")
            
            `uvm_info(get_type_name(), $sformatf("Master agent mode: %s", 
                (cfg.is_active == UVM_ACTIVE) ? "ACTIVE" : "PASSIVE"), UVM_MEDIUM)
            
            if(cfg.is_active == UVM_ACTIVE) begin
                sequencer = axi4_master_sequencer::type_id::create("sequencer", this);
                driver = axi4_master_driver::type_id::create("driver", this);
                `uvm_info(get_type_name(), "Created sequencer and driver for active agent", UVM_HIGH)
            end
            monitor = axi4_master_monitor::type_id::create("monitor", this);
            `uvm_info(get_type_name(), "Created monitor", UVM_HIGH)
        endfunction
        
        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            `uvm_info(get_type_name(), "Connecting master agent components", UVM_LOW)
            
            if(cfg.is_active == UVM_ACTIVE) begin
                driver.seq_item_port.connect(sequencer.seq_item_export);
                `uvm_info(get_type_name(), "Connected driver to sequencer", UVM_HIGH)
            end
        endfunction
    endclass
    
endpackage : axi4_master_pkg
""")
        
        # Slave package
        with open(os.path.join(base_path, "slave/axi4_slave_pkg.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Slave Package  
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

package axi4_slave_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    
    // Transaction class
    class axi4_slave_tx extends uvm_sequence_item;
        `uvm_object_utils(axi4_slave_tx)
        
        // Response fields
        rand bit [1:0] bresp;
        rand bit [1:0] rresp;
        
        function new(string name = "axi4_slave_tx");
            super.new(name);
        endfunction
    endclass
    
    // Slave agent config
    class axi4_slave_agent_config extends uvm_object;
        `uvm_object_utils(axi4_slave_agent_config)
        
        bit is_active = UVM_ACTIVE;
        bit slave_memory_mode_enable = 1;
        
        // Address mapping
        bit [31:0] start_addr = 32'h0;
        bit [31:0] end_addr = 32'hFFFF_FFFF;
        
        function new(string name = "axi4_slave_agent_config");
            super.new(name);
        endfunction
    endclass
    
    // Sequencer class
    class axi4_slave_sequencer extends uvm_sequencer #(axi4_slave_tx);
        `uvm_component_utils(axi4_slave_sequencer)
        
        function new(string name = "axi4_slave_sequencer", uvm_component parent = null);
            super.new(name, parent);
        endfunction
    endclass
    
    // Driver class (stub)
    class axi4_slave_driver extends uvm_driver #(axi4_slave_tx);
        `uvm_component_utils(axi4_slave_driver)
        
        function new(string name = "axi4_slave_driver", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            forever begin
                seq_item_port.get_next_item(req);
                `uvm_info(get_type_name(), "Driving response", UVM_MEDIUM)
                #100ns;
                seq_item_port.item_done();
            end
        endtask
    endclass
    
    // Monitor class - FIXED: No direct interface access
    class axi4_slave_monitor extends uvm_monitor;
        `uvm_component_utils(axi4_slave_monitor)
        
        uvm_analysis_port #(axi4_slave_tx) item_collected_port;
        
        function new(string name = "axi4_slave_monitor", uvm_component parent = null);
            super.new(name, parent);
            item_collected_port = new("item_collected_port", this);
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            `uvm_info(get_type_name(), "Starting slave monitor run_phase", UVM_LOW)
            `uvm_info(get_type_name(), "Monitoring AXI4 slave interface for transactions", UVM_MEDIUM)
            
            // Monitor stub - just log activity without interface access
            forever begin
                #100ns;
                `uvm_info(get_type_name(), "Monitor active - checking for transactions", UVM_HIGH)
            end
        endtask
    endclass
    
    // Agent class
    class axi4_slave_agent extends uvm_agent;
        `uvm_component_utils(axi4_slave_agent)
        
        axi4_slave_agent_config cfg;
        axi4_slave_sequencer sequencer;
        axi4_slave_driver driver;
        axi4_slave_monitor monitor;
        
        function new(string name = "axi4_slave_agent", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            `uvm_info(get_type_name(), "Building slave agent components", UVM_LOW)
            
            // Get configuration
            if(!uvm_config_db#(axi4_slave_agent_config)::get(this, "", "cfg", cfg))
                `uvm_fatal("CONFIG", "Cannot get slave agent config from uvm_config_db")
            
            `uvm_info(get_type_name(), $sformatf("Slave agent mode: %s", 
                (cfg.is_active == UVM_ACTIVE) ? "ACTIVE" : "PASSIVE"), UVM_MEDIUM)
            
            if(cfg.is_active == UVM_ACTIVE) begin
                sequencer = axi4_slave_sequencer::type_id::create("sequencer", this);
                driver = axi4_slave_driver::type_id::create("driver", this);
                `uvm_info(get_type_name(), "Created sequencer and driver for active agent", UVM_HIGH)
            end
            monitor = axi4_slave_monitor::type_id::create("monitor", this);
            `uvm_info(get_type_name(), "Created monitor", UVM_HIGH)
        endfunction
        
        function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            `uvm_info(get_type_name(), "Connecting slave agent components", UVM_LOW)
            
            if(cfg.is_active == UVM_ACTIVE) begin
                driver.seq_item_port.connect(sequencer.seq_item_export);
                `uvm_info(get_type_name(), "Connected driver to sequencer", UVM_HIGH)
            end
        endfunction
    endclass
    
endpackage : axi4_slave_pkg
""")
        
        # Create sequence packages
        with open(os.path.join(base_path, "seq/master_sequences/axi4_master_seq_pkg.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Master Sequence Package
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

package axi4_master_seq_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    import axi4_master_pkg::*;
    
    // Include sequence files
    `include "axi4_master_base_seq.sv"
    `include "axi4_master_write_seq.sv"
    `include "axi4_master_read_seq.sv"
    
endpackage : axi4_master_seq_pkg
""")
        
        with open(os.path.join(base_path, "seq/slave_sequences/axi4_slave_seq_pkg.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Slave Sequence Package
// Generated by AMBA Bus Matrix Configuration Tool  
// Date: {self.timestamp}
//==============================================================================

package axi4_slave_seq_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    import axi4_slave_pkg::*;
    
    // Include sequence files
    `include "axi4_slave_base_seq.sv"
    
endpackage : axi4_slave_seq_pkg
""")
    
    def _generate_sequence_files(self, base_path):
        """Generate basic sequence files"""
        # First create the master and slave packages needed for sequences
        self._generate_agent_packages(base_path)
        
        # Master base sequence
        with open(os.path.join(base_path, "seq/master_sequences/axi4_master_base_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Master Base Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_master_base_seq extends uvm_sequence #(axi4_master_tx);
    
    `uvm_object_utils(axi4_master_base_seq)
    
    // Number of transactions
    int num_trans = 1;
    
    // Constructor
    function new(string name = "axi4_master_base_seq");
        super.new(name);
    endfunction
    
    // Pre body
    virtual task pre_body();
        // Objection handling if needed
    endtask
    
    // Post body  
    virtual task post_body();
        // Objection handling if needed
    endtask
    
    // Body method
    virtual task body();
        `uvm_info(get_type_name(), "Starting base sequence", UVM_MEDIUM)
    endtask : body
    
endclass : axi4_master_base_seq
""")
        
        # Master write sequence
        with open(os.path.join(base_path, "seq/master_sequences/axi4_master_write_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Master Write Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_master_write_seq extends axi4_master_base_seq;
    
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
    
endclass : axi4_master_write_seq
""")
        
        # Master read sequence
        with open(os.path.join(base_path, "seq/master_sequences/axi4_master_read_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Master Read Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_master_read_seq extends axi4_master_base_seq;
    
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
    
endclass : axi4_master_read_seq
""")
        
        # Slave base sequence
        with open(os.path.join(base_path, "seq/slave_sequences/axi4_slave_base_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Slave Base Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_slave_base_seq extends uvm_sequence #(axi4_slave_tx);
    
    `uvm_object_utils(axi4_slave_base_seq)
    
    // Constructor
    function new(string name = "axi4_slave_base_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        `uvm_info(get_type_name(), "Starting slave base sequence", UVM_MEDIUM)
    endtask : body
    
endclass : axi4_slave_base_seq
""")
    
    def _generate_virtual_components(self, base_path):
        """Generate virtual sequencer and sequence components"""
        # Virtual sequencer package (to avoid circular dependency)
        with open(os.path.join(base_path, "virtual_seqr/axi4_virtual_seqr_pkg.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Sequencer Package
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

package axi4_virtual_seqr_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_master_pkg::*;
    import axi4_slave_pkg::*;
    
    `include "axi4_virtual_sequencer.sv"
    
endpackage : axi4_virtual_seqr_pkg
""")
        
        # Virtual sequencer
        with open(os.path.join(base_path, "virtual_seqr/axi4_virtual_sequencer.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Sequencer
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_virtual_sequencer extends uvm_sequencer;
    
    `uvm_component_utils(axi4_virtual_sequencer)
    
    // Master sequencers
    axi4_master_sequencer master_seqr[{len(self.config.masters)}];
    
    // Slave sequencers
    axi4_slave_sequencer slave_seqr[{len(self.config.slaves)}];
    
    // Environment configuration handle (using uvm_object to avoid circular dependency)
    uvm_object env_cfg;
    
    // Constructor
    function new(string name = "axi4_virtual_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
endclass : axi4_virtual_sequencer
""")
        
        # Virtual sequence package
        with open(os.path.join(base_path, "virtual_seq/axi4_virtual_seq_pkg.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Sequence Package
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

package axi4_virtual_seq_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    import axi4_master_pkg::*;
    import axi4_slave_pkg::*;
    import axi4_master_seq_pkg::*;
    import axi4_slave_seq_pkg::*;
    import axi4_virtual_seqr_pkg::*;
    import axi4_env_pkg::*;
    
    // Include virtual sequence files (from current directory)
    `include "axi4_virtual_base_seq.sv"
    `include "axi4_virtual_write_seq.sv"
    `include "axi4_virtual_read_seq.sv"
    `include "axi4_virtual_write_read_seq.sv"
    `include "axi4_virtual_stress_seq.sv"
    `include "axi4_virtual_error_seq.sv"
    `include "axi4_virtual_performance_seq.sv"
    `include "axi4_virtual_interleaved_seq.sv"
    `include "axi4_virtual_boundary_seq.sv"
    
endpackage : axi4_virtual_seq_pkg
""")
        
        # Virtual base sequence
        with open(os.path.join(base_path, "virtual_seq/axi4_virtual_base_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Base Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_virtual_base_seq extends uvm_sequence;
    
    `uvm_object_utils(axi4_virtual_base_seq)
    
    // Public handle to access the virtual sequencer
    axi4_virtual_sequencer p_sequencer;
    
    // This task is called automatically before body()
    virtual task pre_start();
        super.pre_start();
        if(!$cast(p_sequencer, get_sequencer())) begin
            `uvm_error("CASTFL", $sformatf("Failed to cast sequencer to axi4_virtual_sequencer"))
        end
    endtask
    
    // Constructor
    function new(string name = "axi4_virtual_base_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        `uvm_info(get_type_name(), "Starting virtual base sequence", UVM_MEDIUM)
    endtask : body
    
endclass : axi4_virtual_base_seq
""")
        
        # Virtual write sequence
        with open(os.path.join(base_path, "virtual_seq/axi4_virtual_write_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Write Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_virtual_write_seq extends axi4_virtual_base_seq;
    
    `uvm_object_utils(axi4_virtual_write_seq)
    
    // Constructor
    function new(string name = "axi4_virtual_write_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_write_seq write_seq;
        
        `uvm_info(get_type_name(), "Starting virtual write sequence", UVM_MEDIUM)
        
        // Run write sequence on master 0
        write_seq = axi4_master_write_seq::type_id::create("write_seq");
        write_seq.start(p_sequencer.master_seqr[0]);
        
    endtask : body
    
endclass : axi4_virtual_write_seq
""")
        
        # Virtual read sequence
        with open(os.path.join(base_path, "virtual_seq/axi4_virtual_read_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Read Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_virtual_read_seq extends axi4_virtual_base_seq;
    
    `uvm_object_utils(axi4_virtual_read_seq)
    
    // Constructor
    function new(string name = "axi4_virtual_read_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_read_seq read_seq;
        
        `uvm_info(get_type_name(), "Starting virtual read sequence", UVM_MEDIUM)
        
        // Run read sequence on master 0
        read_seq = axi4_master_read_seq::type_id::create("read_seq");
        read_seq.start(p_sequencer.master_seqr[0]);
        
    endtask : body
    
endclass : axi4_virtual_read_seq
""")
        
        # Virtual write-read sequence
        with open(os.path.join(base_path, "virtual_seq/axi4_virtual_write_read_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Write-Read Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_virtual_write_read_seq extends axi4_virtual_base_seq;
    
    `uvm_object_utils(axi4_virtual_write_read_seq)
    
    // Constructor
    function new(string name = "axi4_virtual_write_read_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_virtual_write_seq write_seq;
        axi4_virtual_read_seq read_seq;
        
        `uvm_info(get_type_name(), "Starting virtual write-read sequence", UVM_MEDIUM)
        
        // Run write sequence
        write_seq = axi4_virtual_write_seq::type_id::create("write_seq");
        write_seq.start(p_sequencer);
        
        // Run read sequence
        read_seq = axi4_virtual_read_seq::type_id::create("read_seq");
        read_seq.start(p_sequencer);
        
    endtask : body
    
endclass : axi4_virtual_write_read_seq
""")
    
    def _generate_environment_files(self, base_path):
        """Generate environment files"""
        # First generate virtual sequencer and sequence packages
        self._generate_virtual_components(base_path)
        
        # Generate environment package
        with open(os.path.join(base_path, "env/axi4_env_pkg.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Environment Package
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

package axi4_env_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    import axi4_master_pkg::*;
    import axi4_slave_pkg::*;
    import axi4_virtual_seqr_pkg::*;
    
    // Include environment files
    `include "axi4_env_config.sv"
    `include "axi4_scoreboard.sv"
    `include "axi4_protocol_coverage.sv"
    `include "axi4_env.sv"
    
endpackage : axi4_env_pkg
""")
        
        # Environment configuration
        with open(os.path.join(base_path, "env/axi4_env_config.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Environment Configuration
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_env_config extends uvm_object;
    
    `uvm_object_utils(axi4_env_config)
    
    // Number of masters and slaves
    int no_of_masters = {len(self.config.masters)};
    int no_of_slaves = {len(self.config.slaves)};
    
    // Agent configurations
    axi4_master_agent_config master_cfg[{len(self.config.masters)}];
    axi4_slave_agent_config slave_cfg[{len(self.config.slaves)}];
    
    // Coverage enable
    bit has_coverage = 1;
    
    // Scoreboard enable
    bit has_scoreboard = 1;
    
    // Error injection configuration
    bit enable_error_injection = 0;
    real error_rate = 0.01; // 1% error rate
    
    // Constructor
    function new(string name = "axi4_env_config");
        super.new(name);
        
        // Create agent configurations
        foreach(master_cfg[i]) begin
            master_cfg[i] = axi4_master_agent_config::type_id::create($sformatf("master_cfg[%0d]", i));
        end
        
        foreach(slave_cfg[i]) begin
            slave_cfg[i] = axi4_slave_agent_config::type_id::create($sformatf("slave_cfg[%0d]", i));
        end
    endfunction
    
endclass : axi4_env_config
""")
        
        # Environment class
        with open(os.path.join(base_path, "env/axi4_env.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Environment
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_env extends uvm_env;
    
    `uvm_component_utils(axi4_env)
    
    // Environment configuration
    axi4_env_config env_cfg;
    
    // Master agents
    axi4_master_agent master_agent[{len(self.config.masters)}];
    
    // Slave agents
    axi4_slave_agent slave_agent[{len(self.config.slaves)}];
    
    // Virtual sequencer
    axi4_virtual_sequencer v_seqr;
    
    // Scoreboard
    axi4_scoreboard scoreboard;
    
    // Coverage
    axi4_protocol_coverage coverage;
    
    // Constructor
    function new(string name = "axi4_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Get configuration
        if(!uvm_config_db#(axi4_env_config)::get(this, "", "env_cfg", env_cfg))
            `uvm_fatal("CONFIG", "Cannot get env_cfg from uvm_config_db")
        
        // Set configurations before creating agents
        foreach(env_cfg.master_cfg[i]) begin
            uvm_config_db#(axi4_master_agent_config)::set(this, $sformatf("master_agent[%0d]*", i), "cfg", env_cfg.master_cfg[i]);
        end
        
        foreach(env_cfg.slave_cfg[i]) begin
            uvm_config_db#(axi4_slave_agent_config)::set(this, $sformatf("slave_agent[%0d]*", i), "cfg", env_cfg.slave_cfg[i]);
        end
        
        // Create agents
        foreach(master_agent[i]) begin
            master_agent[i] = axi4_master_agent::type_id::create($sformatf("master_agent[%0d]", i), this);
        end
        
        foreach(slave_agent[i]) begin
            slave_agent[i] = axi4_slave_agent::type_id::create($sformatf("slave_agent[%0d]", i), this);
        end
        
        // Create virtual sequencer
        v_seqr = axi4_virtual_sequencer::type_id::create("v_seqr", this);
        
        // Create scoreboard if enabled
        if(env_cfg.has_scoreboard) begin
            scoreboard = axi4_scoreboard::type_id::create("scoreboard", this);
        end
        
        // Create coverage if enabled
        if(env_cfg.has_coverage) begin
            coverage = axi4_protocol_coverage::type_id::create("coverage", this);
        end
    endfunction
    
    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Pass env_cfg to virtual sequencer
        v_seqr.env_cfg = env_cfg;
        
        // Connect sequencers to virtual sequencer
        foreach(master_agent[i]) begin
            v_seqr.master_seqr[i] = master_agent[i].sequencer;
        end
        
        foreach(slave_agent[i]) begin
            v_seqr.slave_seqr[i] = slave_agent[i].sequencer;
        end
        
        // Connect monitors to scoreboard
        if(env_cfg.has_scoreboard) begin
            foreach(master_agent[i]) begin
                master_agent[i].monitor.item_collected_port.connect(scoreboard.master_fifo[i].analysis_export);
            end
            
            foreach(slave_agent[i]) begin
                slave_agent[i].monitor.item_collected_port.connect(scoreboard.slave_fifo[i].analysis_export);
            end
        end
    endfunction
    
endclass : axi4_env
""")
        
        # Generate stub scoreboard
        with open(os.path.join(base_path, "env/axi4_scoreboard.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Scoreboard (Stub)
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_scoreboard extends uvm_scoreboard;
    
    `uvm_component_utils(axi4_scoreboard)
    
    // Analysis fifos for masters and slaves
    uvm_tlm_analysis_fifo #(axi4_master_tx) master_fifo[{len(self.config.masters)}];
    uvm_tlm_analysis_fifo #(axi4_slave_tx) slave_fifo[{len(self.config.slaves)}];
    
    // Constructor
    function new(string name = "axi4_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        foreach(master_fifo[i]) begin
            master_fifo[i] = new($sformatf("master_fifo[%0d]", i), this);
        end
        
        foreach(slave_fifo[i]) begin
            slave_fifo[i] = new($sformatf("slave_fifo[%0d]", i), this);
        end
    endfunction
    
endclass : axi4_scoreboard
""")
        
        # Generate stub protocol coverage
        with open(os.path.join(base_path, "env/axi4_protocol_coverage.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Protocol Coverage (Stub)
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_protocol_coverage extends uvm_component;
    
    `uvm_component_utils(axi4_protocol_coverage)
    
    // Constructor
    function new(string name = "axi4_protocol_coverage", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info(get_type_name(), "Protocol coverage build phase", UVM_MEDIUM)
    endfunction
    
endclass : axi4_protocol_coverage
""")
    
    def _generate_test_files(self, base_path):
        """Generate test files"""
        # Test package
        with open(os.path.join(base_path, "test/axi4_test_pkg.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Test Package
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

package axi4_test_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    import axi4_master_pkg::*;
    import axi4_slave_pkg::*;
    import axi4_master_seq_pkg::*;
    import axi4_slave_seq_pkg::*;
    import axi4_virtual_seq_pkg::*;
    import axi4_env_pkg::*;
    
    // Include test files
    `include "axi4_base_test.sv"
    `include "axi4_basic_rw_test.sv"
    `include "axi4_burst_test.sv"
    `include "axi4_random_test.sv"
    `include "axi4_stress_test.sv"
    `include "axi4_qos_test.sv"
    `include "axi4_error_injection_test.sv"
    `include "axi4_performance_test.sv"
    `include "axi4_interleaved_test.sv"
    `include "axi4_boundary_test.sv"
    
endpackage : axi4_test_pkg
""")
        
        # Base test
        with open(os.path.join(base_path, "test/axi4_base_test.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Base Test
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_base_test extends uvm_test;
    
    `uvm_component_utils(axi4_base_test)
    
    // Environment instance
    axi4_env env;
    
    // Environment configuration
    axi4_env_config env_cfg;
    
    // Constructor
    function new(string name = "axi4_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create environment configuration
        env_cfg = axi4_env_config::type_id::create("env_cfg");
        
        // Initialize master and slave configurations
        env_cfg.no_of_masters = {len(self.config.masters)};
        env_cfg.no_of_slaves = {len(self.config.slaves)};
        
        // Set configuration
        uvm_config_db#(axi4_env_config)::set(this, "env*", "env_cfg", env_cfg);
        
        // Create environment
        env = axi4_env::type_id::create("env", this);
    endfunction
    
    // Start of simulation phase - control waveform dumping
    function void start_of_simulation_phase(uvm_phase phase);
        super.start_of_simulation_phase(phase);
        
        // Check for waveform control
        if ($test$plusargs("enable_wave")) begin
            `uvm_info(get_type_name(), "Enabling waveform dump", UVM_LOW)
            // Use direct system tasks instead of hierarchical reference
            `ifdef DUMP_FSDB
                $fsdbDumpon();
            `elsif DUMP_VCD
                $dumpon();
            `endif
        end
        
        if ($test$plusargs("disable_wave")) begin
            `uvm_info(get_type_name(), "Disabling waveform dump", UVM_LOW)
            // Use direct system tasks instead of hierarchical reference
            `ifdef DUMP_FSDB
                $fsdbDumpoff();
            `elsif DUMP_VCD
                $dumpoff();
            `endif
        end
    endfunction
    
    // End of elaboration phase
    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        uvm_top.print_topology();
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        `uvm_info(get_type_name(), "Starting base test", UVM_LOW)
        
        // Add test logic here
        #100ns;
        
        `uvm_info(get_type_name(), "Ending base test", UVM_LOW)
        phase.drop_objection(this);
    endtask
    
endclass : axi4_base_test
""")
        
        # Basic read/write test
        with open(os.path.join(base_path, "test/axi4_basic_rw_test.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Basic Read/Write Test
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_basic_rw_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_basic_rw_test)
    
    // Virtual sequence
    axi4_virtual_write_read_seq vseq;
    
    // Constructor
    function new(string name = "axi4_basic_rw_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting basic read/write test", UVM_LOW)
        
        // Create and start virtual sequence
        vseq = axi4_virtual_write_read_seq::type_id::create("vseq");
        vseq.start(env.v_seqr);
        
        `uvm_info(get_type_name(), "Completed basic read/write test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_basic_rw_test
""")
        
        # Burst test
        with open(os.path.join(base_path, "test/axi4_burst_test.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Burst Test
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_burst_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_burst_test)
    
    // Constructor
    function new(string name = "axi4_burst_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_master_burst_seq burst_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting burst test", UVM_LOW)
        
        // Test different burst types and lengths
        burst_seq = axi4_master_burst_seq::type_id::create("burst_seq");
        burst_seq.burst_type = axi4_globals_pkg::INCR;
        burst_seq.burst_length = 16;
        burst_seq.start(env.master_agent[0].sequencer);
        
        #100ns;
        
        // WRAP burst
        burst_seq.burst_type = axi4_globals_pkg::WRAP;
        burst_seq.burst_length = 8;
        burst_seq.start(env.master_agent[0].sequencer);
        
        `uvm_info(get_type_name(), "Completed burst test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_burst_test
""")
        
        # Random test
        with open(os.path.join(base_path, "test/axi4_random_test.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Random Test
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_random_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_random_test)
    
    // Constructor
    function new(string name = "axi4_random_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_master_random_seq random_seq;
        int num_transactions = 100;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), $sformatf("Starting random test with %0d transactions", num_transactions), UVM_LOW)
        
        // Run random sequences on all masters
        fork
            begin
                random_seq = axi4_master_random_seq::type_id::create("random_seq0");
                random_seq.num_trans = num_transactions;
                random_seq.start(env.master_agent[0].sequencer);
            end
            begin
                random_seq = axi4_master_random_seq::type_id::create("random_seq1");
                random_seq.num_trans = num_transactions;
                random_seq.start(env.master_agent[1].sequencer);
            end
        join
        
        `uvm_info(get_type_name(), "Completed random test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_random_test
""")
        
        # Stress test
        with open(os.path.join(base_path, "test/axi4_stress_test.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Stress Test
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_stress_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_stress_test)
    
    // Constructor
    function new(string name = "axi4_stress_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_virtual_stress_seq stress_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting stress test", UVM_LOW)
        
        // Run stress sequence with heavy traffic
        stress_seq = axi4_virtual_stress_seq::type_id::create("stress_seq");
        stress_seq.num_iterations = 500;
        stress_seq.enable_backpressure = 1;
        stress_seq.start(env.v_seqr);
        
        `uvm_info(get_type_name(), "Completed stress test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_stress_test
""")
        
        # QoS test
        with open(os.path.join(base_path, "test/axi4_qos_test.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 QoS Test
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_qos_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_qos_test)
    
    // Constructor
    function new(string name = "axi4_qos_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_master_qos_seq qos_seq_high, qos_seq_low;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting QoS test", UVM_LOW)
        
        // Test QoS arbitration with different priorities
        fork
            begin
                qos_seq_high = axi4_master_qos_seq::type_id::create("qos_seq_high");
                qos_seq_high.qos_value = 4'hF; // Highest priority
                qos_seq_high.num_trans = 10;
                qos_seq_high.start(env.master_agent[0].sequencer);
            end
            begin
                qos_seq_low = axi4_master_qos_seq::type_id::create("qos_seq_low");
                qos_seq_low.qos_value = 4'h0; // Lowest priority
                qos_seq_low.num_trans = 10;
                qos_seq_low.start(env.master_agent[1].sequencer);
            end
        join
        
        `uvm_info(get_type_name(), "Completed QoS test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_qos_test
""")
        
        # Error injection test
        with open(os.path.join(base_path, "test/axi4_error_injection_test.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Error Injection Test
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_error_injection_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_error_injection_test)
    
    // Constructor
    function new(string name = "axi4_error_injection_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Enable error injection in environment
        env_cfg.enable_error_injection = 1;
        env_cfg.error_rate = 5; // 5% error rate
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_virtual_error_seq error_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting error injection test", UVM_LOW)
        
        // Run sequence with error scenarios
        error_seq = axi4_virtual_error_seq::type_id::create("error_seq");
        error_seq.test_slave_errors = 1;
        error_seq.test_decode_errors = 1;
        error_seq.test_exclusive_errors = 1;
        error_seq.start(env.v_seqr);
        
        `uvm_info(get_type_name(), "Completed error injection test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_error_injection_test
""")
        
        # Performance test
        with open(os.path.join(base_path, "test/axi4_performance_test.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Performance Test
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_performance_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_performance_test)
    
    // Performance metrics
    int total_transactions;
    real start_time, end_time;
    real throughput;
    
    // Constructor
    function new(string name = "axi4_performance_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_virtual_performance_seq perf_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting performance test", UVM_LOW)
        
        start_time = $realtime;
        
        // Run performance sequence
        perf_seq = axi4_virtual_performance_seq::type_id::create("perf_seq");
        perf_seq.num_iterations = 1000;
        perf_seq.measure_latency = 1;
        perf_seq.start(env.v_seqr);
        
        end_time = $realtime;
        total_transactions = perf_seq.num_iterations * 2; // Read + Write
        throughput = total_transactions / ((end_time - start_time) / 1ns);
        
        `uvm_info(get_type_name(), $sformatf("Performance: %0.2f transactions/ns", throughput), UVM_LOW)
        `uvm_info(get_type_name(), "Completed performance test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_performance_test
""")
        
        # Interleaved test
        with open(os.path.join(base_path, "test/axi4_interleaved_test.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Interleaved Test
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_interleaved_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_interleaved_test)
    
    // Constructor
    function new(string name = "axi4_interleaved_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_virtual_interleaved_seq interleaved_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting interleaved test", UVM_LOW)
        
        // Test interleaved transactions from multiple masters
        interleaved_seq = axi4_virtual_interleaved_seq::type_id::create("interleaved_seq");
        interleaved_seq.enable_data_interleaving = 1;
        interleaved_seq.num_outstanding = 8;
        interleaved_seq.start(env.v_seqr);
        
        `uvm_info(get_type_name(), "Completed interleaved test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_interleaved_test
""")
        
        # Boundary test
        with open(os.path.join(base_path, "test/axi4_boundary_test.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Boundary Test
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_boundary_test extends axi4_base_test;
    
    `uvm_component_utils(axi4_boundary_test)
    
    // Constructor
    function new(string name = "axi4_boundary_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        axi4_virtual_boundary_seq boundary_seq;
        
        phase.raise_objection(this);
        
        `uvm_info(get_type_name(), "Starting boundary test", UVM_LOW)
        
        // Test boundary conditions
        boundary_seq = axi4_virtual_boundary_seq::type_id::create("boundary_seq");
        boundary_seq.test_4k_boundary = 1;
        boundary_seq.test_slave_boundary = 1;
        boundary_seq.test_max_burst = 1;
        boundary_seq.start(env.v_seqr);
        
        `uvm_info(get_type_name(), "Completed boundary test", UVM_LOW)
        
        phase.drop_objection(this);
    endtask
    
endclass : axi4_boundary_test
""")
        
        # Also need to generate the corresponding sequences
        self._generate_additional_sequences(base_path)
    
    def _generate_additional_sequences(self, base_path):
        """Generate additional sequence files for advanced tests"""
        # Burst sequence
        with open(os.path.join(base_path, "seq/master_sequences/axi4_master_burst_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Master Burst Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_master_burst_seq extends axi4_master_base_seq;
    
    `uvm_object_utils(axi4_master_burst_seq)
    
    // Burst parameters
    rand axi4_burst_type_e burst_type;
    rand int burst_length;
    
    constraint burst_length_c {{
        burst_length inside {{1, 2, 4, 8, 16, 32, 64, 128, 256}};
    }}
    
    // Constructor
    function new(string name = "axi4_master_burst_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_tx tx;
        
        `uvm_do_with(tx, {{
            tx.tx_type == axi4_master_tx::WRITE;
            tx.awburst == burst_type;
            tx.awlen == burst_length - 1;
            tx.awsize == axi4_globals_pkg::SIZE_4B;
        }})
    endtask : body
    
endclass : axi4_master_burst_seq
""")
        
        # Random sequence
        with open(os.path.join(base_path, "seq/master_sequences/axi4_master_random_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Master Random Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_master_random_seq extends axi4_master_base_seq;
    
    `uvm_object_utils(axi4_master_random_seq)
    
    // Constructor
    function new(string name = "axi4_master_random_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_tx tx;
        
        repeat(num_trans) begin
            `uvm_do(tx)
        end
    endtask : body
    
endclass : axi4_master_random_seq
""")
        
        # QoS sequence
        with open(os.path.join(base_path, "seq/master_sequences/axi4_master_qos_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Master QoS Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_master_qos_seq extends axi4_master_base_seq;
    
    `uvm_object_utils(axi4_master_qos_seq)
    
    // QoS value
    rand bit [3:0] qos_value;
    
    // Constructor
    function new(string name = "axi4_master_qos_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_tx tx;
        
        repeat(num_trans) begin
            `uvm_do_with(tx, {{
                tx.awqos == qos_value;
                tx.arqos == qos_value;
            }})
        end
    endtask : body
    
endclass : axi4_master_qos_seq
""")
        
        # Virtual stress sequence
        with open(os.path.join(base_path, "virtual_seq/axi4_virtual_stress_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Stress Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_virtual_stress_seq extends axi4_virtual_base_seq;
    
    `uvm_object_utils(axi4_virtual_stress_seq)
    
    // Parameters
    int num_iterations = 100;
    bit enable_backpressure = 0;
    
    // Constructor
    function new(string name = "axi4_virtual_stress_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_random_seq random_seq[{len(self.config.masters)}];
        
        `uvm_info(get_type_name(), "Starting virtual stress sequence", UVM_MEDIUM)
        
        // Start random sequences on all masters concurrently
        fork
""")
            for i in range(len(self.config.masters)):
                f.write(f"""            begin
                random_seq[{i}] = axi4_master_random_seq::type_id::create($sformatf("random_seq_%0d", {i}));
                random_seq[{i}].num_trans = num_iterations;
                random_seq[{i}].start(p_sequencer.master_seqr[{i}]);
            end
""")
            f.write("""        join
    endtask : body
    
endclass : axi4_virtual_stress_seq
""")
        
        # Virtual error sequence
        with open(os.path.join(base_path, "virtual_seq/axi4_virtual_error_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Error Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_virtual_error_seq extends axi4_virtual_base_seq;
    
    `uvm_object_utils(axi4_virtual_error_seq)
    
    // Error scenarios to test
    bit test_slave_errors = 1;
    bit test_decode_errors = 1;
    bit test_exclusive_errors = 1;
    
    // Constructor
    function new(string name = "axi4_virtual_error_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        `uvm_info(get_type_name(), "Starting virtual error sequence", UVM_MEDIUM)
        
        // Test different error scenarios
        if (test_decode_errors) begin
            // Access unmapped address
            test_decode_error();
        end
        
        if (test_slave_errors) begin
            // Force slave errors
            test_slave_error_response();
        end
        
        if (test_exclusive_errors) begin
            // Test exclusive access failures
            test_exclusive_access_error();
        end
    endtask : body
    
    // Test decode error
    task test_decode_error();
        axi4_master_tx tx;
        
        `uvm_info(get_type_name(), "Testing decode error", UVM_MEDIUM)
        
        `uvm_do_on_with(tx, p_sequencer.master_seqr[0], {{
            tx.tx_type == axi4_master_tx::WRITE;
            tx.awaddr == 'hDEADBEEF; // Unmapped address
        }})
    endtask
    
    // Test slave error response
    task test_slave_error_response();
        // Configure slave to return errors
        `uvm_info(get_type_name(), "Testing slave error response", UVM_MEDIUM)
        // Implementation depends on slave configuration
    endtask
    
    // Test exclusive access error
    task test_exclusive_access_error();
        `uvm_info(get_type_name(), "Testing exclusive access error", UVM_MEDIUM)
        // Implementation for exclusive access testing
    endtask
    
endclass : axi4_virtual_error_seq
""")
        
        # Virtual performance sequence
        with open(os.path.join(base_path, "virtual_seq/axi4_virtual_performance_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Performance Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_virtual_performance_seq extends axi4_virtual_base_seq;
    
    `uvm_object_utils(axi4_virtual_performance_seq)
    
    // Parameters
    int num_iterations = 100;
    bit measure_latency = 0;
    real total_latency = 0;
    int latency_count = 0;
    
    // Constructor
    function new(string name = "axi4_virtual_performance_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        axi4_master_write_seq write_seq;
        axi4_master_read_seq read_seq;
        real start_time, end_time;
        
        `uvm_info(get_type_name(), "Starting virtual performance sequence", UVM_MEDIUM)
        
        repeat(num_iterations) begin
            if (measure_latency) start_time = $realtime;
            
            // Write
            write_seq = axi4_master_write_seq::type_id::create("write_seq");
            write_seq.start(p_sequencer.master_seqr[0]);
            
            // Read
            read_seq = axi4_master_read_seq::type_id::create("read_seq");
            read_seq.start(p_sequencer.master_seqr[0]);
            
            if (measure_latency) begin
                end_time = $realtime;
                total_latency += (end_time - start_time);
                latency_count++;
            end
        end
        
        if (measure_latency && latency_count > 0) begin
            `uvm_info(get_type_name(), $sformatf("Average latency: %0.2f ns", total_latency/latency_count/1ns), UVM_LOW)
        end
    endtask : body
    
endclass : axi4_virtual_performance_seq
""")
        
        # Virtual interleaved sequence
        with open(os.path.join(base_path, "virtual_seq/axi4_virtual_interleaved_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Interleaved Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_virtual_interleaved_seq extends axi4_virtual_base_seq;
    
    `uvm_object_utils(axi4_virtual_interleaved_seq)
    
    // Parameters
    bit enable_data_interleaving = 1;
    int num_outstanding = 4;
    
    // Constructor
    function new(string name = "axi4_virtual_interleaved_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        `uvm_info(get_type_name(), "Starting virtual interleaved sequence", UVM_MEDIUM)
        
        // Start multiple outstanding transactions
        fork
            repeat(num_outstanding) begin
                fork
                    send_interleaved_write();
                    send_interleaved_read();
                join_none
            end
        join
    endtask : body
    
    // Send interleaved write
    task send_interleaved_write();
        axi4_master_burst_seq burst_seq;
        
        burst_seq = axi4_master_burst_seq::type_id::create("burst_seq");
        burst_seq.burst_type = axi4_globals_pkg::INCR;
        burst_seq.burst_length = 8;
        burst_seq.start(p_sequencer.master_seqr[$urandom_range({len(self.config.masters)}-1, 0)]);
    endtask
    
    // Send interleaved read
    task send_interleaved_read();
        axi4_master_burst_seq burst_seq;
        
        burst_seq = axi4_master_burst_seq::type_id::create("burst_seq");
        burst_seq.burst_type = axi4_globals_pkg::INCR;
        burst_seq.burst_length = 8;
        burst_seq.start(p_sequencer.master_seqr[$urandom_range({len(self.config.masters)}-1, 0)]);
    endtask
    
endclass : axi4_virtual_interleaved_seq
""")
        
        # Virtual boundary sequence
        with open(os.path.join(base_path, "virtual_seq/axi4_virtual_boundary_seq.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Boundary Sequence
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

class axi4_virtual_boundary_seq extends axi4_virtual_base_seq;
    
    `uvm_object_utils(axi4_virtual_boundary_seq)
    
    // Test options
    bit test_4k_boundary = 1;
    bit test_slave_boundary = 1;
    bit test_max_burst = 1;
    
    // Constructor
    function new(string name = "axi4_virtual_boundary_seq");
        super.new(name);
    endfunction
    
    // Body method
    virtual task body();
        `uvm_info(get_type_name(), "Starting virtual boundary sequence", UVM_MEDIUM)
        
        if (test_4k_boundary) begin
            test_4k_boundary_crossing();
        end
        
        if (test_slave_boundary) begin
            test_slave_address_boundary();
        end
        
        if (test_max_burst) begin
            test_maximum_burst_length();
        end
    endtask : body
    
    // Test 4K boundary crossing
    task test_4k_boundary_crossing();
        axi4_master_tx tx;
        
        `uvm_info(get_type_name(), "Testing 4K boundary crossing", UVM_MEDIUM)
        
        `uvm_do_on_with(tx, p_sequencer.master_seqr[0], {{
            tx.tx_type == axi4_master_tx::WRITE;
            tx.awaddr == 'h0FF0; // Near 4K boundary
            tx.awlen == 15; // 16 beats
            tx.awsize == axi4_globals_pkg::SIZE_4B;
            tx.awburst == axi4_globals_pkg::INCR;
        }})
    endtask
    
    // Test slave address boundary
    task test_slave_address_boundary();
        axi4_master_tx tx;
        axi4_env_config cfg;
        
        `uvm_info(get_type_name(), "Testing slave address boundary", UVM_MEDIUM)
        
        // Cast env_cfg to proper type
        if (!$cast(cfg, p_sequencer.env_cfg)) begin
            `uvm_error(get_type_name(), "Failed to cast env_cfg to axi4_env_config")
            return;
        end
        
        // Test access at slave boundaries
        foreach(cfg.slave_cfg[i]) begin
            `uvm_do_on_with(tx, p_sequencer.master_seqr[0], {{
                tx.tx_type == axi4_master_tx::READ;
                tx.araddr == cfg.slave_cfg[i].end_addr - 8;
                tx.arlen == 1;
                tx.arsize == axi4_globals_pkg::SIZE_8B;
            }})
        end
    endtask
    
    // Test maximum burst length
    task test_maximum_burst_length();
        axi4_master_tx tx;
        
        `uvm_info(get_type_name(), "Testing maximum burst length", UVM_MEDIUM)
        
        `uvm_do_on_with(tx, p_sequencer.master_seqr[0], {{
            tx.tx_type == axi4_master_tx::WRITE;
            tx.awlen == 255; // Maximum burst length for AXI4
            tx.awsize == axi4_globals_pkg::SIZE_4B;
            tx.awburst == axi4_globals_pkg::INCR;
        }})
    endtask
    
endclass : axi4_virtual_boundary_seq
""")
        
        # Update master sequence package to include new sequences
        self._update_master_seq_package(base_path)
        
        # Note: Virtual sequence package already includes all sequences in _generate_virtual_components()
        # No need to update it again
    
    def _generate_fsdb_documentation(self, base_path):
        """Generate FSDB documentation"""
        with open(os.path.join(base_path, "doc/FSDB_USAGE.md"), "w") as f:
            f.write(f"""# FSDB Waveform Dumping Guide

This VIP supports FSDB waveform dumping for debugging with Verdi.

## Quick Start

### 1. Run simulation with FSDB dumping:
```bash
make run_fsdb TEST=axi4_basic_rw_test
```

### 2. View waveform in Verdi:
```bash
make verdi
```

## Manual Control

### Enable FSDB dumping:
```bash
make run DUMP_FSDB=1
```

### Specify custom FSDB file:
```bash
make run DUMP_FSDB=1 FSDB_FILE=my_waves.fsdb
```

### Runtime control with plusargs:
```bash
./simv +fsdb_file=custom.fsdb +enable_wave
```

## Test Control

Tests can control waveform dumping:
- `+enable_wave` - Enable dumping at start
- `+disable_wave` - Disable dumping at start

## VCD Alternative

For environments without Verdi:
```bash
make run_vcd TEST=axi4_basic_rw_test
make dve  # View in DVE
```

## Compilation Requirements

1. Set VERDI_HOME environment variable:
```bash
export VERDI_HOME=/path/to/verdi/installation
```

2. Ensure Verdi PLI libraries are accessible

## Waveform Files

Generated waveforms are stored in:
- FSDB: `sim/waves/<TEST>_<SEED>.fsdb`
- VCD: `sim/waves/<TEST>_<SEED>.vcd`

## Selective Dumping

To reduce file size, you can:
1. Use `hdl_top.enable_wave_dump()` and `hdl_top.disable_wave_dump()` in tests
2. Modify the `$fsdbDumpvars` scope in hdl_top.sv
3. Use Verdi commands for selective dumping

## Troubleshooting

### FSDB not generated:
- Check VERDI_HOME is set correctly
- Verify +define+DUMP_FSDB is passed during compilation
- Check for PLI loading errors in simulation log

### Verdi won't open:
- Ensure Verdi is in PATH
- Check FSDB file exists in waves directory
- Verify FSDB file is not corrupted
""")
    
    def _update_master_seq_package(self, base_path):
        """Update master sequence package to include new sequences"""
        with open(os.path.join(base_path, "seq/master_sequences/axi4_master_seq_pkg.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Master Sequence Package
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

package axi4_master_seq_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    import axi4_master_pkg::*;
    
    // Include sequence files
    `include "axi4_master_base_seq.sv"
    `include "axi4_master_write_seq.sv"
    `include "axi4_master_read_seq.sv"
    `include "axi4_master_burst_seq.sv"
    `include "axi4_master_random_seq.sv"
    `include "axi4_master_qos_seq.sv"
    
endpackage : axi4_master_seq_pkg
""")
    
    def _update_virtual_seq_package(self, base_path):
        """Update virtual sequence package to include new sequences"""
        with open(os.path.join(base_path, "virtual_seq/axi4_virtual_seq_pkg.sv"), "w") as f:
            f.write(f"""//==============================================================================
// AXI4 Virtual Sequence Package
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

package axi4_virtual_seq_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    import axi4_globals_pkg::*;
    import axi4_master_pkg::*;
    import axi4_slave_pkg::*;
    import axi4_master_seq_pkg::*;
    import axi4_slave_seq_pkg::*;
    import axi4_virtual_seqr_pkg::*;
    import axi4_env_pkg::*;
    
    // Include virtual sequence files
    `include "axi4_virtual_base_seq.sv"
    `include "axi4_virtual_write_seq.sv"
    `include "axi4_virtual_read_seq.sv"
    `include "axi4_virtual_write_read_seq.sv"
    `include "axi4_virtual_stress_seq.sv"
    `include "axi4_virtual_error_seq.sv"
    `include "axi4_virtual_performance_seq.sv"
    `include "axi4_virtual_interleaved_seq.sv"
    `include "axi4_virtual_boundary_seq.sv"
    
endpackage : axi4_virtual_seq_pkg
""")
    
    def _generate_top_files(self, base_path):
        """Generate top-level files"""
        # HDL top
        with open(os.path.join(base_path, "top/hdl_top.sv"), "w") as f:
            f.write(f"""//==============================================================================
// HDL Top Module
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

module hdl_top;
    
    import axi4_globals_pkg::*;
    import uvm_pkg::*;
    
    // Clock and reset
    logic aclk;
    logic aresetn;
    
    // Clock generation
    initial begin
        aclk = 0;
        forever #5ns aclk = ~aclk;
    end
    
    // Reset generation
    initial begin
        aresetn = 0;
        repeat(10) @(posedge aclk);
        aresetn = 1;
    end
    
    // AXI4 interfaces
    axi4_if axi_if[NO_OF_MASTERS](aclk, aresetn);
    
    // Master agent BFMs
    axi4_master_agent_bfm master_bfm[NO_OF_MASTERS](aclk, aresetn);
    
    // Slave agent BFMs
    axi4_slave_agent_bfm slave_bfm[NO_OF_SLAVES](aclk, aresetn);
    
    // FSDB dumping
    `ifdef DUMP_FSDB
    initial begin
        $display("[%0t] Starting FSDB dump", $time);
        $fsdbDumpfile("axi4_vip.fsdb");
        $fsdbDumpvars(0, hdl_top, "+all");
        $fsdbDumpSVA();
        $fsdbDumpMDA();
        $fsdbDumpon();
    end
    `endif
    
    // VCD dumping (alternative)
    `ifdef DUMP_VCD
    initial begin
        $display("[%0t] Starting VCD dump", $time);
        $dumpfile("axi4_vip.vcd");
        $dumpvars(0, hdl_top);
        $dumpon();
    end
    `endif
    
    // Waveform control tasks
    task enable_wave_dump();
        `ifdef DUMP_FSDB
            $fsdbDumpon();
            $display("[%0t] FSDB dumping enabled", $time);
        `elsif DUMP_VCD
            $dumpon();
            $display("[%0t] VCD dumping enabled", $time);
        `else
            $display("[%0t] No waveform dumping configured. Use +define+DUMP_FSDB or +define+DUMP_VCD", $time);
        `endif
    endtask
    
    task disable_wave_dump();
        `ifdef DUMP_FSDB
            $fsdbDumpoff();
            $display("[%0t] FSDB dumping disabled", $time);
        `elsif DUMP_VCD
            $dumpoff();
            $display("[%0t] VCD dumping disabled", $time);
        `endif
    endtask
    
    // Dump control from plusargs
    initial begin
        string dump_file;
        if ($value$plusargs("fsdb_file=%s", dump_file)) begin
            `ifdef DUMP_FSDB
                $fsdbDumpfile(dump_file);
                $display("[%0t] FSDB file set to: %s", $time, dump_file);
            `endif
        end
    end
    
""")
            if self.mode == "rtl_integration":
                f.write("""    // RTL DUT instance
    dut_wrapper #(
        .ADDR_WIDTH(ADDRESS_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH)
    ) dut (
        .clk(aclk),
        .rst_n(aresetn),
        .axi_if(axi_if[0])  // Connect to first master interface
    );
    
    // Additional waveform dumping for DUT internals
    `ifdef DUMP_FSDB
    initial begin
        #1;  // Wait for DUT instantiation
        $fsdbDumpvars(0, dut, "+all");
        $display("[%0t] Added DUT internal signals to FSDB dump", $time);
    end
    `endif
    
    `ifdef DUMP_VCD  
    initial begin
        #1;  // Wait for DUT instantiation
        $dumpvars(0, dut);
        $display("[%0t] Added DUT internal signals to VCD dump", $time);
    end
    `endif
    
""")
            else:
                f.write("""    // Direct connection for standalone mode
    // Connect masters to slaves through interconnect logic
    
""")
            
            f.write("""endmodule : hdl_top
""")
        
        # HVL top
        with open(os.path.join(base_path, "top/hvl_top.sv"), "w") as f:
            f.write(f"""//==============================================================================
// HVL Top Module
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
//==============================================================================

module hvl_top;
    
    import uvm_pkg::*;
    import axi4_test_pkg::*;
    
    initial begin
        // Run UVM test
        run_test();
    end
    
endmodule : hvl_top
""")
    
    def _generate_simulation_files(self, base_path):
        """Generate simulation scripts and makefiles"""
        # Generate FSDB documentation
        self._generate_fsdb_documentation(base_path)
        
        # Main Makefile
        with open(os.path.join(base_path, "sim/Makefile"), "w") as f:
            f.write(f"""#==============================================================================
# Makefile for AXI4 VIP Simulation
# Generated by AMBA Bus Matrix Configuration Tool
# Date: {self.timestamp}
#==============================================================================

# Default simulator
SIM ?= {self.simulator}

# Test name
TEST ?= axi4_base_test

# Random seed
SEED ?= 1

# Directories
VIP_ROOT = ..
SIM_DIR = .
SCRIPT_DIR = $(SIM_DIR)/scripts
LOG_DIR = $(SIM_DIR)/logs
WAVE_DIR = $(SIM_DIR)/waves
COV_DIR = $(SIM_DIR)/coverage

# Export VIP_ROOT for use in compile file
export VIP_ROOT

# Create directories
$(shell mkdir -p $(LOG_DIR) $(WAVE_DIR) $(COV_DIR))

# Common compile options
COMMON_OPTS = +define+UVM_NO_DEPRECATED +define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR

# Waveform dump options
DUMP_FSDB ?= 0
DUMP_VCD ?= 0
FSDB_FILE ?= $(WAVE_DIR)/$(TEST)_$(SEED).fsdb
VCD_FILE ?= $(WAVE_DIR)/$(TEST)_$(SEED).vcd

# Add waveform defines
ifeq ($(DUMP_FSDB), 1)
    COMMON_OPTS += +define+DUMP_FSDB
    VERDI_HOME ?= /home/eda_tools/synopsys/verdi/W-2024.09-SP1
    VCS_COMP_OPTS += -P $(VERDI_HOME)/share/PLI/VCS/LINUX64/novas.tab $(VERDI_HOME)/share/PLI/VCS/LINUX64/pli.a
endif

ifeq ($(DUMP_VCD), 1)
    COMMON_OPTS += +define+DUMP_VCD
endif

# VCS options
VCS_COMP_OPTS = -full64 -sverilog -ntb_opts uvm-1.2 -timescale=1ns/1ps
VCS_COMP_OPTS += -debug_access+all +vcs+lic+wait -lca -kdb
VCS_COMP_OPTS += +lint=PCWM
VCS_COMP_OPTS += $(COMMON_OPTS)

VCS_RUN_OPTS = +UVM_TESTNAME=$(TEST) +UVM_VERBOSITY=UVM_MEDIUM
VCS_RUN_OPTS += +ntb_random_seed=$(SEED)

# Add FSDB runtime options
ifeq ($(DUMP_FSDB), 1)
    VCS_RUN_OPTS += +fsdb_file=$(FSDB_FILE)
endif

# Questa options
QUESTA_COMP_OPTS = -64 -sv -mfcu -cuname design_cuname
QUESTA_COMP_OPTS += +define+QUESTA
QUESTA_COMP_OPTS += $(COMMON_OPTS)

QUESTA_RUN_OPTS = +UVM_TESTNAME=$(TEST) +UVM_VERBOSITY=UVM_MEDIUM
QUESTA_RUN_OPTS += -sv_seed $(SEED)

# Targets
.PHONY: all compile run clean

all: run

compile:
ifeq ($(SIM), vcs)
\tVIP_ROOT=$(VIP_ROOT) vcs $(VCS_COMP_OPTS) -f $(VIP_ROOT)/sim/axi4_compile.f -l $(LOG_DIR)/compile.log
else ifeq ($(SIM), questa)
\tVIP_ROOT=$(VIP_ROOT) vlog $(QUESTA_COMP_OPTS) -f $(VIP_ROOT)/sim/axi4_compile.f -l $(LOG_DIR)/compile.log
endif

run: compile
ifeq ($(SIM), vcs)
\t./simv $(VCS_RUN_OPTS) -l $(LOG_DIR)/$(TEST)_$(SEED).log
else ifeq ($(SIM), questa)
\tvsim -c design_cuname.hvl_top design_cuname.hdl_top $(QUESTA_RUN_OPTS) -do "run -all; quit" -l $(LOG_DIR)/$(TEST)_$(SEED).log
endif

# Run with FSDB dumping
run_fsdb:
\t$(MAKE) run DUMP_FSDB=1
\t@echo "FSDB file generated: $(FSDB_FILE)"

# Run with VCD dumping
run_vcd:
\t$(MAKE) run DUMP_VCD=1
\t@echo "VCD file generated: $(VCD_FILE)"

# Open waveform in Verdi with auto-load last run
verdi:
\t@echo "Auto-loading last run in Verdi..."
\t@# Find the most recent FSDB file
\t@LAST_FSDB=$$(ls -t $(WAVE_DIR)/*.fsdb 2>/dev/null | head -1); \
\tif [ -z "$$LAST_FSDB" ]; then \
\t\techo "No FSDB files found. Run 'make run_fsdb' first."; \
\t\texit 1; \
\tfi; \
\techo "Loading FSDB: $$LAST_FSDB"; \
\techo "Loading KDB: ./simv.daidir/kdb"; \
\tverdi -ssf $$LAST_FSDB -elab ./simv.daidir/kdb -nologo &

# Open waveform in DVE
dve:
\tdve -vpd $(VCD_FILE) &

clean:
\trm -rf csrc simv* *.log ucli.key
\trm -rf work transcript vsim.wlf
\trm -rf $(LOG_DIR)/* $(WAVE_DIR)/* $(COV_DIR)/*

help:
\t@echo "Usage: make [target] [options]"
\t@echo "Targets:"
\t@echo "  compile    - Compile the design"
\t@echo "  run        - Compile and run simulation"
\t@echo "  run_fsdb   - Run with FSDB dumping enabled"
\t@echo "  run_vcd    - Run with VCD dumping enabled"
\t@echo "  verdi      - Open FSDB in Verdi"
\t@echo "  dve        - Open VCD in DVE"
\t@echo "  clean      - Clean simulation files"
\t@echo "Options:"
\t@echo "  SIM={self.simulator}      - Simulator (vcs, questa)"
\t@echo "  TEST=test_name    - Test to run"
\t@echo "  SEED=value        - Random seed"
\t@echo "  DUMP_FSDB=1       - Enable FSDB dumping"
\t@echo "  DUMP_VCD=1        - Enable VCD dumping"
\t@echo "  FSDB_FILE=path    - FSDB output file"
\t@echo "  VCD_FILE=path     - VCD output file"
""")
        
        # Compile filelist
        with open(os.path.join(base_path, "sim/axi4_compile.f"), "w") as f:
            f.write(f"""#==============================================================================
# Compile File List
# Generated by AMBA Bus Matrix Configuration Tool
# Date: {self.timestamp}
#==============================================================================

# Include directories
+incdir+${{VIP_ROOT}}/include
+incdir+${{VIP_ROOT}}/intf
+incdir+${{VIP_ROOT}}/master
+incdir+${{VIP_ROOT}}/slave
+incdir+${{VIP_ROOT}}/seq/master_sequences
+incdir+${{VIP_ROOT}}/seq/slave_sequences
+incdir+${{VIP_ROOT}}/virtual_seq
+incdir+${{VIP_ROOT}}/virtual_seqr
+incdir+${{VIP_ROOT}}/env
+incdir+${{VIP_ROOT}}/test

# Package files (order matters)
${{VIP_ROOT}}/pkg/axi4_globals_pkg.sv

# Interface
${{VIP_ROOT}}/intf/axi4_interface/axi4_if.sv

# BFM stub interfaces (must be compiled before agent BFMs)
${{VIP_ROOT}}/agent/master_agent_bfm/axi4_master_driver_bfm.sv
${{VIP_ROOT}}/agent/master_agent_bfm/axi4_master_monitor_bfm.sv
${{VIP_ROOT}}/agent/slave_agent_bfm/axi4_slave_driver_bfm.sv
${{VIP_ROOT}}/agent/slave_agent_bfm/axi4_slave_monitor_bfm.sv

# Agent BFMs
${{VIP_ROOT}}/agent/master_agent_bfm/axi4_master_agent_bfm.sv
${{VIP_ROOT}}/agent/slave_agent_bfm/axi4_slave_agent_bfm.sv

# Master package and components
${{VIP_ROOT}}/master/axi4_master_pkg.sv

# Slave package and components
${{VIP_ROOT}}/slave/axi4_slave_pkg.sv

# Sequence packages
${{VIP_ROOT}}/seq/master_sequences/axi4_master_seq_pkg.sv
${{VIP_ROOT}}/seq/slave_sequences/axi4_slave_seq_pkg.sv

# Virtual sequencer package (after master/slave packages)
${{VIP_ROOT}}/virtual_seqr/axi4_virtual_seqr_pkg.sv

# Environment package (includes all env components via `include)
${{VIP_ROOT}}/env/axi4_env_pkg.sv

# Virtual sequence package (must be after env_pkg)
${{VIP_ROOT}}/virtual_seq/axi4_virtual_seq_pkg.sv

# Test package (includes all tests via `include)
${{VIP_ROOT}}/test/axi4_test_pkg.sv

""")
            if self.mode == "rtl_integration":
                f.write("""# RTL wrapper
${VIP_ROOT}/rtl_wrapper/dut_wrapper.sv

# Generated RTL (if applicable)
-f ${VIP_ROOT}/rtl_wrapper/rtl_files.f

""")
            f.write("""# Top modules
${VIP_ROOT}/top/hdl_top.sv
${VIP_ROOT}/top/hvl_top.sv
""")
    
    def _generate_verdi_integration(self, base_path):
        """Generate Verdi integration features"""
        from verdi_integration import VerdiIntegration
        
        verdi = VerdiIntegration()
        verdi.generate_verdi_scripts(base_path)
        verdi.generate_verdi_config(base_path)
        
    def _generate_documentation(self, base_path):
        """Generate documentation"""
        # README
        with open(os.path.join(base_path, "doc/README.md"), "w") as f:
            f.write(f"""# AXI4 VIP Environment

Generated by AMBA Bus Matrix Configuration Tool  
Date: {self.timestamp}

## Overview

This is a complete UVM-based AXI4 Verification IP environment following the tim_axi4_vip structure.

### Configuration
- Mode: {self.mode.replace('_', ' ').title()}
- Masters: {len(self.config.masters)}
- Slaves: {len(self.config.slaves)}
- Data Width: {self.config.data_width} bits
- Address Width: {self.config.addr_width} bits
{self._format_warnings()}
### Directory Structure
```
├── agent/              # BFM agents
├── assertions/         # Protocol assertions
├── doc/                # Documentation
├── env/                # Environment components
├── include/            # Common includes
├── intf/               # Interface definitions
├── master/             # Master agent components
├── pkg/                # Package definitions
├── seq/                # Sequences
├── sim/                # Simulation scripts
├── slave/              # Slave agent components
├── test/               # Test cases
├── top/                # Top-level modules
├── virtual_seq/        # Virtual sequences
└── virtual_seqr/       # Virtual sequencer
```

## Quick Start

### 1. Compile and Run
```bash
cd sim
make run TEST=axi4_base_test
```

### 2. Run with Different Simulator
```bash
make run SIM=questa TEST=axi4_basic_rw_test
```

### 3. Run with Random Seed
```bash
make run TEST=axi4_basic_rw_test SEED=12345
```

## Available Tests

- `axi4_base_test` - Basic infrastructure test
- `axi4_basic_rw_test` - Simple read/write test

## Master Configuration
""")
            for i, master in enumerate(self.config.masters):
                f.write(f"""
### Master {i}: {master.name}
- ID Width: {master.id_width}
- QoS Support: {master.qos_support}
- Exclusive Support: {master.exclusive_support}
""")
            
            f.write("\n## Slave Configuration\n")
            for i, slave in enumerate(self.config.slaves):
                f.write(f"""
### Slave {i}: {slave.name}
- Base Address: 0x{slave.base_address:08X}
- Size: {slave.size} KB
- End Address: 0x{slave.get_end_address():08X}
""")
    
    def _generate_rtl_wrapper(self, base_path):
        """Generate RTL wrapper for integration mode"""
        if self.mode != "rtl_integration":
            return
            
        # Create wrapper following the enhanced multi-master/slave support
        wrapper_content = self._get_enhanced_rtl_wrapper()
        with open(os.path.join(base_path, "rtl_wrapper/dut_wrapper.sv"), "w") as f:
            f.write(wrapper_content)
            
        # Create RTL filelist - always create it to avoid file not found errors
        rtl_filelist_path = os.path.join(base_path, "rtl_wrapper/rtl_files.f")
        with open(rtl_filelist_path, "w") as f:
            # For RTL integration mode, include the necessary RTL files
            if self.mode == "rtl_integration":
                num_masters = len(self.config.masters)
                num_slaves = len(self.config.slaves)
                f.write(f"""# RTL files to include
# Generated RTL files for AXI4 interconnect ({num_masters} masters x {num_slaves} slaves)

# Core RTL modules
${{VIP_ROOT}}/rtl_wrapper/generated_rtl/axi4_address_decoder.v
${{VIP_ROOT}}/rtl_wrapper/generated_rtl/axi4_arbiter.v
${{VIP_ROOT}}/rtl_wrapper/generated_rtl/axi4_router.v
${{VIP_ROOT}}/rtl_wrapper/generated_rtl/axi4_interconnect_m{num_masters}s{num_slaves}.v""")
            else:
                f.write("""# RTL files to include
# Add your RTL files here or they will be auto-populated if using tool-generated RTL

# Example:
# ${VIP_ROOT}/rtl_wrapper/generated_rtl/axi4_interconnect.v
# ${VIP_ROOT}/rtl_wrapper/generated_rtl/axi4_address_decoder.v
# ${VIP_ROOT}/rtl_wrapper/generated_rtl/axi4_arbiter.v
# ${VIP_ROOT}/rtl_wrapper/generated_rtl/axi4_router.v

# Placeholder to avoid empty file issues
# Remove this comment when adding actual RTL files
""")
                
        # Copy RTL files if in rtl_integration mode
        if self.mode == "rtl_integration":
            rtl_dir = os.path.join(base_path, "rtl_wrapper/generated_rtl")
            os.makedirs(rtl_dir, exist_ok=True)
            
            # Note: In a real implementation, these RTL files would be generated
            # by the RTL generator. For now, we'll create placeholder message
            with open(os.path.join(rtl_dir, "README.txt"), "w") as f:
                f.write("""RTL files should be placed in this directory.

Required files:
- axi4_address_decoder.v
- axi4_arbiter.v  
- axi4_router.v
- axi4_interconnect_m{}s{}.v

These can be generated using the gen_amba_axi tool or 
copied from existing RTL sources.
""".format(len(self.config.masters), len(self.config.slaves)))
    
    def _get_enhanced_rtl_wrapper(self):
        """Get enhanced RTL wrapper with multi-master/slave support"""
        num_masters = len(self.config.masters)
        num_slaves = len(self.config.slaves)
        # Get maximum ID width from all masters (interconnect must support largest ID)
        if self.config.masters:
            id_widths = [master.id_width for master in self.config.masters]
            id_width = max(id_widths)
            # Add comment if masters have different ID widths
            if len(set(id_widths)) > 1:
                id_info = f"\n// Master ID widths: {', '.join([f'{master.name}={master.id_width}' for master in self.config.masters])}"
            else:
                id_info = ""
        else:
            id_width = 4
            id_info = ""
            
        # Get maximum USER width from all masters  
        if self.config.masters:
            user_widths = [master.user_width for master in self.config.masters]
            user_width = max(user_widths)
        else:
            user_width = 1
        
        # Calculate WIDTH_CID based on actual number of masters
        width_cid = max(1, (num_masters-1).bit_length()) if num_masters > 1 else 0
        
        return f"""//==============================================================================
// DUT Wrapper for RTL Integration
// Generated by AMBA Bus Matrix Configuration Tool
// Date: {self.timestamp}
// Supports {num_masters} masters and {num_slaves} slaves{id_info}
//==============================================================================

module dut_wrapper #(
    parameter ADDR_WIDTH = {self.config.addr_width},
    parameter DATA_WIDTH = {self.config.data_width},
    parameter ID_WIDTH   = {id_width},
    parameter WIDTH_CID  = {width_cid},  // $clog2({num_masters}) = {width_cid}
    parameter WIDTH_SID  = (WIDTH_CID + ID_WIDTH)  // Slave ID width = CID + original ID
    // Note: Slave ID signals use WIDTH_SID to accommodate master routing information
) (
    input  logic clk,
    input  logic rst_n,
    axi4_if.slave axi_if  // VIP connects as master to this slave interface
);

    // Internal signals for all masters
""" + self._generate_master_signals() + """
    
    // Internal signals for all slaves  
""" + self._generate_slave_signals() + f"""

    // Instantiate the generated interconnect
    axi4_interconnect_m{num_masters}s{num_slaves} #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH),
        .ID_WIDTH(ID_WIDTH)
    ) generated_interconnect (
        .aclk(clk),
        .aresetn(rst_n),
        
""" + self._generate_master_connections() + ("," if len(self.config.slaves) > 0 else "") + f"""
        
""" + self._generate_slave_connections() + f"""
    );
    
    // Connect VIP to Master 0
    assign m0_awid    = axi_if.awid;
    assign m0_awaddr  = axi_if.awaddr;
    assign m0_awlen   = axi_if.awlen;
    assign m0_awsize  = axi_if.awsize;
    assign m0_awburst = axi_if.awburst;
    assign m0_awlock  = axi_if.awlock;
    assign m0_awcache = axi_if.awcache;
    assign m0_awprot  = axi_if.awprot;
    assign m0_awqos   = 4'b0000;  // Default QoS
    assign m0_awvalid = axi_if.awvalid;
    assign axi_if.awready = m0_awready;
    
    assign m0_wdata  = axi_if.wdata;
    assign m0_wstrb  = axi_if.wstrb;
    assign m0_wlast  = axi_if.wlast;
    assign m0_wvalid = axi_if.wvalid;
    assign axi_if.wready = m0_wready;
    
    assign axi_if.bid    = m0_bid;
    assign axi_if.bresp  = m0_bresp;
    assign axi_if.bvalid = m0_bvalid;
    assign m0_bready = axi_if.bready;
    
    assign m0_arid    = axi_if.arid;
    assign m0_araddr  = axi_if.araddr;
    assign m0_arlen   = axi_if.arlen;
    assign m0_arsize  = axi_if.arsize;
    assign m0_arburst = axi_if.arburst;
    assign m0_arlock  = axi_if.arlock;
    assign m0_arcache = axi_if.arcache;
    assign m0_arprot  = axi_if.arprot;
    assign m0_arqos   = 4'b0000;  // Default QoS
    assign m0_arvalid = axi_if.arvalid;
    assign axi_if.arready = m0_arready;
    
    assign axi_if.rid    = m0_rid;
    assign axi_if.rdata  = m0_rdata;
    assign axi_if.rresp  = m0_rresp;
    assign axi_if.rlast  = m0_rlast;
    assign axi_if.rvalid = m0_rvalid;
    assign m0_rready = axi_if.rready;
    
""" + self._generate_master_termination() + """
    
""" + self._generate_slave_responses() + """

endmodule : dut_wrapper
"""
    
    def _generate_master_signals(self):
        """Generate signal declarations for all masters (without conditional signals)"""
        signals = []
        for i in range(len(self.config.masters)):
            signals.append(f"""    // Master {i} signals
    logic [ID_WIDTH-1:0]     m{i}_awid;
    logic [ADDR_WIDTH-1:0]   m{i}_awaddr;
    logic [7:0]              m{i}_awlen;
    logic [2:0]              m{i}_awsize;
    logic [1:0]              m{i}_awburst;
    logic                    m{i}_awlock;
    logic [3:0]              m{i}_awcache;
    logic [2:0]              m{i}_awprot;
    logic [3:0]              m{i}_awqos;
    logic                    m{i}_awvalid;
    logic                    m{i}_awready;
    
    logic [DATA_WIDTH-1:0]   m{i}_wdata;
    logic [DATA_WIDTH/8-1:0] m{i}_wstrb;
    logic                    m{i}_wlast;
    logic                    m{i}_wvalid;
    logic                    m{i}_wready;
    
    logic [ID_WIDTH-1:0]     m{i}_bid;
    logic [1:0]              m{i}_bresp;
    logic                    m{i}_bvalid;
    logic                    m{i}_bready;
    
    logic [ID_WIDTH-1:0]     m{i}_arid;
    logic [ADDR_WIDTH-1:0]   m{i}_araddr;
    logic [7:0]              m{i}_arlen;
    logic [2:0]              m{i}_arsize;
    logic [1:0]              m{i}_arburst;
    logic                    m{i}_arlock;
    logic [3:0]              m{i}_arcache;
    logic [2:0]              m{i}_arprot;
    logic [3:0]              m{i}_arqos;
    logic                    m{i}_arvalid;
    logic                    m{i}_arready;
    
    logic [ID_WIDTH-1:0]     m{i}_rid;
    logic [DATA_WIDTH-1:0]   m{i}_rdata;
    logic [1:0]              m{i}_rresp;
    logic                    m{i}_rlast;
    logic                    m{i}_rvalid;
    logic                    m{i}_rready;
""")
        return "\n".join(signals)
    
    def _generate_slave_signals(self):
        """Generate signal declarations for all slaves (without conditional signals)"""
        signals = []
        num_masters = len(self.config.masters)
        # Calculate slave ID width: ID_WIDTH + $clog2(num_masters)
        slave_id_width_expr = f"ID_WIDTH+$clog2({num_masters})" if num_masters > 1 else "ID_WIDTH"
        
        for i in range(len(self.config.slaves)):
            signals.append(f"""    // Slave {i} signals (slave ID width = {slave_id_width_expr})
    logic [{slave_id_width_expr}-1:0]    s{i}_awid;
    logic [3:0]              s{i}_awcache;
    logic [2:0]              s{i}_awprot;
    logic [3:0]              s{i}_awqos;
    logic [ADDR_WIDTH-1:0]   s{i}_awaddr;
    logic [7:0]              s{i}_awlen;
    logic [2:0]              s{i}_awsize;
    logic [1:0]              s{i}_awburst;
    logic                    s{i}_awlock;
    logic                    s{i}_awvalid;
    logic                    s{i}_awready;
    
    logic [DATA_WIDTH-1:0]   s{i}_wdata;
    logic [DATA_WIDTH/8-1:0] s{i}_wstrb;
    logic                    s{i}_wlast;
    logic                    s{i}_wvalid;
    logic                    s{i}_wready;
    
    logic [{slave_id_width_expr}-1:0]    s{i}_bid;
    logic [1:0]              s{i}_bresp;
    logic                    s{i}_bvalid;
    logic                    s{i}_bready;
    
    logic [{slave_id_width_expr}-1:0]    s{i}_arid;
    logic [3:0]              s{i}_arcache;
    logic [2:0]              s{i}_arprot;
    logic [3:0]              s{i}_arqos;
    logic [ADDR_WIDTH-1:0]   s{i}_araddr;
    logic [7:0]              s{i}_arlen;
    logic [2:0]              s{i}_arsize;
    logic [1:0]              s{i}_arburst;
    logic                    s{i}_arlock;
    logic                    s{i}_arvalid;
    logic                    s{i}_arready;
    
    logic [{slave_id_width_expr}-1:0]    s{i}_rid;
    logic [DATA_WIDTH-1:0]   s{i}_rdata;
    logic [1:0]              s{i}_rresp;
    logic                    s{i}_rlast;
    logic                    s{i}_rvalid;
    logic                    s{i}_rready;
""")
        return "\n".join(signals)
    
    def _generate_master_connections(self):
        """Generate master port connections with correct RTL naming (lowercase)"""
        connections = []
        for i, master in enumerate(self.config.masters):
            connections.append(f"""        // Master {i} - {master.name}
        .m{i}_awid(m{i}_awid),
        .m{i}_awaddr(m{i}_awaddr),
        .m{i}_awlen(m{i}_awlen),
        .m{i}_awsize(m{i}_awsize),
        .m{i}_awburst(m{i}_awburst),
        .m{i}_awlock(m{i}_awlock),
        .m{i}_awcache(m{i}_awcache),
        .m{i}_awprot(m{i}_awprot),
        .m{i}_awqos(m{i}_awqos),
        .m{i}_awvalid(m{i}_awvalid),
        .m{i}_awready(m{i}_awready),
        
        .m{i}_wdata(m{i}_wdata),
        .m{i}_wstrb(m{i}_wstrb),
        .m{i}_wlast(m{i}_wlast),
        .m{i}_wvalid(m{i}_wvalid),
        .m{i}_wready(m{i}_wready),
        
        .m{i}_bid(m{i}_bid),
        .m{i}_bresp(m{i}_bresp),
        .m{i}_bvalid(m{i}_bvalid),
        .m{i}_bready(m{i}_bready),
        
        .m{i}_arid(m{i}_arid),
        .m{i}_araddr(m{i}_araddr),
        .m{i}_arlen(m{i}_arlen),
        .m{i}_arsize(m{i}_arsize),
        .m{i}_arburst(m{i}_arburst),
        .m{i}_arlock(m{i}_arlock),
        .m{i}_arcache(m{i}_arcache),
        .m{i}_arprot(m{i}_arprot),
        .m{i}_arqos(m{i}_arqos),
        .m{i}_arvalid(m{i}_arvalid),
        .m{i}_arready(m{i}_arready),
        
        .m{i}_rid(m{i}_rid),
        .m{i}_rdata(m{i}_rdata),
        .m{i}_rresp(m{i}_rresp),
        .m{i}_rlast(m{i}_rlast),
        .m{i}_rvalid(m{i}_rvalid),
        .m{i}_rready(m{i}_rready)""")
            if i < len(self.config.masters) - 1:
                connections[-1] += ","
        return "\n".join(connections)
    
    def _generate_slave_connections(self):
        """Generate slave port connections with correct RTL naming (lowercase)"""
        connections = []
        for i, slave in enumerate(self.config.slaves):
            connections.append(f"""        // Slave {i} - {slave.name}
        .s{i}_awid(s{i}_awid),
        .s{i}_awaddr(s{i}_awaddr),
        .s{i}_awlen(s{i}_awlen),
        .s{i}_awsize(s{i}_awsize),
        .s{i}_awburst(s{i}_awburst),
        .s{i}_awlock(s{i}_awlock),
        .s{i}_awvalid(s{i}_awvalid),
        .s{i}_awready(s{i}_awready),
        .s{i}_awcache(s{i}_awcache),
        .s{i}_awprot(s{i}_awprot),
        .s{i}_awqos(s{i}_awqos),
        
        .s{i}_wdata(s{i}_wdata),
        .s{i}_wstrb(s{i}_wstrb),
        .s{i}_wlast(s{i}_wlast),
        .s{i}_wvalid(s{i}_wvalid),
        .s{i}_wready(s{i}_wready),
        
        .s{i}_bid(s{i}_bid),
        .s{i}_bresp(s{i}_bresp),
        .s{i}_bvalid(s{i}_bvalid),
        .s{i}_bready(s{i}_bready),
        
        .s{i}_arid(s{i}_arid),
        .s{i}_araddr(s{i}_araddr),
        .s{i}_arlen(s{i}_arlen),
        .s{i}_arsize(s{i}_arsize),
        .s{i}_arburst(s{i}_arburst),
        .s{i}_arlock(s{i}_arlock),
        .s{i}_arvalid(s{i}_arvalid),
        .s{i}_arready(s{i}_arready),
        .s{i}_arcache(s{i}_arcache),
        .s{i}_arprot(s{i}_arprot),
        .s{i}_arqos(s{i}_arqos),
        
        .s{i}_rid(s{i}_rid),
        .s{i}_rdata(s{i}_rdata),
        .s{i}_rresp(s{i}_rresp),
        .s{i}_rlast(s{i}_rlast),
        .s{i}_rvalid(s{i}_rvalid),
        .s{i}_rready(s{i}_rready)""")
        # Add comma between master and slave connections, and between slaves
        if len(connections) > 0:
            connections = [",\n" + conn if i > 0 else conn for i, conn in enumerate(connections)]
        return "\n".join(connections)
    
    def _generate_master_termination(self):
        """Generate termination logic for unused masters"""
        if len(self.config.masters) <= 1:
            return "    // No additional masters to terminate"
            
        termination = ["    // Terminate unused master interfaces"]
        for i in range(1, len(self.config.masters)):
            termination.append(f"""    // Master {i} termination
    // Write Address Channel
    assign m{i}_awid    = {{ID_WIDTH{{1'b0}}}};
    assign m{i}_awaddr  = {{ADDR_WIDTH{{1'b0}}}};
    assign m{i}_awlen   = 8'd0;
    assign m{i}_awsize  = 3'd0;
    assign m{i}_awburst = 2'b01;
    assign m{i}_awlock  = 1'b0;
    assign m{i}_awcache = 4'b0000;
    assign m{i}_awprot  = 3'b000;
    assign m{i}_awqos   = 4'b0000;
    assign m{i}_awvalid = 1'b0;
    
    // Write Data Channel
    assign m{i}_wdata   = {{DATA_WIDTH{{1'b0}}}};
    assign m{i}_wstrb   = {{(DATA_WIDTH/8){{1'b0}}}};
    assign m{i}_wlast   = 1'b0;
    assign m{i}_wvalid  = 1'b0;
    
    // Write Response Channel
    assign m{i}_bready  = 1'b1;
    
    // Read Address Channel
    assign m{i}_arid    = {{ID_WIDTH{{1'b0}}}};
    assign m{i}_araddr  = {{ADDR_WIDTH{{1'b0}}}};
    assign m{i}_arlen   = 8'd0;
    assign m{i}_arsize  = 3'd0;
    assign m{i}_arburst = 2'b01;
    assign m{i}_arlock  = 1'b0;
    assign m{i}_arcache = 4'b0000;
    assign m{i}_arprot  = 3'b000;
    assign m{i}_arqos   = 4'b0000;
    assign m{i}_arvalid = 1'b0;
    
    // Read Data Channel
    assign m{i}_rready  = 1'b1;
""")
        return "\n".join(termination)
    
    def _generate_slave_responses(self):
        """Generate response logic for all slaves"""
        responses = ["    // Slave response logic for testing"]
        for i, slave in enumerate(self.config.slaves):
            responses.append(f"""    // Slave {i} ({slave.name}) - Simple memory model
    always @(posedge clk) begin
        if (!rst_n) begin
            s{i}_awready <= 1'b0;
            s{i}_wready  <= 1'b0;
            s{i}_bvalid  <= 1'b0;
            s{i}_arready <= 1'b0;
            s{i}_rvalid  <= 1'b0;
        end else begin
            // Simple handshaking
            s{i}_awready <= 1'b1;
            s{i}_wready  <= 1'b1;
            s{i}_arready <= 1'b1;
            
            // Write response
            if (s{i}_awvalid && s{i}_awready && s{i}_wvalid && s{i}_wready && s{i}_wlast) begin
                s{i}_bvalid <= 1'b1;
                s{i}_bid    <= s{i}_awid;
                s{i}_bresp  <= 2'b00; // OKAY
            end else if (s{i}_bready && s{i}_bvalid) begin
                s{i}_bvalid <= 1'b0;
            end
            
            // Read response (single beat for now)
            if (s{i}_arvalid && s{i}_arready) begin
                s{i}_rvalid <= 1'b1;
                s{i}_rid    <= s{i}_arid;
                s{i}_rdata  <= {{DATA_WIDTH{{1'b0}}}}; // Return zeros
                s{i}_rresp  <= 2'b00; // OKAY
                s{i}_rlast  <= 1'b1;  // Single beat
            end else if (s{i}_rready && s{i}_rvalid) begin
                s{i}_rvalid <= 1'b0;
            end
        end
    end
""")
        return "\n".join(responses)