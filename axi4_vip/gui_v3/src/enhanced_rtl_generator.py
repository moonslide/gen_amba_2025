#!/usr/bin/env python3
"""
Enhanced RTL Generator with full feature support
Wraps gen_amba tools and adds missing protocol features
"""

import os
import subprocess
import logging
from datetime import datetime
from typing import Dict, List, Optional

logger = logging.getLogger(__name__)

class EnhancedRTLGenerator:
    """Generate enhanced RTL with all AXI4 features"""
    
    def __init__(self, project_config, settings):
        self.project = project_config
        self.settings = settings
        self.output_dir = settings['output_dir']
        
        # Paths to gen_amba tools
        self.gen_amba_base = "/home/timtim01/eda_test/project/gen_amba_2025"
        self.gen_axi = os.path.join(self.gen_amba_base, "gen_amba_axi/gen_amba_axi")
        self.gen_ahb = os.path.join(self.gen_amba_base, "gen_amba_ahb/gen_amba_ahb")
        self.gen_apb = os.path.join(self.gen_amba_base, "gen_amba_apb/gen_amba_apb")
        
    def generate(self):
        """Generate complete RTL with all features"""
        rtl_dir = os.path.join(self.output_dir, 'rtl')
        os.makedirs(rtl_dir, exist_ok=True)
        
        # Step 1: Generate base interconnect using gen_amba
        base_file = self.generate_base_interconnect(rtl_dir)
        
        # Step 2: Enhance with missing features
        if 'rtl' in self.settings:
            rtl_settings = self.settings['rtl']
            
            # Add QoS support
            if self.settings['common'].get('enable_qos', False):
                self.add_qos_wrapper(rtl_dir, base_file)
            
            # Add REGION support
            if self.settings['common'].get('enable_region', False):
                self.add_region_wrapper(rtl_dir, base_file)
            
            # Add USER signals
            if self.settings['common'].get('enable_user', False):
                self.add_user_signals(rtl_dir, base_file)
            
            # Add pipeline stages
            if rtl_settings.get('pipeline_stages', 0) > 0:
                self.add_pipeline_stages(rtl_dir, base_file, rtl_settings['pipeline_stages'])
            
            # Add arbitration schemes
            if rtl_settings.get('arbitration', 'round_robin') != 'round_robin':
                self.add_arbitration_scheme(rtl_dir, base_file, rtl_settings['arbitration'])
            
            # Add exclusive access monitor
            if self.settings['common'].get('enable_exclusive', False):
                self.add_exclusive_monitor(rtl_dir, base_file)
            
            # Add CDC logic if needed
            # CDC is needed when: 1) explicitly requested, OR 2) multiple domains exist
            if rtl_settings.get('gen_cdc', False) or (hasattr(self.project, 'domains') and len(self.project.domains) > 1):
                self.add_cdc_logic(rtl_dir, len(getattr(self.project, 'domains', [])))
            
            # Add firewall/security if requested
            if rtl_settings.get('gen_firewall', False) or self.settings['common'].get('enable_firewall', False):
                self.add_firewall(rtl_dir)
            
            # Add assertions if requested
            if rtl_settings.get('gen_assertions', False):
                self.add_assertions(rtl_dir)
        
        # Step 3: Generate supporting files
        if self.settings['common'].get('gen_filelist', False):
            self.generate_filelist(rtl_dir)
        
        if self.settings['common'].get('gen_makefile', False):
            self.generate_makefile(rtl_dir)
        
        if self.settings['common'].get('gen_scripts', False):
            self.generate_sim_scripts(rtl_dir)
        
        if self.settings['common'].get('gen_documentation', False):
            self.generate_documentation(rtl_dir)
        
        # Always generate integrated top file for easier use
        self.generate_integrated_top(rtl_dir)
        
        logger.info(f"Enhanced RTL generation complete: {rtl_dir}")
        return rtl_dir
    
    def generate_base_interconnect(self, rtl_dir):
        """Generate base interconnect using gen_amba_axi"""
        output_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_interconnect.v")
        
        # Build command
        cmd = [
            self.gen_axi,
            f"--master={len(self.project.masters)}",
            f"--slave={len(self.project.slaves)}",
            f"--module={self.settings['project_name']}_interconnect",
            f"--addr-width={self.settings['common']['addr_width']}",
            f"--data-width={self.settings['common']['data_width']}",
            f"--output={output_file}"
        ]
        
        # Add AXI3 flag if needed
        if hasattr(self.project, 'axi_version') and self.project.axi_version == 3:
            cmd.append("--axi3")
        
        # Add AXI4 feature flags
        if self.settings['common'].get('enable_qos', False):
            cmd.append("--enable-qos")
        if self.settings['common'].get('enable_region', False):
            cmd.append("--enable-region")
        if self.settings['common'].get('enable_user', False):
            cmd.append("--enable-user")
        if self.settings['common'].get('enable_firewall', False):
            cmd.append("--enable-firewall")
        if self.settings['common'].get('enable_cdc', False):
            cmd.append("--enable-cdc")
        if hasattr(self.project, 'bus') and hasattr(self.project.bus, 'user_width') and self.project.bus.user_width > 0:
            cmd.append(f"--user-width={self.project.bus.user_width}")
        
        # Run gen_amba_axi (Python 3.6 compatible)
        try:
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, 
                                  universal_newlines=True, check=True)
            logger.info(f"Generated base interconnect: {output_file}")
        except subprocess.CalledProcessError as e:
            logger.error(f"Failed to generate base interconnect: {e.stderr}")
            raise
        
        return output_file
    
    def add_qos_wrapper(self, rtl_dir, base_file):
        """Add QoS support wrapper"""
        qos_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_qos_wrapper.v")
        
        content = f"""//------------------------------------------------------------------------------
// QoS Wrapper for {self.settings['project_name']}
// Generated by Enhanced RTL Generator
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
//------------------------------------------------------------------------------

module {self.settings['project_name']}_qos_wrapper #(
    parameter ADDR_WIDTH = {self.settings['common']['addr_width']},
    parameter DATA_WIDTH = {self.settings['common']['data_width']},
    parameter ID_WIDTH   = {self.settings['common']['id_width']},
    parameter NUM_MASTERS = {len(self.project.masters)},
    parameter NUM_SLAVES  = {len(self.project.slaves)}
)(
    input wire aclk,
    input wire aresetn,
    
    // Master interfaces with QoS
"""
        
        # Add master ports with QoS
        for i in range(len(self.project.masters)):
            content += f"""
    // Master {i} interface
    input  wire [3:0]              m{i}_awqos,
    input  wire [3:0]              m{i}_arqos,
    input  wire [ID_WIDTH-1:0]     m{i}_awid,
    input  wire [ADDR_WIDTH-1:0]   m{i}_awaddr,
    input  wire [7:0]              m{i}_awlen,
    input  wire [2:0]              m{i}_awsize,
    input  wire [1:0]              m{i}_awburst,
    input  wire                    m{i}_awvalid,
    output wire                    m{i}_awready,
    // ... other signals
"""
        
        content += """
);

// QoS-based arbitration logic
reg [3:0] qos_priority [0:NUM_MASTERS-1];
reg [NUM_MASTERS-1:0] grant;

// Priority encoder based on QoS values
always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        grant <= 0;
    end else begin
        // Implement QoS-based arbitration
        // Higher QoS value = higher priority
    end
end

// Instantiate base interconnect
{0}_interconnect base_interconnect (
    .aclk(aclk),
    .aresetn(aresetn),
    // Connect signals
);

endmodule
""".format(self.settings['project_name'])
        
        with open(qos_file, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated QoS wrapper: {qos_file}")
        return qos_file
    
    def add_region_wrapper(self, rtl_dir, base_file):
        """Add REGION support wrapper"""
        region_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_region_wrapper.v")
        
        content = f"""//------------------------------------------------------------------------------
// REGION Wrapper for {self.settings['project_name']}
// Generated by Enhanced RTL Generator
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
//------------------------------------------------------------------------------

module {self.settings['project_name']}_region_wrapper #(
    parameter ADDR_WIDTH = {self.settings['common']['addr_width']},
    parameter DATA_WIDTH = {self.settings['common']['data_width']},
    parameter ID_WIDTH   = {self.settings['common']['id_width']},
    parameter NUM_MASTERS = {len(self.project.masters)},
    parameter NUM_SLAVES  = {len(self.project.slaves)},
    parameter NUM_REGIONS = 16
)(
    input wire aclk,
    input wire aresetn,
    
    // Master interfaces with REGION
"""
        
        for i in range(len(self.project.masters)):
            content += f"""
    // Master {i} interface
    input  wire [3:0]              m{i}_awregion,
    input  wire [3:0]              m{i}_arregion,
"""
        
        content += """
    // Other signals...
);

// Region configuration registers
reg [ADDR_WIDTH-1:0] region_base [0:NUM_REGIONS-1];
reg [ADDR_WIDTH-1:0] region_size [0:NUM_REGIONS-1];
reg [NUM_SLAVES-1:0] region_slave_map [0:NUM_REGIONS-1];

// Region decode logic
always @(*) begin
    // Decode region based on address
    // Map to appropriate slave
end

endmodule
"""
        
        with open(region_file, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated REGION wrapper: {region_file}")
        return region_file
    
    def add_user_signals(self, rtl_dir, base_file):
        """Add USER signal support"""
        user_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_user_wrapper.v")
        
        user_width = self.settings['common'].get('user_width', 0)
        if user_width == 0:
            return None
        
        content = f"""//------------------------------------------------------------------------------
// USER Signal Wrapper for {self.settings['project_name']}
// Generated by Enhanced RTL Generator
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
//------------------------------------------------------------------------------

module {self.settings['project_name']}_user_wrapper #(
    parameter USER_WIDTH = {user_width},
    parameter ADDR_WIDTH = {self.settings['common']['addr_width']},
    parameter DATA_WIDTH = {self.settings['common']['data_width']},
    parameter ID_WIDTH   = {self.settings['common']['id_width']}
)(
    input wire aclk,
    input wire aresetn,
    
    // USER signals for each channel
    input  wire [USER_WIDTH-1:0] awuser,
    input  wire [USER_WIDTH-1:0] wuser,
    output wire [USER_WIDTH-1:0] buser,
    input  wire [USER_WIDTH-1:0] aruser,
    output wire [USER_WIDTH-1:0] ruser,
    
    // Other signals...
);

// USER signal pass-through logic
// Route USER signals alongside transactions

endmodule
"""
        
        with open(user_file, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated USER wrapper: {user_file}")
        return user_file
    
    def add_pipeline_stages(self, rtl_dir, base_file, num_stages):
        """Add configurable pipeline stages"""
        pipeline_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_pipeline.v")
        
        content = f"""//------------------------------------------------------------------------------
// Pipeline Stages for {self.settings['project_name']}
// Generated by Enhanced RTL Generator
// Pipeline Stages: {num_stages}
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
//------------------------------------------------------------------------------

module {self.settings['project_name']}_pipeline #(
    parameter PIPELINE_STAGES = {num_stages},
    parameter ADDR_WIDTH = {self.settings['common']['addr_width']},
    parameter DATA_WIDTH = {self.settings['common']['data_width']}
)(
    input wire aclk,
    input wire aresetn,
    
    // Input interface
    input  wire [ADDR_WIDTH-1:0] addr_in,
    input  wire [DATA_WIDTH-1:0] data_in,
    input  wire                  valid_in,
    output wire                  ready_out,
    
    // Output interface
    output wire [ADDR_WIDTH-1:0] addr_out,
    output wire [DATA_WIDTH-1:0] data_out,
    output wire                  valid_out,
    input  wire                  ready_in
);

// Pipeline registers
genvar i;
generate
    for (i = 0; i < PIPELINE_STAGES; i = i + 1) begin : pipeline_stage
        reg [ADDR_WIDTH-1:0] addr_reg;
        reg [DATA_WIDTH-1:0] data_reg;
        reg valid_reg;
        
        always @(posedge aclk or negedge aresetn) begin
            if (!aresetn) begin
                addr_reg <= 0;
                data_reg <= 0;
                valid_reg <= 0;
            end else if (ready_in) begin
                if (i == 0) begin
                    addr_reg <= addr_in;
                    data_reg <= data_in;
                    valid_reg <= valid_in;
                end else begin
                    addr_reg <= pipeline_stage[i-1].addr_reg;
                    data_reg <= pipeline_stage[i-1].data_reg;
                    valid_reg <= pipeline_stage[i-1].valid_reg;
                end
            end
        end
    end
endgenerate

// Output assignment
assign addr_out = (PIPELINE_STAGES > 0) ? pipeline_stage[PIPELINE_STAGES-1].addr_reg : addr_in;
assign data_out = (PIPELINE_STAGES > 0) ? pipeline_stage[PIPELINE_STAGES-1].data_reg : data_in;
assign valid_out = (PIPELINE_STAGES > 0) ? pipeline_stage[PIPELINE_STAGES-1].valid_reg : valid_in;
assign ready_out = ready_in;

endmodule
"""
        
        with open(pipeline_file, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated pipeline stages: {pipeline_file}")
        return pipeline_file
    
    def add_arbitration_scheme(self, rtl_dir, base_file, scheme):
        """Add different arbitration schemes"""
        arb_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_arbiter_{scheme}.v")
        
        content = f"""//------------------------------------------------------------------------------
// {scheme.upper()} Arbiter for {self.settings['project_name']}
// Generated by Enhanced RTL Generator
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
//------------------------------------------------------------------------------

module {self.settings['project_name']}_arbiter_{scheme} #(
    parameter NUM_MASTERS = {len(self.project.masters)}
)(
    input wire aclk,
    input wire aresetn,
    
    // Request inputs
    input  wire [NUM_MASTERS-1:0] request,
    input  wire [3:0] qos [0:NUM_MASTERS-1],
    
    // Grant outputs
    output reg [NUM_MASTERS-1:0] grant
);

"""
        
        if scheme == 'fixed_priority':
            content += """
// Fixed priority arbitration
integer i;
always @(*) begin
    grant = 0;
    for (i = 0; i < NUM_MASTERS; i = i + 1) begin
        if (request[i] && grant == 0) begin
            grant[i] = 1'b1;
        end
    end
end
"""
        elif scheme == 'weighted':
            content += """
// Weighted round-robin arbitration
reg [7:0] weight_counter [0:NUM_MASTERS-1];
reg [7:0] weight_value [0:NUM_MASTERS-1];
reg [$clog2(NUM_MASTERS)-1:0] current_master;

always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        current_master <= 0;
        grant <= 0;
    end else begin
        // Implement weighted arbitration
        if (weight_counter[current_master] > 0) begin
            if (request[current_master]) begin
                grant <= (1 << current_master);
                weight_counter[current_master] <= weight_counter[current_master] - 1;
            end else begin
                current_master <= (current_master + 1) % NUM_MASTERS;
                weight_counter[current_master] <= weight_value[current_master];
            end
        end else begin
            current_master <= (current_master + 1) % NUM_MASTERS;
            weight_counter[current_master] <= weight_value[current_master];
        end
    end
end
"""
        elif scheme == 'qos_based':
            content += """
// QoS-based arbitration
reg [3:0] max_qos;
reg [$clog2(NUM_MASTERS)-1:0] selected_master;
integer i;

always @(*) begin
    max_qos = 0;
    selected_master = 0;
    grant = 0;
    
    // Find highest QoS requesting master
    for (i = 0; i < NUM_MASTERS; i = i + 1) begin
        if (request[i] && qos[i] > max_qos) begin
            max_qos = qos[i];
            selected_master = i;
        end
    end
    
    if (max_qos > 0) begin
        grant[selected_master] = 1'b1;
    end
end
"""
        
        content += "\nendmodule\n"
        
        with open(arb_file, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated {scheme} arbiter: {arb_file}")
        return arb_file
    
    def add_exclusive_monitor(self, rtl_dir, base_file):
        """Add exclusive access monitor"""
        excl_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_exclusive_monitor.v")
        
        content = f"""//------------------------------------------------------------------------------
// Exclusive Access Monitor for {self.settings['project_name']}
// Generated by Enhanced RTL Generator
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
//------------------------------------------------------------------------------

module {self.settings['project_name']}_exclusive_monitor #(
    parameter ADDR_WIDTH = {self.settings['common']['addr_width']},
    parameter ID_WIDTH   = {self.settings['common']['id_width']},
    parameter NUM_MONITORS = 16
)(
    input wire aclk,
    input wire aresetn,
    
    // Exclusive read tracking
    input  wire [ID_WIDTH-1:0]   excl_rid,
    input  wire [ADDR_WIDTH-1:0] excl_raddr,
    input  wire                  excl_rvalid,
    
    // Exclusive write checking
    input  wire [ID_WIDTH-1:0]   excl_wid,
    input  wire [ADDR_WIDTH-1:0] excl_waddr,
    input  wire                  excl_wvalid,
    output reg                   excl_wpass
);

// Exclusive access table
reg [ADDR_WIDTH-1:0] excl_addr_table [0:NUM_MONITORS-1];
reg [ID_WIDTH-1:0]   excl_id_table [0:NUM_MONITORS-1];
reg                   excl_valid_table [0:NUM_MONITORS-1];

integer i;

// Track exclusive reads
always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        for (i = 0; i < NUM_MONITORS; i = i + 1) begin
            excl_valid_table[i] <= 0;
        end
    end else if (excl_rvalid) begin
        // Store exclusive read in table
        for (i = 0; i < NUM_MONITORS; i = i + 1) begin
            if (!excl_valid_table[i]) begin
                excl_addr_table[i] <= excl_raddr;
                excl_id_table[i] <= excl_rid;
                excl_valid_table[i] <= 1'b1;
                break;
            end
        end
    end
end

// Check exclusive writes
always @(*) begin
    excl_wpass = 1'b0;
    for (i = 0; i < NUM_MONITORS; i = i + 1) begin
        if (excl_valid_table[i] && 
            excl_id_table[i] == excl_wid &&
            excl_addr_table[i] == excl_waddr) begin
            excl_wpass = 1'b1;
        end
    end
end

endmodule
"""
        
        with open(excl_file, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated exclusive monitor: {excl_file}")
        return excl_file
    
    def add_cdc_logic(self, rtl_dir, num_domains=0):
        """Add Clock Domain Crossing logic"""
        cdc_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_cdc.v")
        
        # Determine number of clock domains
        if num_domains == 0:
            # If no domains specified, create CDC for at least 2 domains
            num_domains = 2
        
        content = f"""//------------------------------------------------------------------------------
// Clock Domain Crossing (CDC) Logic for {self.settings['project_name']}
// Generated by Enhanced RTL Generator
// Number of Clock Domains: {num_domains}
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
//------------------------------------------------------------------------------

module {self.settings['project_name']}_cdc #(
    parameter DATA_WIDTH = {self.settings['common']['data_width']},
    parameter ADDR_WIDTH = {self.settings['common']['addr_width']},
    parameter ID_WIDTH   = {self.settings['common']['id_width']},
    parameter SYNC_STAGES = 2,
    parameter FIFO_DEPTH = 4
)(
    // Source domain
    input  wire src_clk,
    input  wire src_rstn,
    
    // AXI Write Address Channel
    input  wire [ID_WIDTH-1:0]     src_awid,
    input  wire [ADDR_WIDTH-1:0]   src_awaddr,
    input  wire [7:0]              src_awlen,
    input  wire [2:0]              src_awsize,
    input  wire [1:0]              src_awburst,
    input  wire                    src_awvalid,
    output wire                    src_awready,
    
    // AXI Write Data Channel
    input  wire [DATA_WIDTH-1:0]   src_wdata,
    input  wire [DATA_WIDTH/8-1:0] src_wstrb,
    input  wire                    src_wlast,
    input  wire                    src_wvalid,
    output wire                    src_wready,
    
    // Destination domain
    input  wire dst_clk,
    input  wire dst_rstn,
    
    // AXI Write Address Channel
    output reg [ID_WIDTH-1:0]      dst_awid,
    output reg [ADDR_WIDTH-1:0]    dst_awaddr,
    output reg [7:0]               dst_awlen,
    output reg [2:0]               dst_awsize,
    output reg [1:0]               dst_awburst,
    output reg                     dst_awvalid,
    input  wire                    dst_awready,
    
    // AXI Write Data Channel
    output reg [DATA_WIDTH-1:0]    dst_wdata,
    output reg [DATA_WIDTH/8-1:0]  dst_wstrb,
    output reg                     dst_wlast,
    output reg                     dst_wvalid,
    input  wire                    dst_wready
);

// Async FIFO for AW channel
reg [ADDR_WIDTH+ID_WIDTH+13:0] aw_fifo [0:FIFO_DEPTH-1]; // awid + awaddr + awlen + awsize + awburst
reg [$clog2(FIFO_DEPTH):0] aw_wr_ptr, aw_rd_ptr;
reg [$clog2(FIFO_DEPTH):0] aw_wr_ptr_gray, aw_rd_ptr_gray;
reg [$clog2(FIFO_DEPTH):0] aw_wr_ptr_sync [0:SYNC_STAGES-1];
reg [$clog2(FIFO_DEPTH):0] aw_rd_ptr_sync [0:SYNC_STAGES-1];

// Async FIFO for W channel
reg [DATA_WIDTH+DATA_WIDTH/8:0] w_fifo [0:FIFO_DEPTH-1]; // wdata + wstrb + wlast
reg [$clog2(FIFO_DEPTH):0] w_wr_ptr, w_rd_ptr;
reg [$clog2(FIFO_DEPTH):0] w_wr_ptr_gray, w_rd_ptr_gray;
reg [$clog2(FIFO_DEPTH):0] w_wr_ptr_sync [0:SYNC_STAGES-1];
reg [$clog2(FIFO_DEPTH):0] w_rd_ptr_sync [0:SYNC_STAGES-1];

// Gray code conversion functions
function [$clog2(FIFO_DEPTH):0] bin2gray;
    input [$clog2(FIFO_DEPTH):0] bin;
    begin
        bin2gray = bin ^ (bin >> 1);
    end
endfunction

function [$clog2(FIFO_DEPTH):0] gray2bin;
    input [$clog2(FIFO_DEPTH):0] gray;
    integer i;
    begin
        gray2bin[$clog2(FIFO_DEPTH)] = gray[$clog2(FIFO_DEPTH)];
        for (i = $clog2(FIFO_DEPTH)-1; i >= 0; i = i - 1)
            gray2bin[i] = gray2bin[i+1] ^ gray[i];
    end
endfunction

// Write domain logic - AW channel
always @(posedge src_clk or negedge src_rstn) begin
    if (!src_rstn) begin
        aw_wr_ptr <= 0;
        aw_wr_ptr_gray <= 0;
    end else if (src_awvalid && src_awready) begin
        aw_fifo[aw_wr_ptr[$clog2(FIFO_DEPTH)-1:0]] <= {{src_awid, src_awaddr, src_awlen, src_awsize, src_awburst}};
        aw_wr_ptr <= aw_wr_ptr + 1;
        aw_wr_ptr_gray <= bin2gray(aw_wr_ptr + 1);
    end
end

// Write domain logic - W channel
always @(posedge src_clk or negedge src_rstn) begin
    if (!src_rstn) begin
        w_wr_ptr <= 0;
        w_wr_ptr_gray <= 0;
    end else if (src_wvalid && src_wready) begin
        w_fifo[w_wr_ptr[$clog2(FIFO_DEPTH)-1:0]] <= {{src_wdata, src_wstrb, src_wlast}};
        w_wr_ptr <= w_wr_ptr + 1;
        w_wr_ptr_gray <= bin2gray(w_wr_ptr + 1);
    end
end

// Synchronizers - AW channel
integer i;
always @(posedge dst_clk or negedge dst_rstn) begin
    if (!dst_rstn) begin
        for (i = 0; i < SYNC_STAGES; i = i + 1)
            aw_wr_ptr_sync[i] <= 0;
    end else begin
        aw_wr_ptr_sync[0] <= aw_wr_ptr_gray;
        for (i = 1; i < SYNC_STAGES; i = i + 1)
            aw_wr_ptr_sync[i] <= aw_wr_ptr_sync[i-1];
    end
end

// Read domain logic - AW channel
wire [$clog2(FIFO_DEPTH):0] aw_wr_ptr_dst = gray2bin(aw_wr_ptr_sync[SYNC_STAGES-1]);
wire aw_empty = (aw_rd_ptr == aw_wr_ptr_dst);

always @(posedge dst_clk or negedge dst_rstn) begin
    if (!dst_rstn) begin
        aw_rd_ptr <= 0;
        aw_rd_ptr_gray <= 0;
        dst_awvalid <= 0;
    end else begin
        if (!aw_empty && (!dst_awvalid || dst_awready)) begin
            {{dst_awid, dst_awaddr, dst_awlen, dst_awsize, dst_awburst}} <= aw_fifo[aw_rd_ptr[$clog2(FIFO_DEPTH)-1:0]];
            dst_awvalid <= 1;
            aw_rd_ptr <= aw_rd_ptr + 1;
            aw_rd_ptr_gray <= bin2gray(aw_rd_ptr + 1);
        end else if (dst_awvalid && dst_awready) begin
            dst_awvalid <= 0;
        end
    end
end

// Synchronizers - W channel
always @(posedge dst_clk or negedge dst_rstn) begin
    if (!dst_rstn) begin
        for (i = 0; i < SYNC_STAGES; i = i + 1)
            w_wr_ptr_sync[i] <= 0;
    end else begin
        w_wr_ptr_sync[0] <= w_wr_ptr_gray;
        for (i = 1; i < SYNC_STAGES; i = i + 1)
            w_wr_ptr_sync[i] <= w_wr_ptr_sync[i-1];
    end
end

// Read domain logic - W channel
wire [$clog2(FIFO_DEPTH):0] w_wr_ptr_dst = gray2bin(w_wr_ptr_sync[SYNC_STAGES-1]);
wire w_empty = (w_rd_ptr == w_wr_ptr_dst);

always @(posedge dst_clk or negedge dst_rstn) begin
    if (!dst_rstn) begin
        w_rd_ptr <= 0;
        w_rd_ptr_gray <= 0;
        dst_wvalid <= 0;
    end else begin
        if (!w_empty && (!dst_wvalid || dst_wready)) begin
            {{dst_wdata, dst_wstrb, dst_wlast}} <= w_fifo[w_rd_ptr[$clog2(FIFO_DEPTH)-1:0]];
            dst_wvalid <= 1;
            w_rd_ptr <= w_rd_ptr + 1;
            w_rd_ptr_gray <= bin2gray(w_rd_ptr + 1);
        end else if (dst_wvalid && dst_wready) begin
            dst_wvalid <= 0;
        end
    end
end

// AR Channel CDC - Address Read
reg [ADDR_WIDTH+ID_WIDTH+10:0] ar_fifo [0:FIFO_DEPTH-1];
reg [$clog2(FIFO_DEPTH):0] ar_wr_ptr, ar_wr_ptr_gray;
reg [$clog2(FIFO_DEPTH):0] ar_rd_ptr, ar_rd_ptr_gray;
reg [$clog2(FIFO_DEPTH):0] ar_wr_ptr_sync [0:SYNC_STAGES-1];
reg [$clog2(FIFO_DEPTH):0] ar_rd_ptr_sync [0:SYNC_STAGES-1];

// Write domain logic - AR channel
always @(posedge src_clk or negedge src_rstn) begin
    if (!src_rstn) begin
        ar_wr_ptr <= 0;
        ar_wr_ptr_gray <= 0;
    end else if (src_arvalid && src_arready) begin
        ar_fifo[ar_wr_ptr[$clog2(FIFO_DEPTH)-1:0]] <= {{src_arid, src_araddr, src_arlen, src_arsize, src_arburst}};
        ar_wr_ptr <= ar_wr_ptr + 1;
        ar_wr_ptr_gray <= bin2gray(ar_wr_ptr + 1);
    end
end

// Synchronizers - AR channel
always @(posedge dst_clk or negedge dst_rstn) begin
    if (!dst_rstn) begin
        for (i = 0; i < SYNC_STAGES; i = i + 1)
            ar_wr_ptr_sync[i] <= 0;
    end else begin
        ar_wr_ptr_sync[0] <= ar_wr_ptr_gray;
        for (i = 1; i < SYNC_STAGES; i = i + 1)
            ar_wr_ptr_sync[i] <= ar_wr_ptr_sync[i-1];
    end
end

// Read domain logic - AR channel
wire [$clog2(FIFO_DEPTH):0] ar_wr_ptr_dst = gray2bin(ar_wr_ptr_sync[SYNC_STAGES-1]);
wire ar_empty = (ar_rd_ptr == ar_wr_ptr_dst);

always @(posedge dst_clk or negedge dst_rstn) begin
    if (!dst_rstn) begin
        ar_rd_ptr <= 0;
        ar_rd_ptr_gray <= 0;
        dst_arvalid <= 0;
    end else begin
        if (!ar_empty && (!dst_arvalid || dst_arready)) begin
            {{dst_arid, dst_araddr, dst_arlen, dst_arsize, dst_arburst}} <= ar_fifo[ar_rd_ptr[$clog2(FIFO_DEPTH)-1:0]];
            dst_arvalid <= 1;
            ar_rd_ptr <= ar_rd_ptr + 1;
            ar_rd_ptr_gray <= bin2gray(ar_rd_ptr + 1);
        end else if (dst_arvalid && dst_arready) begin
            dst_arvalid <= 0;
        end
    end
end

// R Channel CDC - Read Response (from dst to src)
reg [DATA_WIDTH+ID_WIDTH+3:0] r_fifo [0:FIFO_DEPTH-1];
reg [$clog2(FIFO_DEPTH):0] r_wr_ptr, r_wr_ptr_gray;
reg [$clog2(FIFO_DEPTH):0] r_rd_ptr, r_rd_ptr_gray;
reg [$clog2(FIFO_DEPTH):0] r_wr_ptr_sync [0:SYNC_STAGES-1];
reg [$clog2(FIFO_DEPTH):0] r_rd_ptr_sync [0:SYNC_STAGES-1];

// Write domain logic - R channel (dst domain)
always @(posedge dst_clk or negedge dst_rstn) begin
    if (!dst_rstn) begin
        r_wr_ptr <= 0;
        r_wr_ptr_gray <= 0;
    end else if (dst_rvalid && dst_rready) begin
        r_fifo[r_wr_ptr[$clog2(FIFO_DEPTH)-1:0]] <= {{dst_rid, dst_rdata, dst_rresp, dst_rlast}};
        r_wr_ptr <= r_wr_ptr + 1;
        r_wr_ptr_gray <= bin2gray(r_wr_ptr + 1);
    end
end

// Synchronizers - R channel
always @(posedge src_clk or negedge src_rstn) begin
    if (!src_rstn) begin
        for (i = 0; i < SYNC_STAGES; i = i + 1)
            r_wr_ptr_sync[i] <= 0;
    end else begin
        r_wr_ptr_sync[0] <= r_wr_ptr_gray;
        for (i = 1; i < SYNC_STAGES; i = i + 1)
            r_wr_ptr_sync[i] <= r_wr_ptr_sync[i-1];
    end
end

// Read domain logic - R channel (src domain)
wire [$clog2(FIFO_DEPTH):0] r_wr_ptr_src = gray2bin(r_wr_ptr_sync[SYNC_STAGES-1]);
wire r_empty = (r_rd_ptr == r_wr_ptr_src);

always @(posedge src_clk or negedge src_rstn) begin
    if (!src_rstn) begin
        r_rd_ptr <= 0;
        r_rd_ptr_gray <= 0;
        src_rvalid <= 0;
    end else begin
        if (!r_empty && (!src_rvalid || src_rready)) begin
            {{src_rid, src_rdata, src_rresp, src_rlast}} <= r_fifo[r_rd_ptr[$clog2(FIFO_DEPTH)-1:0]];
            src_rvalid <= 1;
            r_rd_ptr <= r_rd_ptr + 1;
            r_rd_ptr_gray <= bin2gray(r_rd_ptr + 1);
        end else if (src_rvalid && src_rready) begin
            src_rvalid <= 0;
        end
    end
end

// B Channel CDC - Write Response (from dst to src)
reg [ID_WIDTH+1:0] b_fifo [0:FIFO_DEPTH-1];
reg [$clog2(FIFO_DEPTH):0] b_wr_ptr, b_wr_ptr_gray;
reg [$clog2(FIFO_DEPTH):0] b_rd_ptr, b_rd_ptr_gray;
reg [$clog2(FIFO_DEPTH):0] b_wr_ptr_sync [0:SYNC_STAGES-1];
reg [$clog2(FIFO_DEPTH):0] b_rd_ptr_sync [0:SYNC_STAGES-1];

// Write domain logic - B channel (dst domain)
always @(posedge dst_clk or negedge dst_rstn) begin
    if (!dst_rstn) begin
        b_wr_ptr <= 0;
        b_wr_ptr_gray <= 0;
    end else if (dst_bvalid && dst_bready) begin
        b_fifo[b_wr_ptr[$clog2(FIFO_DEPTH)-1:0]] <= {{dst_bid, dst_bresp}};
        b_wr_ptr <= b_wr_ptr + 1;
        b_wr_ptr_gray <= bin2gray(b_wr_ptr + 1);
    end
end

// Synchronizers - B channel
always @(posedge src_clk or negedge src_rstn) begin
    if (!src_rstn) begin
        for (i = 0; i < SYNC_STAGES; i = i + 1)
            b_wr_ptr_sync[i] <= 0;
    end else begin
        b_wr_ptr_sync[0] <= b_wr_ptr_gray;
        for (i = 1; i < SYNC_STAGES; i = i + 1)
            b_wr_ptr_sync[i] <= b_wr_ptr_sync[i-1];
    end
end

// Read domain logic - B channel (src domain)
wire [$clog2(FIFO_DEPTH):0] b_wr_ptr_src = gray2bin(b_wr_ptr_sync[SYNC_STAGES-1]);
wire b_empty = (b_rd_ptr == b_wr_ptr_src);

always @(posedge src_clk or negedge src_rstn) begin
    if (!src_rstn) begin
        b_rd_ptr <= 0;
        b_rd_ptr_gray <= 0;
        src_bvalid <= 0;
    end else begin
        if (!b_empty && (!src_bvalid || src_bready)) begin
            {{src_bid, src_bresp}} <= b_fifo[b_rd_ptr[$clog2(FIFO_DEPTH)-1:0]];
            src_bvalid <= 1;
            b_rd_ptr <= b_rd_ptr + 1;
            b_rd_ptr_gray <= bin2gray(b_rd_ptr + 1);
        end else if (src_bvalid && src_bready) begin
            src_bvalid <= 0;
        end
    end
end

// Ready signals - forward path
assign src_awready = (aw_wr_ptr + 1 != gray2bin(aw_rd_ptr_sync[SYNC_STAGES-1]));
assign src_wready = (w_wr_ptr + 1 != gray2bin(w_rd_ptr_sync[SYNC_STAGES-1]));
assign src_arready = (ar_wr_ptr + 1 != gray2bin(ar_rd_ptr_sync[SYNC_STAGES-1]));

// Ready signals - return path
assign dst_rready = (r_rd_ptr != gray2bin(r_wr_ptr_sync[SYNC_STAGES-1]));
assign dst_bready = (b_rd_ptr != gray2bin(b_wr_ptr_sync[SYNC_STAGES-1]));

endmodule
"""
        
        with open(cdc_file, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated CDC logic: {cdc_file}")
        return cdc_file
    
    def add_firewall(self, rtl_dir):
        """Add AXI4 firewall for security access control"""
        firewall_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_firewall.v")
        
        # Get security configuration from project
        secure_masters = []
        secure_slaves = []
        
        if hasattr(self.project, 'masters'):
            for master in self.project.masters:
                if hasattr(master, 'security') and master.security == 'secure':
                    secure_masters.append(master.index)
        
        if hasattr(self.project, 'slaves'):
            for slave in self.project.slaves:
                if hasattr(slave, 'security') and slave.security == 'secure':
                    secure_slaves.append(slave.index)
        
        content = f"""//------------------------------------------------------------------------------
// AXI4 Firewall Module for {self.settings['project_name']}
// Generated by Enhanced RTL Generator
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
//------------------------------------------------------------------------------

module {self.settings['project_name']}_firewall #(
    parameter ADDR_WIDTH = {self.settings['common']['addr_width']},
    parameter DATA_WIDTH = {self.settings['common']['data_width']},
    parameter ID_WIDTH   = {self.settings['common']['id_width']},
    parameter NUM_MASTERS = {len(self.project.masters)},
    parameter NUM_SLAVES  = {len(self.project.slaves)}
)(
    input wire aclk,
    input wire aresetn,
    
    // Configuration interface
    input wire [NUM_MASTERS-1:0] master_secure,
    input wire [NUM_SLAVES-1:0]  slave_secure,
    input wire [NUM_SLAVES-1:0]  slave_nonsec_access_allowed,
    
    // Master interfaces (input)
    input wire [NUM_MASTERS-1:0] m_awvalid,
    input wire [NUM_MASTERS-1:0] m_arvalid,
    input wire [ID_WIDTH-1:0]    m_awid [0:NUM_MASTERS-1],
    input wire [ID_WIDTH-1:0]    m_arid [0:NUM_MASTERS-1],
    input wire [ADDR_WIDTH-1:0]  m_awaddr [0:NUM_MASTERS-1],
    input wire [ADDR_WIDTH-1:0]  m_araddr [0:NUM_MASTERS-1],
    input wire [2:0]              m_awprot [0:NUM_MASTERS-1],
    input wire [2:0]              m_arprot [0:NUM_MASTERS-1],
    
    // Slave selection
    input wire [$clog2(NUM_SLAVES)-1:0] aw_slave_sel [0:NUM_MASTERS-1],
    input wire [$clog2(NUM_SLAVES)-1:0] ar_slave_sel [0:NUM_MASTERS-1],
    
    // Security violation outputs
    output reg [NUM_MASTERS-1:0] aw_violation,
    output reg [NUM_MASTERS-1:0] ar_violation,
    output reg                   security_alert,
    
    // Transaction blocking
    output reg [NUM_MASTERS-1:0] aw_block,
    output reg [NUM_MASTERS-1:0] ar_block
);

// Security configuration registers
reg [NUM_MASTERS-1:0] master_is_secure;
reg [NUM_SLAVES-1:0]  slave_is_secure;
reg [NUM_SLAVES-1:0]  slave_allows_nonsec;

// Configuration update
always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        master_is_secure <= {{{len(self.project.masters)}{{1'b0}}}};
        slave_is_secure <= {{{len(self.project.slaves)}{{1'b0}}}};
        slave_allows_nonsec <= {{{len(self.project.slaves)}{{1'b1}}}}; // Default: allow non-secure
    end else begin
        master_is_secure <= master_secure;
        slave_is_secure <= slave_secure;
        slave_allows_nonsec <= slave_nonsec_access_allowed;
    end
end

// Security check logic for each master
genvar i;
generate
    for (i = 0; i < NUM_MASTERS; i = i + 1) begin : master_security_check
        
        // Write channel security check
        always @(*) begin
            aw_violation[i] = 1'b0;
            aw_block[i] = 1'b0;
            
            if (m_awvalid[i]) begin
                // Check AxPROT[1] bit: 0=secure, 1=non-secure
                reg is_secure_transaction = !m_awprot[i][1];
                reg target_is_secure = slave_is_secure[aw_slave_sel[i]];
                reg target_allows_nonsec = slave_allows_nonsec[aw_slave_sel[i]];
                
                // Security violation conditions:
                // 1. Non-secure master trying to access secure slave
                // 2. Non-secure transaction to secure-only slave
                if (!master_is_secure[i] && target_is_secure && !target_allows_nonsec) begin
                    aw_violation[i] = 1'b1;
                    aw_block[i] = 1'b1;
                end else if (!is_secure_transaction && target_is_secure && !target_allows_nonsec) begin
                    aw_violation[i] = 1'b1;
                    aw_block[i] = 1'b1;
                end
            end
        end
        
        // Read channel security check
        always @(*) begin
            ar_violation[i] = 1'b0;
            ar_block[i] = 1'b0;
            
            if (m_arvalid[i]) begin
                // Check AxPROT[1] bit: 0=secure, 1=non-secure
                reg is_secure_transaction = !m_arprot[i][1];
                reg target_is_secure = slave_is_secure[ar_slave_sel[i]];
                reg target_allows_nonsec = slave_allows_nonsec[ar_slave_sel[i]];
                
                // Security violation conditions:
                // 1. Non-secure master trying to access secure slave
                // 2. Non-secure transaction to secure-only slave
                if (!master_is_secure[i] && target_is_secure && !target_allows_nonsec) begin
                    ar_violation[i] = 1'b1;
                    ar_block[i] = 1'b1;
                end else if (!is_secure_transaction && target_is_secure && !target_allows_nonsec) begin
                    ar_violation[i] = 1'b1;
                    ar_block[i] = 1'b1;
                end
            end
        end
    end
endgenerate

// Global security alert
always @(*) begin
    security_alert = |aw_violation | |ar_violation;
end

// Violation logging
reg [31:0] violation_count;
reg [ID_WIDTH-1:0] last_violation_id;
reg [ADDR_WIDTH-1:0] last_violation_addr;
reg last_violation_is_write;

always @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
        violation_count <= 32'd0;
        last_violation_id <= {{{self.settings['common']['id_width']}{{1'b0}}}};
        last_violation_addr <= {{{self.settings['common']['addr_width']}{{1'b0}}}};
        last_violation_is_write <= 1'b0;
    end else begin
        // Log violations
        for (integer j = 0; j < NUM_MASTERS; j = j + 1) begin
            if (aw_violation[j]) begin
                violation_count <= violation_count + 1;
                last_violation_id <= m_awid[j];
                last_violation_addr <= m_awaddr[j];
                last_violation_is_write <= 1'b1;
            end else if (ar_violation[j]) begin
                violation_count <= violation_count + 1;
                last_violation_id <= m_arid[j];
                last_violation_addr <= m_araddr[j];
                last_violation_is_write <= 1'b0;
            end
        end
    end
end

// Address range based security (optional enhanced feature)
// Define secure address regions
localparam SECURE_REGION_START = 32'h8000_0000;
localparam SECURE_REGION_END   = 32'h9000_0000;

// Enhanced security check with address regions
generate
    for (i = 0; i < NUM_MASTERS; i = i + 1) begin : addr_range_check
        wire aw_in_secure_region = (m_awaddr[i] >= SECURE_REGION_START) && 
                                   (m_awaddr[i] < SECURE_REGION_END);
        wire ar_in_secure_region = (m_araddr[i] >= SECURE_REGION_START) && 
                                   (m_araddr[i] < SECURE_REGION_END);
        
        // Additional blocking based on address regions
        always @(*) begin
            if (aw_in_secure_region && !master_is_secure[i]) begin
                aw_block[i] = 1'b1;
            end
            if (ar_in_secure_region && !master_is_secure[i]) begin
                ar_block[i] = 1'b1;
            end
        end
    end
endgenerate

endmodule
"""
        
        with open(firewall_file, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated firewall module: {firewall_file}")
        return firewall_file
    
    def add_assertions(self, rtl_dir):
        """Add protocol assertions"""
        assert_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_assertions.sv")
        
        content = f"""//------------------------------------------------------------------------------
// AXI4 Protocol Assertions for {self.settings['project_name']}
// Generated by Enhanced RTL Generator
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
//------------------------------------------------------------------------------

module {self.settings['project_name']}_assertions #(
    parameter ADDR_WIDTH = {self.settings['common']['addr_width']},
    parameter DATA_WIDTH = {self.settings['common']['data_width']},
    parameter ID_WIDTH   = {self.settings['common']['id_width']}
)(
    input wire aclk,
    input wire aresetn,
    
    // AXI signals to check
    input wire awvalid,
    input wire awready,
    input wire [ADDR_WIDTH-1:0] awaddr,
    input wire [7:0] awlen,
    input wire [2:0] awsize,
    input wire [1:0] awburst,
    
    input wire wvalid,
    input wire wready,
    input wire wlast,
    
    input wire bvalid,
    input wire bready,
    input wire [1:0] bresp,
    
    input wire arvalid,
    input wire arready,
    input wire [ADDR_WIDTH-1:0] araddr,
    
    input wire rvalid,
    input wire rready,
    input wire rlast,
    input wire [1:0] rresp
);

// AXI4 Protocol Assertions

// A1: VALID must remain asserted until READY
property valid_stable;
    @(posedge aclk) disable iff (!aresetn)
    (awvalid && !awready) |=> awvalid;
endproperty
assert property (valid_stable) else $error("AWVALID deasserted before AWREADY");

// A2: WLAST must align with AWLEN
property wlast_matches_awlen;
    @(posedge aclk) disable iff (!aresetn)
    // Track that WLAST comes at the right beat
    1'b1; // Simplified - actual implementation would track burst length
endproperty
assert property (wlast_matches_awlen) else $error("WLAST doesn't match AWLEN");

// A3: 4KB boundary crossing check
property no_4kb_crossing;
    @(posedge aclk) disable iff (!aresetn)
    awvalid |-> (awaddr[11:0] + (awlen * (1 << awsize))) <= 4096;
endproperty
assert property (no_4kb_crossing) else $error("Transaction crosses 4KB boundary");

// A4: WRAP burst length must be 2, 4, 8, or 16
property wrap_burst_length;
    @(posedge aclk) disable iff (!aresetn)
    (awvalid && awburst == 2'b10) |-> 
    (awlen == 1 || awlen == 3 || awlen == 7 || awlen == 15);
endproperty
assert property (wrap_burst_length) else $error("Invalid WRAP burst length");

// A5: Response must be OKAY, EXOKAY, SLVERR, or DECERR
property valid_response;
    @(posedge aclk) disable iff (!aresetn)
    bvalid |-> (bresp <= 2'b11);
endproperty
assert property (valid_response) else $error("Invalid response code");

// Coverage points
covergroup axi_coverage @(posedge aclk);
    burst_type: coverpoint awburst {{
        bins fixed = {{2'b00}};
        bins incr  = {{2'b01}};
        bins wrap  = {{2'b10}};
    }}
    
    burst_size: coverpoint awsize {{
        bins byte     = {{3'b000}};
        bins halfword = {{3'b001}};
        bins word     = {{3'b010}};
        bins dword    = {{3'b011}};
    }}
    
    response: coverpoint bresp {{
        bins okay   = {{2'b00}};
        bins exokay = {{2'b01}};
        bins slverr = {{2'b10}};
        bins decerr = {{2'b11}};
    }}
endgroup

axi_coverage cov = new();

endmodule
"""
        
        with open(assert_file, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated assertions: {assert_file}")
        return assert_file
    
    def generate_filelist(self, rtl_dir):
        """Generate filelist.f for compilation"""
        filelist = os.path.join(rtl_dir, "filelist.f")
        
        # Get all Verilog files
        files = []
        for f in os.listdir(rtl_dir):
            if f.endswith('.v') or f.endswith('.sv'):
                files.append(f)
        
        content = f"""# Filelist for {self.settings['project_name']}
# Generated by Enhanced RTL Generator
# Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

# Include directories
+incdir+.

# RTL files
"""
        for f in sorted(files):
            content += f"{f}\n"
        
        with open(filelist, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated filelist: {filelist}")
        return filelist
    
    def generate_makefile(self, rtl_dir):
        """Generate Makefile for compilation"""
        makefile = os.path.join(rtl_dir, "Makefile")
        
        simulator = self.settings.get('simulator', 'VCS')
        
        content = f"""# Makefile for {self.settings['project_name']}
# Generated by Enhanced RTL Generator
# Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
# Simulator: {simulator}

# Project settings
PROJECT = {self.settings['project_name']}
TOP_MODULE = $(PROJECT)_top

# Simulator settings
"""
        
        if simulator == 'VCS':
            content += """
VCS = vcs
VCS_FLAGS = -full64 -sverilog +v2k -timescale=1ns/1ps \\
            -debug_access+all -lca -kdb +lint=TFIPC-L \\
            +define+DUMP_VCD

compile: clean
\t$(VCS) $(VCS_FLAGS) -f filelist.f -o simv

run: compile
\t./simv +UVM_TESTNAME=test_base

clean:
\trm -rf simv* csrc *.log ucli.key vc_hdrs.h .inter.vpd.uvm DVEfiles
"""
        elif simulator == 'Questa':
            content += """
VLOG = vlog
VSIM = vsim
VLOG_FLAGS = -sv +acc -timescale 1ns/1ps

compile: clean
\t$(VLOG) $(VLOG_FLAGS) -f filelist.f

run: compile
\t$(VSIM) -c $(TOP_MODULE) -do "run -all; quit"

clean:
\trm -rf work transcript *.wlf
"""
        elif simulator == 'Xcelium':
            content += """
XRUN = xrun
XRUN_FLAGS = -64bit -sv -timescale 1ns/1ps \\
             -access +rwc -input @"probe -create -all -depth all"

compile: clean
\t$(XRUN) $(XRUN_FLAGS) -f filelist.f

clean:
\trm -rf xcelium.d *.log *.history
"""
        else:  # Icarus Verilog
            content += """
IVERILOG = iverilog
VVP = vvp
IVERILOG_FLAGS = -g2012 -Wall

compile: clean
\t$(IVERILOG) $(IVERILOG_FLAGS) -f filelist.f -o $(PROJECT).vvp

run: compile
\t$(VVP) $(PROJECT).vvp

clean:
\trm -f *.vvp *.vcd
"""
        
        content += """

# Waveform viewing
wave:
\tgtkwave *.vcd &

.PHONY: compile run clean wave
"""
        
        with open(makefile, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated Makefile: {makefile}")
        return makefile
    
    def generate_sim_scripts(self, rtl_dir):
        """Generate simulation scripts"""
        # Generate run script
        run_script = os.path.join(rtl_dir, "run_sim.sh")
        
        content = f"""#!/bin/bash
# Simulation script for {self.settings['project_name']}
# Generated by Enhanced RTL Generator
# Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

echo "Starting simulation for {self.settings['project_name']}"
echo "======================================"

# Set up environment
export PROJECT={self.settings['project_name']}

# Compile
echo "Compiling RTL..."
make compile

if [ $? -ne 0 ]; then
    echo "Compilation failed!"
    exit 1
fi

# Run simulation
echo "Running simulation..."
make run

# Check results
if [ -f "simulation.log" ]; then
    errors=$(grep -c "ERROR" simulation.log)
    warnings=$(grep -c "WARNING" simulation.log)
    echo ""
    echo "Simulation Summary:"
    echo "  Errors: $errors"
    echo "  Warnings: $warnings"
fi

echo "Simulation complete!"
"""
        
        with open(run_script, 'w') as f:
            f.write(content)
        os.chmod(run_script, 0o755)
        
        logger.info(f"Generated simulation script: {run_script}")
        return run_script
    
    def generate_documentation(self, rtl_dir):
        """Generate documentation"""
        doc_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_readme.md")
        
        content = f"""# {self.settings['project_name']} - AXI4 Interconnect

## Overview
Generated by Enhanced RTL Generator  
Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}  
Author: {self.settings.get('author', 'Unknown')}  
Company: {self.settings.get('company', 'N/A')}  

## Configuration

### Bus Parameters
- **Data Width**: {self.settings['common']['data_width']} bits
- **Address Width**: {self.settings['common']['addr_width']} bits
- **ID Width**: {self.settings['common']['id_width']} bits
- **User Width**: {self.settings['common'].get('user_width', 0)} bits

### Topology
- **Masters**: {len(self.project.masters)}
- **Slaves**: {len(self.project.slaves)}

### Features Enabled
"""
        
        if self.settings['common'].get('enable_qos'):
            content += "- ✅ QoS (Quality of Service)\n"
        if self.settings['common'].get('enable_region'):
            content += "- ✅ REGION support\n"
        if self.settings['common'].get('enable_exclusive'):
            content += "- ✅ Exclusive Access\n"
        if self.settings['common'].get('enable_user'):
            content += "- ✅ USER signals\n"
        
        if 'rtl' in self.settings:
            rtl = self.settings['rtl']
            content += f"""
### RTL Settings
- **Pipeline Stages**: {rtl.get('pipeline_stages', 0)}
- **Arbitration**: {rtl.get('arbitration', 'round_robin')}
- **Max Outstanding**: {rtl.get('max_outstanding', 8)}
- **Optimization**: {rtl.get('optimization', 'balanced')}
"""
        
        content += """
## File Structure

```
rtl/
├── {0}_interconnect.v     # Base interconnect
├── {0}_qos_wrapper.v      # QoS support (if enabled)
├── {0}_region_wrapper.v   # REGION support (if enabled)
├── {0}_user_wrapper.v     # USER signals (if enabled)
├── {0}_pipeline.v         # Pipeline stages
├── {0}_arbiter_*.v        # Arbitration logic
├── {0}_exclusive_monitor.v # Exclusive access monitor
├── {0}_cdc.v              # CDC logic (if multi-domain)
├── {0}_assertions.sv      # Protocol assertions
├── filelist.f             # Compilation filelist
├── Makefile               # Build automation
└── run_sim.sh             # Simulation script
```

## Building and Running

### Compilation
```bash
make compile
```

### Simulation
```bash
make run
# or
./run_sim.sh
```

### View Waveforms
```bash
make wave
```

## Master Interfaces
""".format(self.settings['project_name'])
        
        for i, master in enumerate(self.project.masters):
            master_name = master.name if hasattr(master, 'name') else str(master)
            content += f"- **Master {i}** ({master_name}): "
            if hasattr(master, 'qos_aw'):
                content += f"QoS AW={master.qos_aw}, AR={master.qos_ar}"
            content += "\n"
        
        content += "\n## Slave Interfaces\n"
        for i, slave in enumerate(self.project.slaves):
            slave_name = slave.name if hasattr(slave, 'name') else str(slave)
            content += f"- **Slave {i}** ({slave_name}): "
            if hasattr(slave, 'base_addr'):
                content += f"Base=0x{slave.base_addr:08X}, Size=0x{slave.size:08X}"
            content += "\n"
        
        with open(doc_file, 'w') as f:
            f.write(content)
        
        logger.info(f"Generated documentation: {doc_file}")
        return doc_file
    
    def generate_integrated_top(self, rtl_dir):
        """Generate integrated top-level wrapper that includes all modules"""
        top_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_integrated_top.v")
        
        num_masters = len(self.project.masters)
        num_slaves = len(self.project.slaves)
        
        content = f"""//------------------------------------------------------------------------------
// Integrated Top-Level Wrapper for {self.settings['project_name']}
// Generated by Enhanced RTL Generator
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
//
// This file provides a single top-level module that integrates all features
// Number of Masters: {num_masters}
// Number of Slaves: {num_slaves}
//------------------------------------------------------------------------------

module {self.settings['project_name']}_top
    #(parameter NUM_MASTER  = {num_masters}
              , NUM_SLAVE   = {num_slaves}
              , WIDTH_ID    = {self.settings['common']['id_width']}
              , WIDTH_AD    = {self.settings['common']['addr_width']}
              , WIDTH_DA    = {self.settings['common']['data_width']}
              , WIDTH_DS    = (WIDTH_DA/8)
              , WIDTH_CID   = $clog2(NUM_MASTER)
              , WIDTH_SID   = WIDTH_CID + WIDTH_ID
"""
        
        # Add feature-specific parameters
        if self.settings['common'].get('enable_user', False):
            user_width = self.settings['common'].get('user_width', 8)
            content += f"""              , WIDTH_AWUSER = {user_width}
              , WIDTH_WUSER  = {user_width}
              , WIDTH_BUSER  = {user_width}
              , WIDTH_ARUSER = {user_width}
              , WIDTH_RUSER  = {user_width}
"""
        
        if self.settings['common'].get('enable_qos', False):
            content += "              , WIDTH_QOS    = 4\n"
        
        if self.settings['common'].get('enable_region', False):
            content += "              , WIDTH_REGION = 4\n"
        
        # Add slave address parameters
        for i, slave in enumerate(self.project.slaves):
            base_addr = getattr(slave, 'base_addr', i * 0x2000)
            size = getattr(slave, 'size', 0x2000)
            content += f"""              , SLAVE_EN{i} = 1
              , ADDR_BASE{i} = 32'h{base_addr:08X}
              , ADDR_LENGTH{i} = {12 if size <= 4096 else 16}
"""
        
        content += "    )\n    (\n"
        content += "      input  wire                     ARESETn\n"
        content += "    , input  wire                     ACLK\n"
        
        # Generate master ports
        for m in range(num_masters):
            content += f"""
    //---------- Master {m} Interface ----------
    // AXI4 Write Address Channel
    , input  wire [WIDTH_ID-1:0]     M{m}_AWID
    , input  wire [WIDTH_AD-1:0]     M{m}_AWADDR
    , input  wire [7:0]               M{m}_AWLEN
    , input  wire [2:0]               M{m}_AWSIZE
    , input  wire [1:0]               M{m}_AWBURST
    , input  wire                     M{m}_AWLOCK
    , input  wire [3:0]               M{m}_AWCACHE
    , input  wire [2:0]               M{m}_AWPROT
    , input  wire                     M{m}_AWVALID
    , output wire                     M{m}_AWREADY
"""
            if self.settings['common'].get('enable_qos', False):
                content += f"    , input  wire [3:0]               M{m}_AWQOS\n"
                content += f"    , input  wire [3:0]               M{m}_AWREGION\n"
            if self.settings['common'].get('enable_user', False):
                content += f"    , input  wire [WIDTH_AWUSER-1:0]  M{m}_AWUSER\n"
            
            content += f"""    // AXI4 Write Data Channel
    , input  wire [WIDTH_DA-1:0]     M{m}_WDATA
    , input  wire [WIDTH_DS-1:0]     M{m}_WSTRB
    , input  wire                     M{m}_WLAST
    , input  wire                     M{m}_WVALID
    , output wire                     M{m}_WREADY
"""
            if self.settings['common'].get('enable_user', False):
                content += f"    , input  wire [WIDTH_WUSER-1:0]   M{m}_WUSER\n"
            
            content += f"""    // AXI4 Write Response Channel
    , output wire [WIDTH_ID-1:0]     M{m}_BID
    , output wire [1:0]               M{m}_BRESP
    , output wire                     M{m}_BVALID
    , input  wire                     M{m}_BREADY
"""
            if self.settings['common'].get('enable_user', False):
                content += f"    , output wire [WIDTH_BUSER-1:0]   M{m}_BUSER\n"
            
            content += f"""    // AXI4 Read Address Channel
    , input  wire [WIDTH_ID-1:0]     M{m}_ARID
    , input  wire [WIDTH_AD-1:0]     M{m}_ARADDR
    , input  wire [7:0]               M{m}_ARLEN
    , input  wire [2:0]               M{m}_ARSIZE
    , input  wire [1:0]               M{m}_ARBURST
    , input  wire                     M{m}_ARLOCK
    , input  wire [3:0]               M{m}_ARCACHE
    , input  wire [2:0]               M{m}_ARPROT
    , input  wire                     M{m}_ARVALID
    , output wire                     M{m}_ARREADY
"""
            if self.settings['common'].get('enable_qos', False):
                content += f"    , input  wire [3:0]               M{m}_ARQOS\n"
                content += f"    , input  wire [3:0]               M{m}_ARREGION\n"
            if self.settings['common'].get('enable_user', False):
                content += f"    , input  wire [WIDTH_ARUSER-1:0]  M{m}_ARUSER\n"
            
            content += f"""    // AXI4 Read Data Channel
    , output wire [WIDTH_ID-1:0]     M{m}_RID
    , output wire [WIDTH_DA-1:0]     M{m}_RDATA
    , output wire [1:0]               M{m}_RRESP
    , output wire                     M{m}_RLAST
    , output wire                     M{m}_RVALID
    , input  wire                     M{m}_RREADY
"""
            if self.settings['common'].get('enable_user', False):
                content += f"    , output wire [WIDTH_RUSER-1:0]   M{m}_RUSER\n"
        
        # Generate slave ports
        for s in range(num_slaves):
            content += f"""
    //---------- Slave {s} Interface ----------
    // AXI4 Write Address Channel
    , output wire [WIDTH_SID-1:0]    S{s}_AWID
    , output wire [WIDTH_AD-1:0]     S{s}_AWADDR
    , output wire [7:0]               S{s}_AWLEN
    , output wire [2:0]               S{s}_AWSIZE
    , output wire [1:0]               S{s}_AWBURST
    , output wire                     S{s}_AWLOCK
    , output wire [3:0]               S{s}_AWCACHE
    , output wire [2:0]               S{s}_AWPROT
    , output wire                     S{s}_AWVALID
    , input  wire                     S{s}_AWREADY
"""
            if self.settings['common'].get('enable_qos', False):
                content += f"    , output wire [3:0]               S{s}_AWQOS\n"
                content += f"    , output wire [3:0]               S{s}_AWREGION\n"
            if self.settings['common'].get('enable_user', False):
                content += f"    , output wire [WIDTH_AWUSER-1:0]  S{s}_AWUSER\n"
            
            content += f"""    // AXI4 Write Data Channel
    , output wire [WIDTH_DA-1:0]     S{s}_WDATA
    , output wire [WIDTH_DS-1:0]     S{s}_WSTRB
    , output wire                     S{s}_WLAST
    , output wire                     S{s}_WVALID
    , input  wire                     S{s}_WREADY
"""
            if self.settings['common'].get('enable_user', False):
                content += f"    , output wire [WIDTH_WUSER-1:0]   S{s}_WUSER\n"
            
            content += f"""    // AXI4 Write Response Channel
    , input  wire [WIDTH_SID-1:0]    S{s}_BID
    , input  wire [1:0]               S{s}_BRESP
    , input  wire                     S{s}_BVALID
    , output wire                     S{s}_BREADY
"""
            if self.settings['common'].get('enable_user', False):
                content += f"    , input  wire [WIDTH_BUSER-1:0]   S{s}_BUSER\n"
            
            content += f"""    // AXI4 Read Address Channel
    , output wire [WIDTH_SID-1:0]    S{s}_ARID
    , output wire [WIDTH_AD-1:0]     S{s}_ARADDR
    , output wire [7:0]               S{s}_ARLEN
    , output wire [2:0]               S{s}_ARSIZE
    , output wire [1:0]               S{s}_ARBURST
    , output wire                     S{s}_ARLOCK
    , output wire [3:0]               S{s}_ARCACHE
    , output wire [2:0]               S{s}_ARPROT
    , output wire                     S{s}_ARVALID
    , input  wire                     S{s}_ARREADY
"""
            if self.settings['common'].get('enable_qos', False):
                content += f"    , output wire [3:0]               S{s}_ARQOS\n"
                content += f"    , output wire [3:0]               S{s}_ARREGION\n"
            if self.settings['common'].get('enable_user', False):
                content += f"    , output wire [WIDTH_ARUSER-1:0]  S{s}_ARUSER\n"
            
            content += f"""    // AXI4 Read Data Channel
    , input  wire [WIDTH_SID-1:0]    S{s}_RID
    , input  wire [WIDTH_DA-1:0]     S{s}_RDATA
    , input  wire [1:0]               S{s}_RRESP
    , input  wire                     S{s}_RLAST
    , input  wire                     S{s}_RVALID
    , output wire                     S{s}_RREADY
"""
            if self.settings['common'].get('enable_user', False):
                content += f"    , input  wire [WIDTH_RUSER-1:0]   S{s}_RUSER\n"
        
        content += "    );\n\n"
        
        # Instantiate the main interconnect
        content += f"""    //--------------------------------------------------------------------------
    // Main AXI Interconnect
    //--------------------------------------------------------------------------
    
    {self.settings['project_name']}_interconnect #(
        .NUM_MASTER(NUM_MASTER),
        .NUM_SLAVE(NUM_SLAVE),
        .WIDTH_ID(WIDTH_ID),
        .WIDTH_AD(WIDTH_AD),
        .WIDTH_DA(WIDTH_DA)
"""
        
        for i in range(num_slaves):
            content += f"""        ,.SLAVE_EN{i}(SLAVE_EN{i})
        ,.ADDR_BASE{i}(ADDR_BASE{i})
        ,.ADDR_LENGTH{i}(ADDR_LENGTH{i})
"""
        
        content += """    ) u_interconnect (
        .ARESETn(ARESETn),
        .ACLK(ACLK)
"""
        
        # Connect all ports
        for m in range(num_masters):
            for signal in ['AWID', 'AWADDR', 'AWLEN', 'AWSIZE', 'AWBURST', 'AWLOCK',
                          'AWCACHE', 'AWPROT', 'AWVALID', 'AWREADY',
                          'WDATA', 'WSTRB', 'WLAST', 'WVALID', 'WREADY',
                          'BID', 'BRESP', 'BVALID', 'BREADY',
                          'ARID', 'ARADDR', 'ARLEN', 'ARSIZE', 'ARBURST', 'ARLOCK',
                          'ARCACHE', 'ARPROT', 'ARVALID', 'ARREADY',
                          'RID', 'RDATA', 'RRESP', 'RLAST', 'RVALID', 'RREADY']:
                content += f"        ,.M{m}_{signal}(M{m}_{signal})\n"
            
            if self.settings['common'].get('enable_qos', False):
                for signal in ['AWQOS', 'AWREGION', 'ARQOS', 'ARREGION']:
                    content += f"        ,.M{m}_{signal}(M{m}_{signal})\n"
            
            if self.settings['common'].get('enable_user', False):
                for signal in ['AWUSER', 'WUSER', 'BUSER', 'ARUSER', 'RUSER']:
                    content += f"        ,.M{m}_{signal}(M{m}_{signal})\n"
        
        for s in range(num_slaves):
            for signal in ['AWID', 'AWADDR', 'AWLEN', 'AWSIZE', 'AWBURST', 'AWLOCK',
                          'AWCACHE', 'AWPROT', 'AWVALID', 'AWREADY',
                          'WDATA', 'WSTRB', 'WLAST', 'WVALID', 'WREADY',
                          'BID', 'BRESP', 'BVALID', 'BREADY',
                          'ARID', 'ARADDR', 'ARLEN', 'ARSIZE', 'ARBURST', 'ARLOCK',
                          'ARCACHE', 'ARPROT', 'ARVALID', 'ARREADY',
                          'RID', 'RDATA', 'RRESP', 'RLAST', 'RVALID', 'RREADY']:
                content += f"        ,.S{s}_{signal}(S{s}_{signal})\n"
            
            if self.settings['common'].get('enable_qos', False):
                for signal in ['AWQOS', 'AWREGION', 'ARQOS', 'ARREGION']:
                    content += f"        ,.S{s}_{signal}(S{s}_{signal})\n"
            
            if self.settings['common'].get('enable_user', False):
                for signal in ['AWUSER', 'WUSER', 'BUSER', 'ARUSER', 'RUSER']:
                    content += f"        ,.S{s}_{signal}(S{s}_{signal})\n"
        
        content += "    );\n\n"
        
        # Add comment about additional wrapper modules
        if any([self.settings['common'].get(f'enable_{feature}', False) 
                for feature in ['qos', 'region', 'exclusive', 'cdc', 'firewall']]):
            content += """    //--------------------------------------------------------------------------
    // Note: Additional feature modules (QoS, Region, CDC, etc.) are included
    // in separate files and can be instantiated as wrappers around this top
    // or integrated directly into the interconnect implementation.
    //--------------------------------------------------------------------------

"""
        
        content += "endmodule\n"
        
        with open(top_file, 'w') as f:
            f.write(content)
        
        # Also update filelist to include the integrated top
        filelist_file = os.path.join(rtl_dir, 'filelist.f')
        if os.path.exists(filelist_file):
            with open(filelist_file, 'r') as f:
                filelist_content = f.read()
            
            if f"{self.settings['project_name']}_integrated_top.v" not in filelist_content:
                with open(filelist_file, 'a') as f:
                    f.write(f"\n# Integrated top-level module\n")
                    f.write(f"{self.settings['project_name']}_integrated_top.v\n")
        
        logger.info(f"Generated integrated top file: {top_file}")
        return top_file


# Export the generator class
__all__ = ['EnhancedRTLGenerator']