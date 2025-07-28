#!/usr/bin/env python3
"""
VIP REGION Identifier Implementation Generator
Generates comprehensive REGION components for AXI4 verification
"""

import os
import datetime
from typing import Dict, List, Optional, Tuple

class VIPRegionGenerator:
    """Generator for AXI4 VIP REGION implementation"""
    
    def __init__(self, config: Dict):
        """Initialize generator with configuration"""
        self.config = config
        self.num_masters = config.get('num_masters', 2)
        self.num_slaves = config.get('num_slaves', 2)
        self.data_width = config.get('data_width', 64)
        self.addr_width = config.get('addr_width', 32)
        self.id_width = config.get('id_width', 4)
        self.region_width = 4  # AXI4 standard REGION width
        self.protocol_version = config.get('protocol', 'AXI4')
        
        # REGION configuration
        self.max_regions = 16  # 4-bit REGION field
        self.regions_per_slave = 4  # Default regions per slave
        
    def generate_all_region_components(self, output_dir: str):
        """Generate all REGION-related components"""
        # Create directory structure
        region_dir = os.path.join(output_dir, 'region')
        os.makedirs(region_dir, exist_ok=True)
        
        # Generate REGION components
        self._generate_region_decoder(region_dir)
        self._generate_region_mapper(region_dir)
        self._generate_region_controller(region_dir)
        self._generate_region_monitor(region_dir)
        self._generate_region_checker(region_dir)
        self._generate_region_configurator(region_dir)
        self._generate_region_package(region_dir)
        
    def _generate_region_decoder(self, output_dir: str):
        """Generate REGION decoder component"""
        content = f"""// AXI4 VIP REGION Decoder
// Generated: {datetime.datetime.now()}
// Decodes address to REGION mapping

`ifndef AXI4_REGION_DECODER_SV
`define AXI4_REGION_DECODER_SV

class axi4_region_decoder extends uvm_component;
    `uvm_component_utils(axi4_region_decoder)
    
    // Region mapping structure
    typedef struct {{
        bit[{self.addr_width-1}:0] start_addr;
        bit[{self.addr_width-1}:0] end_addr;
        bit[3:0] region_id;
        bit[3:0] attributes;
        string region_name;
        bit cacheable;
        bit bufferable;
        bit secure;
        bit exclusive_capable;
    }} region_map_t;
    
    // Region maps per slave
    region_map_t slave_regions[int][$];
    
    // Global region map
    region_map_t global_regions[$];
    
    // 4KB boundary tracking
    bit enforce_4kb_boundary = 1;
    bit auto_split_4kb = 1;
    
    // Region attributes
    typedef enum bit[3:0] {{
        REGION_NORMAL_MEM    = 4'b0000,
        REGION_DEVICE_MEM    = 4'b0001,
        REGION_STRONGLY_ORD  = 4'b0010,
        REGION_PERIPHERAL    = 4'b0011,
        REGION_NORMAL_NC     = 4'b0100,
        REGION_NORMAL_WT     = 4'b0101,
        REGION_NORMAL_WB     = 4'b0110,
        REGION_RESERVED      = 4'b1111
    }} region_attr_e;
    
    // Statistics
    int region_access_count[16];
    int region_violations;
    int boundary_splits;
    
    // Constructor
    function new(string name = "axi4_region_decoder", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        initialize_default_regions();
    endfunction
    
    // Initialize default region mappings
    function void initialize_default_regions();
        // Create default regions for each slave
        for (int slave_id = 0; slave_id < {self.num_slaves}; slave_id++) begin
            bit[{self.addr_width-1}:0] slave_base = slave_id * 32'h1000_0000;
            
            // Create 4 regions per slave by default
            for (int r = 0; r < {self.regions_per_slave}; r++) begin
                region_map_t region;
                region.start_addr = slave_base + (r * 32'h0400_0000);
                region.end_addr = region.start_addr + 32'h03FF_FFFF;
                region.region_id = (slave_id * 4 + r) % 16;
                region.region_name = $sformatf("Slave%0d_Region%0d", slave_id, r);
                
                // Set attributes based on region
                case (r)
                    0: begin  // Normal memory region
                        region.attributes = REGION_NORMAL_WB;
                        region.cacheable = 1;
                        region.bufferable = 1;
                        region.secure = 0;
                        region.exclusive_capable = 1;
                    end
                    1: begin  // Device memory region
                        region.attributes = REGION_DEVICE_MEM;
                        region.cacheable = 0;
                        region.bufferable = 1;
                        region.secure = 0;
                        region.exclusive_capable = 0;
                    end
                    2: begin  // Peripheral region
                        region.attributes = REGION_PERIPHERAL;
                        region.cacheable = 0;
                        region.bufferable = 0;
                        region.secure = 1;
                        region.exclusive_capable = 0;
                    end
                    3: begin  // Strongly ordered region
                        region.attributes = REGION_STRONGLY_ORD;
                        region.cacheable = 0;
                        region.bufferable = 0;
                        region.secure = 0;
                        region.exclusive_capable = 0;
                    end
                endcase
                
                add_region(slave_id, region);
            end
        end
    endfunction
    
    // Add region mapping
    function void add_region(int slave_id, region_map_t region);
        // Validate region
        if (!validate_region(region)) begin
            `uvm_error(get_type_name(), 
                      $sformatf("Invalid region: %s [%0h:%0h]", 
                               region.region_name, region.start_addr, region.end_addr))
            return;
        end
        
        // Check for 4KB boundary crossing
        if (enforce_4kb_boundary && crosses_4kb_boundary(region)) begin
            if (auto_split_4kb) begin
                split_region_at_4kb(slave_id, region);
                boundary_splits++;
            end else begin
                `uvm_error(get_type_name(), 
                          $sformatf("Region %s crosses 4KB boundary", region.region_name))
                region_violations++;
            end
        end else begin
            slave_regions[slave_id].push_back(region);
            global_regions.push_back(region);
            
            `uvm_info(get_type_name(), 
                     $sformatf("Added region: %s [%0h:%0h] ID=%0d", 
                              region.region_name, region.start_addr, 
                              region.end_addr, region.region_id), 
                     UVM_MEDIUM)
        end
    endfunction
    
    // Validate region
    function bit validate_region(region_map_t region);
        // Check address range
        if (region.end_addr <= region.start_addr) return 0;
        
        // Check region ID
        if (region.region_id > 15) return 0;
        
        // Check for overlaps with existing regions
        foreach (global_regions[i]) begin
            if (regions_overlap(region, global_regions[i])) begin
                `uvm_warning(get_type_name(), 
                            $sformatf("Region overlap detected: %s with %s", 
                                     region.region_name, global_regions[i].region_name))
                return 0;
            end
        end
        
        return 1;
    endfunction
    
    // Check if regions overlap
    function bit regions_overlap(region_map_t r1, region_map_t r2);
        return !((r1.end_addr < r2.start_addr) || (r2.end_addr < r1.start_addr));
    endfunction
    
    // Check if region crosses 4KB boundary
    function bit crosses_4kb_boundary(region_map_t region);
        bit[{self.addr_width-1}:0] start_4kb = region.start_addr & ~32'hFFF;
        bit[{self.addr_width-1}:0] end_4kb = region.end_addr & ~32'hFFF;
        return (start_4kb != end_4kb);
    endfunction
    
    // Split region at 4KB boundaries
    function void split_region_at_4kb(int slave_id, region_map_t region);
        bit[{self.addr_width-1}:0] current_addr = region.start_addr;
        bit[{self.addr_width-1}:0] next_boundary;
        int split_count = 0;
        
        while (current_addr <= region.end_addr) begin
            region_map_t split_region = region;
            split_region.start_addr = current_addr;
            
            // Calculate next 4KB boundary
            next_boundary = (current_addr & ~32'hFFF) + 32'h1000;
            
            if (next_boundary > region.end_addr) begin
                split_region.end_addr = region.end_addr;
            end else begin
                split_region.end_addr = next_boundary - 1;
            end
            
            split_region.region_name = $sformatf("%s_split%0d", 
                                                region.region_name, split_count);
            
            // Add split region
            slave_regions[slave_id].push_back(split_region);
            global_regions.push_back(split_region);
            
            `uvm_info(get_type_name(), 
                     $sformatf("Split region: %s [%0h:%0h]", 
                              split_region.region_name, 
                              split_region.start_addr, 
                              split_region.end_addr), 
                     UVM_HIGH)
            
            current_addr = next_boundary;
            split_count++;
            
            if (current_addr > region.end_addr) break;
        end
    endfunction
    
    // Decode address to REGION
    function bit[3:0] decode_region(bit[{self.addr_width-1}:0] addr, int slave_id);
        bit[3:0] region_id = 4'hF;  // Default to reserved
        
        // Search slave-specific regions first
        if (slave_regions.exists(slave_id)) begin
            foreach (slave_regions[slave_id][i]) begin
                if (addr >= slave_regions[slave_id][i].start_addr &&
                    addr <= slave_regions[slave_id][i].end_addr) begin
                    region_id = slave_regions[slave_id][i].region_id;
                    region_access_count[region_id]++;
                    
                    `uvm_info(get_type_name(), 
                             $sformatf("Address %0h decoded to region %0d (%s)", 
                                      addr, region_id, 
                                      slave_regions[slave_id][i].region_name), 
                             UVM_HIGH)
                    return region_id;
                end
            end
        end
        
        // Search global regions
        foreach (global_regions[i]) begin
            if (addr >= global_regions[i].start_addr &&
                addr <= global_regions[i].end_addr) begin
                region_id = global_regions[i].region_id;
                region_access_count[region_id]++;
                return region_id;
            end
        end
        
        `uvm_warning(get_type_name(), 
                    $sformatf("No region mapping found for address %0h", addr))
        region_violations++;
        
        return region_id;
    endfunction
    
    // Get region attributes
    function region_map_t get_region_attributes(bit[3:0] region_id);
        foreach (global_regions[i]) begin
            if (global_regions[i].region_id == region_id) begin
                return global_regions[i];
            end
        end
        
        // Return default region if not found
        region_map_t default_region;
        default_region.region_id = region_id;
        default_region.attributes = REGION_RESERVED;
        default_region.region_name = "UNMAPPED";
        return default_region;
    endfunction
    
    // Check if burst crosses region boundary
    function bit burst_crosses_region(bit[{self.addr_width-1}:0] start_addr,
                                     int burst_len, int burst_size);
        bit[{self.addr_width-1}:0] end_addr;
        bit[3:0] start_region, end_region;
        
        // Calculate end address
        end_addr = start_addr + (burst_len * (1 << burst_size));
        
        // Get regions
        start_region = decode_region(start_addr, 0);  // Simplified - needs slave_id
        end_region = decode_region(end_addr, 0);
        
        if (start_region != end_region) begin
            `uvm_warning(get_type_name(), 
                        $sformatf("Burst crosses region boundary: %0h->%0h (regions %0d->%0d)",
                                 start_addr, end_addr, start_region, end_region))
            region_violations++;
            return 1;
        end
        
        return 0;
    endfunction
    
    // Generate region map report
    function string get_region_map();
        string report = "\\n=== REGION Map ===\\n";
        
        foreach (slave_regions[slave_id]) begin
            report = {{report, $sformatf("\\nSlave %0d regions:\\n", slave_id)}};
            foreach (slave_regions[slave_id][i]) begin
                region_map_t r = slave_regions[slave_id][i];
                report = {{report, $sformatf("  %s: [%08h:%08h] ID=%0d, Attr=%0h\\n",
                                            r.region_name, r.start_addr, r.end_addr,
                                            r.region_id, r.attributes)}};
            end
        end
        
        return report;
    endfunction
    
    // Get region statistics
    function string get_region_stats();
        string stats = "\\n=== REGION Statistics ===\\n";
        
        for (int i = 0; i < 16; i++) begin
            if (region_access_count[i] > 0) begin
                stats = {{stats, $sformatf("  Region %2d: %8d accesses\\n", 
                                          i, region_access_count[i])}};
            end
        end
        
        stats = {{stats, $sformatf("\\nViolations: %0d\\n", region_violations)}};
        stats = {{stats, $sformatf("Boundary splits: %0d\\n", boundary_splits)}};
        
        return stats;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_region_map(), UVM_LOW)
        `uvm_info(get_type_name(), get_region_stats(), UVM_LOW)
    endfunction

endclass

`endif // AXI4_REGION_DECODER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_region_decoder.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_region_mapper(self, output_dir: str):
        """Generate REGION mapper component"""
        content = f"""// AXI4 VIP REGION Mapper
// Generated: {datetime.datetime.now()}
// Maps transactions to appropriate regions

`ifndef AXI4_REGION_MAPPER_SV
`define AXI4_REGION_MAPPER_SV

class axi4_region_mapper extends uvm_component;
    `uvm_component_utils(axi4_region_mapper)
    
    // Region decoder handle
    axi4_region_decoder decoder;
    
    // Mapping mode
    typedef enum {{
        STATIC_MAPPING,      // Fixed address to region mapping
        DYNAMIC_MAPPING,     // Runtime configurable mapping
        ATTRIBUTE_BASED,     // Map based on transaction attributes
        MASTER_BASED,        // Different mapping per master
        HYBRID_MAPPING       // Combination of above
    }} mapping_mode_e;
    
    mapping_mode_e mode = STATIC_MAPPING;
    
    // Master-specific region preferences
    bit[3:0] master_default_region[int];
    bit[3:0] master_allowed_regions[int][$];
    
    // Transaction to region mapping cache
    typedef struct {{
        bit[{self.addr_width-1}:0] addr;
        bit[3:0] region;
        realtime timestamp;
    }} region_cache_entry_t;
    
    region_cache_entry_t region_cache[$];
    int cache_size = 1024;
    bit enable_caching = 1;
    
    // Region remapping table
    bit[3:0] region_remap[16] = '{{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}};
    
    // Statistics
    int cache_hits;
    int cache_misses;
    int remap_count;
    
    // Constructor
    function new(string name = "axi4_region_mapper", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Map transaction to region
    function bit[3:0] map_transaction(axi4_transaction trans);
        bit[3:0] region_id;
        
        // Check cache first
        if (enable_caching) begin
            region_id = check_cache(trans.addr);
            if (region_id != 4'hF) begin
                cache_hits++;
                return apply_remap(region_id);
            end
            cache_misses++;
        end
        
        // Perform mapping based on mode
        case (mode)
            STATIC_MAPPING:    region_id = static_map(trans);
            DYNAMIC_MAPPING:   region_id = dynamic_map(trans);
            ATTRIBUTE_BASED:   region_id = attribute_map(trans);
            MASTER_BASED:      region_id = master_map(trans);
            HYBRID_MAPPING:    region_id = hybrid_map(trans);
        endcase
        
        // Update cache
        if (enable_caching) begin
            update_cache(trans.addr, region_id);
        end
        
        // Apply remapping if configured
        region_id = apply_remap(region_id);
        
        `uvm_info(get_type_name(), 
                 $sformatf("Mapped transaction addr=%0h to region=%0d", 
                          trans.addr, region_id), 
                 UVM_HIGH)
        
        return region_id;
    endfunction
    
    // Static mapping based on address
    function bit[3:0] static_map(axi4_transaction trans);
        return decoder.decode_region(trans.addr, trans.slave_id);
    endfunction
    
    // Dynamic mapping with runtime configuration
    function bit[3:0] dynamic_map(axi4_transaction trans);
        bit[3:0] base_region = static_map(trans);
        
        // Apply dynamic rules
        if (trans.lock && !decoder.get_region_attributes(base_region).exclusive_capable) begin
            // Find exclusive-capable region
            foreach (decoder.global_regions[i]) begin
                if (decoder.global_regions[i].exclusive_capable) begin
                    `uvm_info(get_type_name(), 
                             $sformatf("Remapped exclusive access to region %0d", 
                                      decoder.global_regions[i].region_id), 
                             UVM_MEDIUM)
                    return decoder.global_regions[i].region_id;
                end
            end
        end
        
        return base_region;
    endfunction
    
    // Attribute-based mapping
    function bit[3:0] attribute_map(axi4_transaction trans);
        // Map based on cache and protection attributes
        bit cacheable = trans.cache[3] || trans.cache[2];
        bit secure = trans.prot[1];
        
        // Find matching region
        foreach (decoder.global_regions[i]) begin
            if (decoder.global_regions[i].cacheable == cacheable &&
                decoder.global_regions[i].secure == secure) begin
                // Check if address is in range
                if (trans.addr >= decoder.global_regions[i].start_addr &&
                    trans.addr <= decoder.global_regions[i].end_addr) begin
                    return decoder.global_regions[i].region_id;
                end
            end
        end
        
        // Fallback to static mapping
        return static_map(trans);
    endfunction
    
    // Master-specific mapping
    function bit[3:0] master_map(axi4_transaction trans);
        int master_id = trans.master_id;
        bit[3:0] base_region = static_map(trans);
        
        // Check if master has region restrictions
        if (master_allowed_regions.exists(master_id)) begin
            // Verify region is allowed for this master
            bit allowed = 0;
            foreach (master_allowed_regions[master_id][i]) begin
                if (master_allowed_regions[master_id][i] == base_region) begin
                    allowed = 1;
                    break;
                end
            end
            
            if (!allowed) begin
                // Use master's default region
                if (master_default_region.exists(master_id)) begin
                    `uvm_warning(get_type_name(), 
                                $sformatf("Master %0d not allowed in region %0d, using default %0d",
                                         master_id, base_region, master_default_region[master_id]))
                    return master_default_region[master_id];
                end
            end
        end
        
        return base_region;
    endfunction
    
    // Hybrid mapping combining multiple strategies
    function bit[3:0] hybrid_map(axi4_transaction trans);
        bit[3:0] static_region = static_map(trans);
        bit[3:0] attr_region = attribute_map(trans);
        bit[3:0] master_region = master_map(trans);
        
        // Priority: Master restrictions > Attributes > Static
        if (master_region != static_region) begin
            return master_region;
        end else if (attr_region != static_region) begin
            return attr_region;
        end else begin
            return static_region;
        end
    endfunction
    
    // Check cache for address
    function bit[3:0] check_cache(bit[{self.addr_width-1}:0] addr);
        foreach (region_cache[i]) begin
            if (region_cache[i].addr == addr) begin
                // Move to front (LRU)
                region_cache_entry_t entry = region_cache[i];
                region_cache.delete(i);
                region_cache.push_front(entry);
                return entry.region;
            end
        end
        return 4'hF;  // Not found
    endfunction
    
    // Update cache
    function void update_cache(bit[{self.addr_width-1}:0] addr, bit[3:0] region);
        region_cache_entry_t entry;
        entry.addr = addr;
        entry.region = region;
        entry.timestamp = $realtime;
        
        region_cache.push_front(entry);
        
        // Maintain cache size
        if (region_cache.size() > cache_size) begin
            void'(region_cache.pop_back());
        end
    endfunction
    
    // Apply region remapping
    function bit[3:0] apply_remap(bit[3:0] original_region);
        bit[3:0] remapped = region_remap[original_region];
        if (remapped != original_region) begin
            remap_count++;
            `uvm_info(get_type_name(), 
                     $sformatf("Remapped region %0d -> %0d", original_region, remapped), 
                     UVM_HIGH)
        end
        return remapped;
    endfunction
    
    // Configure master region access
    function void configure_master_regions(int master_id, bit[3:0] allowed_regions[$],
                                          bit[3:0] default_region = 4'h0);
        master_allowed_regions[master_id] = allowed_regions;
        master_default_region[master_id] = default_region;
        
        `uvm_info(get_type_name(), 
                 $sformatf("Configured master %0d: allowed regions=%p, default=%0d",
                          master_id, allowed_regions, default_region), 
                 UVM_MEDIUM)
    endfunction
    
    // Set region remapping
    function void set_region_remap(bit[3:0] from_region, bit[3:0] to_region);
        region_remap[from_region] = to_region;
        `uvm_info(get_type_name(), 
                 $sformatf("Set region remap: %0d -> %0d", from_region, to_region), 
                 UVM_MEDIUM)
    endfunction
    
    // Get mapping statistics
    function string get_mapping_stats();
        string stats = "\\n=== Region Mapper Statistics ===\\n";
        
        if (enable_caching) begin
            real hit_rate = (cache_hits + cache_misses) > 0 ? 
                           real'(cache_hits) / real'(cache_hits + cache_misses) * 100.0 : 0.0;
            stats = {{stats, $sformatf("Cache hits: %0d\\n", cache_hits)}};
            stats = {{stats, $sformatf("Cache misses: %0d\\n", cache_misses)}};
            stats = {{stats, $sformatf("Cache hit rate: %0.1f%%\\n", hit_rate)}};
            stats = {{stats, $sformatf("Cache size: %0d/%0d\\n", region_cache.size(), cache_size)}};
        end
        
        stats = {{stats, $sformatf("Remap operations: %0d\\n", remap_count)}};
        stats = {{stats, $sformatf("Mapping mode: %s\\n", mode.name())}};
        
        return stats;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_mapping_stats(), UVM_LOW)
    endfunction

endclass

`endif // AXI4_REGION_MAPPER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_region_mapper.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_region_controller(self, output_dir: str):
        """Generate REGION controller component"""
        content = f"""// AXI4 VIP REGION Controller
// Generated: {datetime.datetime.now()}
// Controls region-based access and policies

`ifndef AXI4_REGION_CONTROLLER_SV
`define AXI4_REGION_CONTROLLER_SV

class axi4_region_controller extends uvm_component;
    `uvm_component_utils(axi4_region_controller)
    
    // Region decoder and mapper handles
    axi4_region_decoder decoder;
    axi4_region_mapper mapper;
    
    // Region access control
    typedef struct {{
        bit read_enable;
        bit write_enable;
        bit exclusive_enable;
        bit secure_only;
        int max_outstanding;
        int current_outstanding;
        bit[3:0] allowed_masters[$];
        bit[3:0] priority_level;
    }} region_access_control_t;
    
    region_access_control_t region_controls[16];
    
    // Region state tracking
    typedef enum {{
        REGION_IDLE,
        REGION_ACTIVE,
        REGION_BUSY,
        REGION_LOCKED,
        REGION_ERROR
    }} region_state_e;
    
    region_state_e region_states[16];
    
    // Exclusive access tracking
    typedef struct {{
        bit valid;
        bit[{self.id_width-1}:0] id;
        int master_id;
        bit[{self.addr_width-1}:0] addr;
        int size;
        realtime lock_time;
    }} exclusive_monitor_t;
    
    exclusive_monitor_t exclusive_monitors[16];
    
    // Region transition control
    bit allow_cross_region_burst = 0;
    bit enforce_region_ordering = 1;
    bit enable_region_protection = 1;
    
    // Statistics
    int region_access_granted[16];
    int region_access_denied[16];
    int exclusive_success[16];
    int exclusive_fail[16];
    
    // Constructor
    function new(string name = "axi4_region_controller", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        initialize_region_controls();
    endfunction
    
    // Initialize region controls
    function void initialize_region_controls();
        for (int i = 0; i < 16; i++) begin
            region_controls[i].read_enable = 1;
            region_controls[i].write_enable = 1;
            region_controls[i].exclusive_enable = (i < 8);  // Lower regions support exclusive
            region_controls[i].secure_only = (i >= 12);     // High regions secure only
            region_controls[i].max_outstanding = 16;
            region_controls[i].current_outstanding = 0;
            region_controls[i].priority_level = i / 4;      // 4 priority levels
            
            region_states[i] = REGION_IDLE;
        end
    endfunction
    
    // Check region access permission
    function bit check_region_access(axi4_transaction trans, bit[3:0] region_id);
        region_access_control_t ctrl = region_controls[region_id];
        bit granted = 1;
        string denial_reason = "";
        
        // Check basic read/write permission
        if (trans.is_write && !ctrl.write_enable) begin
            granted = 0;
            denial_reason = "Write not permitted";
        end else if (!trans.is_write && !ctrl.read_enable) begin
            granted = 0;
            denial_reason = "Read not permitted";
        end
        
        // Check exclusive access permission
        if (trans.lock && !ctrl.exclusive_enable) begin
            granted = 0;
            denial_reason = "Exclusive access not supported";
        end
        
        // Check security
        if (ctrl.secure_only && !trans.prot[1]) begin
            granted = 0;
            denial_reason = "Non-secure access to secure region";
        end
        
        // Check master permission
        if (ctrl.allowed_masters.size() > 0) begin
            bit master_allowed = 0;
            foreach (ctrl.allowed_masters[i]) begin
                if (ctrl.allowed_masters[i] == trans.master_id) begin
                    master_allowed = 1;
                    break;
                end
            end
            if (!master_allowed) begin
                granted = 0;
                denial_reason = $sformatf("Master %0d not allowed", trans.master_id);
            end
        end
        
        // Check outstanding limit
        if (ctrl.current_outstanding >= ctrl.max_outstanding) begin
            granted = 0;
            denial_reason = "Outstanding transaction limit reached";
        end
        
        // Update statistics
        if (granted) begin
            region_access_granted[region_id]++;
            ctrl.current_outstanding++;
            region_controls[region_id] = ctrl;
        end else begin
            region_access_denied[region_id]++;
            `uvm_warning(get_type_name(), 
                        $sformatf("Region %0d access denied: %s", region_id, denial_reason))
        end
        
        return granted;
    endfunction
    
    // Process exclusive access
    function bit process_exclusive_access(axi4_transaction trans, bit[3:0] region_id);
        if (!trans.lock) return 1;  // Non-exclusive always succeeds
        
        if (trans.is_write) begin
            // Exclusive write - check monitor
            return check_exclusive_write(trans, region_id);
        end else begin
            // Exclusive read - set monitor
            set_exclusive_monitor(trans, region_id);
            return 1;
        end
    endfunction
    
    // Set exclusive monitor
    function void set_exclusive_monitor(axi4_transaction trans, bit[3:0] region_id);
        exclusive_monitor_t monitor;
        monitor.valid = 1;
        monitor.id = trans.id;
        monitor.master_id = trans.master_id;
        monitor.addr = trans.addr;
        monitor.size = trans.size;
        monitor.lock_time = $realtime;
        
        exclusive_monitors[region_id] = monitor;
        
        `uvm_info(get_type_name(), 
                 $sformatf("Set exclusive monitor: Region=%0d, Master=%0d, Addr=%0h",
                          region_id, trans.master_id, trans.addr), 
                 UVM_MEDIUM)
    endfunction
    
    // Check exclusive write
    function bit check_exclusive_write(axi4_transaction trans, bit[3:0] region_id);
        exclusive_monitor_t monitor = exclusive_monitors[region_id];
        bit success = 0;
        
        if (monitor.valid &&
            monitor.id == trans.id &&
            monitor.master_id == trans.master_id &&
            monitor.addr == trans.addr &&
            monitor.size == trans.size) begin
            // Exclusive success
            success = 1;
            exclusive_success[region_id]++;
            
            // Clear monitor
            exclusive_monitors[region_id].valid = 0;
            
            `uvm_info(get_type_name(), 
                     $sformatf("Exclusive write success: Region=%0d, Master=%0d",
                              region_id, trans.master_id), 
                     UVM_MEDIUM)
        end else begin
            // Exclusive fail
            exclusive_fail[region_id]++;
            
            `uvm_info(get_type_name(), 
                     $sformatf("Exclusive write fail: Region=%0d, Master=%0d",
                              region_id, trans.master_id), 
                     UVM_MEDIUM)
        end
        
        return success;
    endfunction
    
    // Update region state
    function void update_region_state(bit[3:0] region_id, region_state_e new_state);
        region_state_e old_state = region_states[region_id];
        region_states[region_id] = new_state;
        
        `uvm_info(get_type_name(), 
                 $sformatf("Region %0d state: %s -> %s", 
                          region_id, old_state.name(), new_state.name()), 
                 UVM_HIGH)
    endfunction
    
    // Handle burst crossing regions
    function bit handle_cross_region_burst(axi4_transaction trans);
        bit[{self.addr_width-1}:0] start_addr = trans.addr;
        bit[{self.addr_width-1}:0] end_addr;
        bit[3:0] start_region, end_region;
        
        // Calculate end address
        case (trans.burst)
            2'b00: end_addr = start_addr;  // FIXED
            2'b01: begin  // INCR
                end_addr = start_addr + (trans.len * (1 << trans.size));
            end
            2'b10: begin  // WRAP
                int wrap_size = (trans.len + 1) * (1 << trans.size);
                end_addr = start_addr + wrap_size - 1;
            end
        endcase
        
        // Get regions
        start_region = mapper.map_transaction(trans);
        
        // Create temp transaction for end address check
        axi4_transaction end_trans = trans;
        end_trans.addr = end_addr;
        end_region = mapper.map_transaction(end_trans);
        
        if (start_region != end_region) begin
            if (allow_cross_region_burst) begin
                `uvm_info(get_type_name(), 
                         $sformatf("Allowing burst across regions %0d -> %0d",
                                  start_region, end_region), 
                         UVM_MEDIUM)
                return 1;
            end else begin
                `uvm_error(get_type_name(), 
                          $sformatf("Burst not allowed to cross regions %0d -> %0d",
                                   start_region, end_region))
                return 0;
            end
        end
        
        return 1;
    endfunction
    
    // Complete transaction in region
    function void complete_region_transaction(axi4_transaction trans, bit[3:0] region_id);
        if (region_controls[region_id].current_outstanding > 0) begin
            region_controls[region_id].current_outstanding--;
        end
        
        // Update state if no more outstanding
        if (region_controls[region_id].current_outstanding == 0) begin
            update_region_state(region_id, REGION_IDLE);
        end
    endfunction
    
    // Configure region access control
    function void configure_region_access(bit[3:0] region_id, 
                                         region_access_control_t config);
        region_controls[region_id] = config;
        
        `uvm_info(get_type_name(), 
                 $sformatf("Configured region %0d: R=%0b, W=%0b, Excl=%0b, Secure=%0b",
                          region_id, config.read_enable, config.write_enable,
                          config.exclusive_enable, config.secure_only), 
                 UVM_MEDIUM)
    endfunction
    
    // Lock region for exclusive use
    function bit lock_region(bit[3:0] region_id, int master_id);
        if (region_states[region_id] == REGION_IDLE ||
            region_states[region_id] == REGION_ACTIVE) begin
            update_region_state(region_id, REGION_LOCKED);
            
            // Temporarily restrict to locking master
            region_controls[region_id].allowed_masters = '{master_id};
            
            `uvm_info(get_type_name(), 
                     $sformatf("Region %0d locked by master %0d", region_id, master_id), 
                     UVM_MEDIUM)
            return 1;
        end
        
        return 0;
    endfunction
    
    // Unlock region
    function void unlock_region(bit[3:0] region_id);
        if (region_states[region_id] == REGION_LOCKED) begin
            update_region_state(region_id, REGION_IDLE);
            
            // Clear master restrictions
            region_controls[region_id].allowed_masters.delete();
            
            `uvm_info(get_type_name(), 
                     $sformatf("Region %0d unlocked", region_id), 
                     UVM_MEDIUM)
        end
    endfunction
    
    // Get region status
    function string get_region_status();
        string status = "\\n=== Region Controller Status ===\\n";
        
        for (int i = 0; i < 16; i++) begin
            if (region_states[i] != REGION_IDLE || region_access_granted[i] > 0 ||
                region_access_denied[i] > 0) begin
                status = {{status, $sformatf("\\nRegion %2d:\\n", i)}};
                status = {{status, $sformatf("  State: %s\\n", region_states[i].name())}};
                status = {{status, $sformatf("  Outstanding: %0d/%0d\\n",
                                            region_controls[i].current_outstanding,
                                            region_controls[i].max_outstanding)}};
                status = {{status, $sformatf("  Access granted: %0d, denied: %0d\\n",
                                            region_access_granted[i],
                                            region_access_denied[i])}};
                
                if (exclusive_success[i] > 0 || exclusive_fail[i] > 0) begin
                    status = {{status, $sformatf("  Exclusive: success=%0d, fail=%0d\\n",
                                                exclusive_success[i],
                                                exclusive_fail[i])}};
                end
                
                if (exclusive_monitors[i].valid) begin
                    status = {{status, $sformatf("  Active exclusive monitor: Master=%0d, Addr=%0h\\n",
                                                exclusive_monitors[i].master_id,
                                                exclusive_monitors[i].addr)}};
                end
            end
        end
        
        return status;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_region_status(), UVM_LOW)
    endfunction

endclass

`endif // AXI4_REGION_CONTROLLER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_region_controller.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_region_monitor(self, output_dir: str):
        """Generate REGION monitor component"""
        content = f"""// AXI4 VIP REGION Monitor
// Generated: {datetime.datetime.now()}
// Monitors region usage and compliance

`ifndef AXI4_REGION_MONITOR_SV
`define AXI4_REGION_MONITOR_SV

class axi4_region_monitor extends uvm_monitor;
    `uvm_component_utils(axi4_region_monitor)
    
    // Virtual interface
    virtual axi4_if vif;
    
    // Analysis ports
    uvm_analysis_port #(axi4_region_event) region_ap;
    
    // Component handles
    axi4_region_decoder decoder;
    axi4_region_controller controller;
    
    // Region tracking
    typedef struct {{
        int access_count;
        int violation_count;
        real total_bandwidth;
        real peak_bandwidth;
        int outstanding_count;
        realtime last_access_time;
        int unique_masters[$];
    }} region_stats_t;
    
    region_stats_t region_stats[16];
    
    // Transaction tracking for bandwidth calculation
    typedef struct {{
        realtime start_time;
        realtime end_time;
        int bytes_transferred;
        bit[3:0] region_id;
    }} bandwidth_sample_t;
    
    bandwidth_sample_t bandwidth_samples[$];
    realtime bandwidth_window = 1us;
    
    // Region consistency checking
    bit check_region_consistency = 1;
    bit check_4kb_compliance = 1;
    bit check_exclusive_regions = 1;
    
    // Violation tracking
    int consistency_violations;
    int boundary_violations;
    int protection_violations;
    
    // Constructor
    function new(string name = "axi4_region_monitor", uvm_component parent = null);
        super.new(name, parent);
        region_ap = new("region_ap", this);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
    endfunction
    
    // Run phase
    task run_phase(uvm_phase phase);
        fork
            monitor_aw_channel();
            monitor_ar_channel();
            monitor_responses();
            calculate_bandwidth();
            check_region_violations();
        join
    endtask
    
    // Monitor write address channel
    task monitor_aw_channel();
        forever begin
            @(posedge vif.clk);
            
            if (vif.awvalid && vif.awready) begin
                axi4_region_event evt = new();
                evt.addr = vif.awaddr;
                evt.region = vif.awregion;
                evt.id = vif.awid;
                evt.len = vif.awlen;
                evt.size = vif.awsize;
                evt.burst = vif.awburst;
                evt.master_id = get_master_from_id(vif.awid);
                evt.is_write = 1;
                evt.timestamp = $realtime;
                
                // Process region event
                process_region_event(evt);
                
                // Send to analysis port
                region_ap.write(evt);
            end
        end
    endtask
    
    // Monitor read address channel
    task monitor_ar_channel();
        forever begin
            @(posedge vif.clk);
            
            if (vif.arvalid && vif.arready) begin
                axi4_region_event evt = new();
                evt.addr = vif.araddr;
                evt.region = vif.arregion;
                evt.id = vif.arid;
                evt.len = vif.arlen;
                evt.size = vif.arsize;
                evt.burst = vif.arburst;
                evt.master_id = get_master_from_id(vif.arid);
                evt.is_write = 0;
                evt.timestamp = $realtime;
                
                // Process region event
                process_region_event(evt);
                
                // Send to analysis port
                region_ap.write(evt);
            end
        end
    endtask
    
    // Process region event
    function void process_region_event(axi4_region_event evt);
        bit[3:0] decoded_region;
        bit[3:0] actual_region = evt.region;
        
        // Update statistics
        update_region_stats(actual_region, evt);
        
        // Decode expected region from address
        if (decoder != null) begin
            decoded_region = decoder.decode_region(evt.addr, 0);  // Simplified
            
            // Check consistency
            if (check_region_consistency && decoded_region != actual_region) begin
                `uvm_warning(get_type_name(), 
                            $sformatf("Region mismatch: addr=%0h, expected=%0d, actual=%0d",
                                     evt.addr, decoded_region, actual_region))
                consistency_violations++;
                region_stats[actual_region].violation_count++;
            end
        end
        
        // Check 4KB compliance
        if (check_4kb_compliance) begin
            check_4kb_boundary_compliance(evt);
        end
        
        // Check exclusive access regions
        if (check_exclusive_regions && evt.lock) begin
            check_exclusive_region_compliance(evt);
        end
        
        // Track bandwidth
        track_bandwidth(evt);
    endfunction
    
    // Update region statistics
    function void update_region_stats(bit[3:0] region_id, axi4_region_event evt);
        region_stats[region_id].access_count++;
        region_stats[region_id].last_access_time = evt.timestamp;
        
        // Track unique masters
        if (!(evt.master_id inside {region_stats[region_id].unique_masters})) begin
            region_stats[region_id].unique_masters.push_back(evt.master_id);
        end
        
        // Update outstanding count
        if (evt.is_write) begin
            region_stats[region_id].outstanding_count++;
        end
    endfunction
    
    // Check 4KB boundary compliance
    function void check_4kb_boundary_compliance(axi4_region_event evt);
        bit[{self.addr_width-1}:0] start_addr = evt.addr;
        bit[{self.addr_width-1}:0] end_addr;
        int bytes_per_beat = 1 << evt.size;
        
        // Calculate end address
        case (evt.burst)
            2'b00: end_addr = start_addr;  // FIXED
            2'b01: end_addr = start_addr + (evt.len * bytes_per_beat);  // INCR
            2'b10: begin  // WRAP
                int wrap_size = (evt.len + 1) * bytes_per_beat;
                end_addr = start_addr + wrap_size - 1;
            end
        endcase
        
        // Check if crosses 4KB boundary
        if ((start_addr & ~32'hFFF) != (end_addr & ~32'hFFF)) begin
            // Check if REGION changes at boundary
            bit[{self.addr_width-1}:0] boundary_addr = (start_addr & ~32'hFFF) + 32'h1000;
            bit[3:0] boundary_region = decoder.decode_region(boundary_addr, 0);
            
            if (boundary_region == evt.region) begin
                `uvm_error(get_type_name(), 
                          $sformatf("Transaction crosses 4KB boundary without REGION change: " +
                                   "addr=%0h, len=%0d, region=%0d",
                                   evt.addr, evt.len, evt.region))
                boundary_violations++;
                region_stats[evt.region].violation_count++;
            end
        end
    endfunction
    
    // Check exclusive region compliance
    function void check_exclusive_region_compliance(axi4_region_event evt);
        axi4_region_decoder::region_map_t region_info;
        
        if (decoder != null) begin
            region_info = decoder.get_region_attributes(evt.region);
            
            if (!region_info.exclusive_capable) begin
                `uvm_error(get_type_name(), 
                          $sformatf("Exclusive access to non-exclusive region %0d", evt.region))
                protection_violations++;
                region_stats[evt.region].violation_count++;
            end
        end
    endfunction
    
    // Track bandwidth per region
    function void track_bandwidth(axi4_region_event evt);
        bandwidth_sample_t sample;
        sample.start_time = evt.timestamp;
        sample.region_id = evt.region;
        sample.bytes_transferred = (evt.len + 1) * (1 << evt.size);
        
        bandwidth_samples.push_back(sample);
        
        // Cleanup old samples
        while (bandwidth_samples.size() > 0 && 
               bandwidth_samples[0].start_time < ($realtime - bandwidth_window)) begin
            void'(bandwidth_samples.pop_front());
        end
    endfunction
    
    // Monitor responses for completion
    task monitor_responses();
        forever begin
            @(posedge vif.clk);
            
            // Monitor write response
            if (vif.bvalid && vif.bready) begin
                // Update outstanding count
                // Need to track which region this belongs to
            end
            
            // Monitor read response
            if (vif.rvalid && vif.rready && vif.rlast) begin
                // Update outstanding count
            end
        end
    endtask
    
    // Calculate bandwidth periodically
    task calculate_bandwidth();
        forever begin
            #100ns;  // Calculate every 100ns
            
            // Calculate per-region bandwidth
            real region_bandwidth[16];
            
            foreach (bandwidth_samples[i]) begin
                real time_in_window = $realtime - bandwidth_samples[i].start_time;
                if (time_in_window > 0) begin
                    region_bandwidth[bandwidth_samples[i].region_id] += 
                        real'(bandwidth_samples[i].bytes_transferred) / time_in_window;
                end
            end
            
            // Update statistics
            for (int i = 0; i < 16; i++) begin
                if (region_bandwidth[i] > 0) begin
                    region_stats[i].total_bandwidth += region_bandwidth[i];
                    if (region_bandwidth[i] > region_stats[i].peak_bandwidth) begin
                        region_stats[i].peak_bandwidth = region_bandwidth[i];
                    end
                end
            end
        end
    endtask
    
    // Check for region violations
    task check_region_violations();
        forever begin
            #1us;  // Check every microsecond
            
            // Check for inactive regions
            foreach (region_stats[i]) begin
                if (region_stats[i].access_count > 0) begin
                    realtime idle_time = $realtime - region_stats[i].last_access_time;
                    
                    if (idle_time > 10us && region_stats[i].outstanding_count > 0) begin
                        `uvm_warning(get_type_name(), 
                                    $sformatf("Region %0d has outstanding transactions but no activity for %0.1fus",
                                             i, idle_time / 1000.0))
                    end
                end
            end
        end
    endtask
    
    // Get master ID from transaction ID
    function int get_master_from_id(bit[{self.id_width-1}:0] id);
        // Simple mapping - upper bits indicate master
        return id[{self.id_width-1}:{self.id_width-2}];
    endfunction
    
    // Generate region report
    function string get_region_report();
        string report = "\\n=== Region Monitor Report ===\\n";
        
        for (int i = 0; i < 16; i++) begin
            if (region_stats[i].access_count > 0) begin
                report = {{report, $sformatf("\\nRegion %2d:\\n", i)}};
                report = {{report, $sformatf("  Accesses: %0d\\n", region_stats[i].access_count)}};
                report = {{report, $sformatf("  Violations: %0d\\n", region_stats[i].violation_count)}};
                report = {{report, $sformatf("  Peak bandwidth: %0.2f MB/s\\n", 
                                            region_stats[i].peak_bandwidth / 1e6)}};
                report = {{report, $sformatf("  Unique masters: %0d (%p)\\n",
                                            region_stats[i].unique_masters.size(),
                                            region_stats[i].unique_masters)}};
            end
        end
        
        report = {{report, $sformatf("\\nViolation Summary:\\n")}};
        report = {{report, $sformatf("  Consistency violations: %0d\\n", consistency_violations)}};
        report = {{report, $sformatf("  Boundary violations: %0d\\n", boundary_violations)}};
        report = {{report, $sformatf("  Protection violations: %0d\\n", protection_violations)}};
        
        return report;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_region_report(), UVM_LOW)
    endfunction

endclass

// Region event class
class axi4_region_event extends uvm_sequence_item;
    `uvm_object_utils(axi4_region_event)
    
    bit[{self.addr_width-1}:0] addr;
    bit[3:0] region;
    bit[{self.id_width-1}:0] id;
    bit[7:0] len;
    bit[2:0] size;
    bit[1:0] burst;
    bit lock;
    int master_id;
    bit is_write;
    realtime timestamp;
    
    function new(string name = "axi4_region_event");
        super.new(name);
    endfunction
    
    function string convert2string();
        return $sformatf("Region Event: addr=%0h, region=%0d, master=%0d, %s",
                        addr, region, master_id, is_write ? "Write" : "Read");
    endfunction

endclass

`endif // AXI4_REGION_MONITOR_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_region_monitor.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_region_checker(self, output_dir: str):
        """Generate REGION checker component"""
        content = f"""// AXI4 VIP REGION Checker
// Generated: {datetime.datetime.now()}
// Checks REGION signal compliance with AXI4 specification

`ifndef AXI4_REGION_CHECKER_SV
`define AXI4_REGION_CHECKER_SV

class axi4_region_checker extends uvm_component;
    `uvm_component_utils(axi4_region_checker)
    
    // Checker configuration
    bit enable_protocol_checks = 1;
    bit enable_consistency_checks = 1;
    bit enable_performance_checks = 1;
    bit strict_4kb_checking = 1;
    
    // Check results
    typedef struct {{
        int total_checks;
        int passed;
        int failed;
        int warnings;
        string last_failure_msg;
        realtime last_failure_time;
    }} check_stats_t;
    
    check_stats_t protocol_stats;
    check_stats_t consistency_stats;
    check_stats_t performance_stats;
    
    // Specific check counters
    int region_constant_violations;
    int region_4kb_violations;
    int region_wrap_violations;
    int region_exclusive_violations;
    int region_ordering_violations;
    
    // Transaction tracking for checks
    typedef struct {{
        bit[{self.addr_width-1}:0] start_addr;
        bit[3:0] region;
        bit[7:0] len;
        bit[2:0] size;
        bit[1:0] burst;
        bit active;
        int beats_remaining;
        bit[3:0] expected_region;
    }} tracked_burst_t;
    
    tracked_burst_t active_bursts[bit[{self.id_width-1}:0]];
    
    // Constructor
    function new(string name = "axi4_region_checker", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Check transaction
    function void check_transaction(axi4_transaction trans);
        if (enable_protocol_checks) begin
            check_protocol_compliance(trans);
        end
        
        if (enable_consistency_checks) begin
            check_region_consistency(trans);
        end
        
        if (enable_performance_checks) begin
            check_region_performance(trans);
        end
        
        // Track burst for multi-beat checks
        if (trans.len > 0) begin
            track_burst(trans);
        end
    endfunction
    
    // Protocol compliance checks
    function void check_protocol_compliance(axi4_transaction trans);
        protocol_stats.total_checks++;
        bit check_passed = 1;
        
        // Check 1: REGION must remain constant throughout burst
        if (active_bursts.exists(trans.id)) begin
            if (active_bursts[trans.id].active && 
                active_bursts[trans.id].region != trans.region) begin
                `uvm_error("REGION_PROTOCOL", 
                          $sformatf("REGION changed during burst: ID=%0h, was %0d, now %0d",
                                   trans.id, active_bursts[trans.id].region, trans.region))
                region_constant_violations++;
                check_passed = 0;
            end
        end
        
        // Check 2: REGION consistency at 4KB boundaries
        if (strict_4kb_checking) begin
            if (!check_4kb_region_consistency(trans)) begin
                check_passed = 0;
            end
        end
        
        // Check 3: WRAP burst must not change REGION
        if (trans.burst == 2'b10) begin  // WRAP
            if (!check_wrap_region_consistency(trans)) begin
                check_passed = 0;
            end
        end
        
        // Check 4: Exclusive access region rules
        if (trans.lock) begin
            if (!check_exclusive_region_rules(trans)) begin
                check_passed = 0;
            end
        end
        
        // Update statistics
        if (check_passed) begin
            protocol_stats.passed++;
        end else begin
            protocol_stats.failed++;
            protocol_stats.last_failure_time = $realtime;
        end
    endfunction
    
    // Check 4KB boundary region consistency
    function bit check_4kb_region_consistency(axi4_transaction trans);
        bit[{self.addr_width-1}:0] start_addr = trans.addr;
        bit[{self.addr_width-1}:0] end_addr;
        int bytes_per_beat = 1 << trans.size;
        
        // Calculate end address
        case (trans.burst)
            2'b00: end_addr = start_addr;  // FIXED
            2'b01: begin  // INCR
                end_addr = start_addr + (trans.len * bytes_per_beat);
            end
            2'b10: begin  // WRAP
                int wrap_size = (trans.len + 1) * bytes_per_beat;
                end_addr = start_addr + wrap_size - 1;
            end
        endcase
        
        // Check if crosses 4KB boundary
        bit[{self.addr_width-1}:0] start_4kb = start_addr & ~32'hFFF;
        bit[{self.addr_width-1}:0] end_4kb = end_addr & ~32'hFFF;
        
        if (start_4kb != end_4kb) begin
            // For each 4KB boundary crossed, REGION should be consistent
            bit[{self.addr_width-1}:0] current_4kb = start_4kb;
            
            while (current_4kb < end_4kb) begin
                current_4kb += 32'h1000;
                
                // In strict mode, REGION must be same across boundary
                if (trans.region != get_expected_region_at_address(current_4kb)) begin
                    `uvm_error("REGION_4KB", 
                              $sformatf("REGION not consistent at 4KB boundary %0h: " +
                                       "transaction region=%0d",
                                       current_4kb, trans.region))
                    region_4kb_violations++;
                    return 0;
                end
            end
        end
        
        return 1;
    endfunction
    
    // Check WRAP burst region consistency
    function bit check_wrap_region_consistency(axi4_transaction trans);
        if (trans.burst != 2'b10) return 1;  // Not WRAP
        
        bit[{self.addr_width-1}:0] start_addr = trans.addr;
        int bytes_per_beat = 1 << trans.size;
        int wrap_size = (trans.len + 1) * bytes_per_beat;
        bit[{self.addr_width-1}:0] wrap_boundary = (start_addr / wrap_size) * wrap_size;
        
        // All addresses in WRAP burst should have same REGION
        for (int beat = 0; beat <= trans.len; beat++) begin
            bit[{self.addr_width-1}:0] beat_addr = start_addr + (beat * bytes_per_beat);
            if (beat_addr >= wrap_boundary + wrap_size) begin
                beat_addr = wrap_boundary + (beat_addr - (wrap_boundary + wrap_size));
            end
            
            bit[3:0] expected_region = get_expected_region_at_address(beat_addr);
            if (expected_region != trans.region) begin
                `uvm_error("REGION_WRAP", 
                          $sformatf("WRAP burst spans multiple regions: addr=%0h, region=%0d, " +
                                   "but beat %0d expects region %0d",
                                   trans.addr, trans.region, beat, expected_region))
                region_wrap_violations++;
                return 0;
            end
        end
        
        return 1;
    endfunction
    
    // Check exclusive access region rules
    function bit check_exclusive_region_rules(axi4_transaction trans);
        // Exclusive accesses should use appropriate regions
        bit[3:0] region_attr = get_region_attributes(trans.region);
        
        // Check if region supports exclusive access
        if (!is_exclusive_capable_region(trans.region)) begin
            `uvm_warning("REGION_EXCLUSIVE", 
                        $sformatf("Exclusive access to non-exclusive region %0d", trans.region))
            region_exclusive_violations++;
            protocol_stats.warnings++;
            // This is a warning, not an error
            return 1;
        end
        
        return 1;
    endfunction
    
    // Region consistency checks
    function void check_region_consistency(axi4_transaction trans);
        consistency_stats.total_checks++;
        bit check_passed = 1;
        
        // Check 1: Region matches address mapping
        bit[3:0] expected_region = get_expected_region_at_address(trans.addr);
        if (trans.region != expected_region) begin
            `uvm_warning("REGION_CONSISTENCY", 
                        $sformatf("Region mismatch: addr=%0h, actual=%0d, expected=%0d",
                                 trans.addr, trans.region, expected_region))
            consistency_stats.warnings++;
        end
        
        // Check 2: Master using allowed regions
        if (!is_master_allowed_in_region(trans.master_id, trans.region)) begin
            `uvm_error("REGION_CONSISTENCY", 
                      $sformatf("Master %0d not allowed in region %0d",
                               trans.master_id, trans.region))
            check_passed = 0;
        end
        
        // Check 3: Security consistency
        if (!check_security_consistency(trans)) begin
            check_passed = 0;
        end
        
        // Update statistics
        if (check_passed) begin
            consistency_stats.passed++;
        end else begin
            consistency_stats.failed++;
            consistency_stats.last_failure_time = $realtime;
        end
    endfunction
    
    // Check security consistency
    function bit check_security_consistency(axi4_transaction trans);
        bit region_secure = is_secure_region(trans.region);
        bit trans_secure = trans.prot[1];
        
        if (region_secure && !trans_secure) begin
            `uvm_error("REGION_SECURITY", 
                      $sformatf("Non-secure access to secure region %0d", trans.region))
            return 0;
        end
        
        return 1;
    endfunction
    
    // Performance-related checks
    function void check_region_performance(axi4_transaction trans);
        performance_stats.total_checks++;
        bit check_passed = 1;
        
        // Check 1: Optimal region selection for burst
        if (trans.len > 15) begin  // Long burst
            if (!is_optimal_region_for_burst(trans)) begin
                `uvm_info("REGION_PERFORMANCE", 
                         $sformatf("Sub-optimal region %0d selected for long burst", 
                                  trans.region), 
                         UVM_HIGH)
                performance_stats.warnings++;
            end
        end
        
        // Check 2: Region ordering for QoS
        if (!check_region_qos_ordering(trans)) begin
            region_ordering_violations++;
            performance_stats.warnings++;
        end
        
        if (check_passed) begin
            performance_stats.passed++;
        end
    endfunction
    
    // Track burst for multi-beat checking
    function void track_burst(axi4_transaction trans);
        tracked_burst_t burst;
        burst.start_addr = trans.addr;
        burst.region = trans.region;
        burst.len = trans.len;
        burst.size = trans.size;
        burst.burst = trans.burst;
        burst.active = 1;
        burst.beats_remaining = trans.len + 1;
        burst.expected_region = trans.region;
        
        active_bursts[trans.id] = burst;
    endfunction
    
    // Update burst tracking
    function void update_burst_tracking(bit[{self.id_width-1}:0] id);
        if (active_bursts.exists(id)) begin
            active_bursts[id].beats_remaining--;
            if (active_bursts[id].beats_remaining <= 0) begin
                active_bursts[id].active = 0;
            end
        end
    endfunction
    
    // Helper functions (simplified implementations)
    function bit[3:0] get_expected_region_at_address(bit[{self.addr_width-1}:0] addr);
        // Simplified region mapping
        return addr[31:28];  // Use upper 4 bits as region
    endfunction
    
    function bit[3:0] get_region_attributes(bit[3:0] region);
        // Return region attributes (simplified)
        return region;
    endfunction
    
    function bit is_exclusive_capable_region(bit[3:0] region);
        // Regions 0-7 support exclusive access
        return (region < 8);
    endfunction
    
    function bit is_master_allowed_in_region(int master_id, bit[3:0] region);
        // All masters allowed in all regions (simplified)
        return 1;
    endfunction
    
    function bit is_secure_region(bit[3:0] region);
        // Regions 12-15 are secure
        return (region >= 12);
    endfunction
    
    function bit is_optimal_region_for_burst(axi4_transaction trans);
        // Check if region is optimal for burst characteristics
        return 1;  // Simplified
    endfunction
    
    function bit check_region_qos_ordering(axi4_transaction trans);
        // Check if high QoS uses appropriate regions
        if (trans.qos >= 12 && trans.region < 8) begin
            `uvm_info("REGION_QOS", 
                     $sformatf("High QoS %0d using low-priority region %0d",
                              trans.qos, trans.region), 
                     UVM_HIGH)
            return 0;
        end
        return 1;
    endfunction
    
    // Get checker report
    function string get_checker_report();
        string report = "\\n=== REGION Checker Report ===\\n";
        
        report = {{report, "\\nProtocol Checks:\\n"}};
        report = {{report, $sformatf("  Total: %0d, Passed: %0d, Failed: %0d, Warnings: %0d\\n",
                                    protocol_stats.total_checks, protocol_stats.passed,
                                    protocol_stats.failed, protocol_stats.warnings)}};
        report = {{report, $sformatf("  Constant violations: %0d\\n", region_constant_violations)}};
        report = {{report, $sformatf("  4KB violations: %0d\\n", region_4kb_violations)}};
        report = {{report, $sformatf("  WRAP violations: %0d\\n", region_wrap_violations)}};
        report = {{report, $sformatf("  Exclusive violations: %0d\\n", region_exclusive_violations)}};
        
        report = {{report, "\\nConsistency Checks:\\n"}};
        report = {{report, $sformatf("  Total: %0d, Passed: %0d, Failed: %0d, Warnings: %0d\\n",
                                    consistency_stats.total_checks, consistency_stats.passed,
                                    consistency_stats.failed, consistency_stats.warnings)}};
        
        report = {{report, "\\nPerformance Checks:\\n"}};
        report = {{report, $sformatf("  Total: %0d, Passed: %0d, Failed: %0d, Warnings: %0d\\n",
                                    performance_stats.total_checks, performance_stats.passed,
                                    performance_stats.failed, performance_stats.warnings)}};
        report = {{report, $sformatf("  Ordering violations: %0d\\n", region_ordering_violations)}};
        
        if (protocol_stats.failed > 0) begin
            report = {{report, $sformatf("\\nLast failure: %s at %0t\\n",
                                        protocol_stats.last_failure_msg,
                                        protocol_stats.last_failure_time)}};
        end
        
        return report;
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        `uvm_info(get_type_name(), get_checker_report(), UVM_LOW)
        
        // Overall pass/fail
        if (protocol_stats.failed > 0 || consistency_stats.failed > 0) begin
            `uvm_error(get_type_name(), "REGION checker detected failures!")
        end
    endfunction

endclass

`endif // AXI4_REGION_CHECKER_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_region_checker.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_region_configurator(self, output_dir: str):
        """Generate REGION configurator component"""
        content = f"""// AXI4 VIP REGION Configurator
// Generated: {datetime.datetime.now()}
// Provides runtime REGION configuration interface

`ifndef AXI4_REGION_CONFIGURATOR_SV
`define AXI4_REGION_CONFIGURATOR_SV

class axi4_region_configurator extends uvm_object;
    `uvm_object_utils(axi4_region_configurator)
    
    // Singleton instance
    static axi4_region_configurator m_inst;
    
    // Region configuration database
    axi4_region_decoder::region_map_t region_configs[string];
    
    // Master region assignments
    bit[3:0] master_region_masks[int] = '{{16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF}};
    
    // Region policy settings
    typedef struct {{
        bit auto_region_assignment;
        bit enforce_4kb_alignment;
        bit allow_region_remapping;
        bit strict_boundary_checking;
        string default_region_policy;
    }} region_policy_t;
    
    region_policy_t policy;
    
    // Constructor
    function new(string name = "axi4_region_configurator");
        super.new(name);
        set_default_policy();
    endfunction
    
    // Singleton getter
    static function axi4_region_configurator get();
        if (m_inst == null) begin
            m_inst = axi4_region_configurator::type_id::create("axi4_region_configurator");
        end
        return m_inst;
    endfunction
    
    // Set default policy
    function void set_default_policy();
        policy.auto_region_assignment = 1;
        policy.enforce_4kb_alignment = 1;
        policy.allow_region_remapping = 0;
        policy.strict_boundary_checking = 1;
        policy.default_region_policy = "STATIC";
    endfunction
    
    // Create region configuration
    function void create_region(string name,
                               bit[{self.addr_width-1}:0] start_addr,
                               bit[{self.addr_width-1}:0] end_addr,
                               bit[3:0] region_id,
                               bit[3:0] attributes = 0);
        axi4_region_decoder::region_map_t region;
        
        region.region_name = name;
        region.start_addr = start_addr;
        region.end_addr = end_addr;
        region.region_id = region_id;
        region.attributes = attributes;
        
        // Set default attributes based on region ID
        case (region_id)
            0, 1, 2, 3: begin  // Low regions - normal memory
                region.cacheable = 1;
                region.bufferable = 1;
                region.secure = 0;
                region.exclusive_capable = 1;
            end
            4, 5, 6, 7: begin  // Mid regions - device memory
                region.cacheable = 0;
                region.bufferable = 1;
                region.secure = 0;
                region.exclusive_capable = 1;
            end
            8, 9, 10, 11: begin  // High regions - peripheral
                region.cacheable = 0;
                region.bufferable = 0;
                region.secure = 0;
                region.exclusive_capable = 0;
            end
            12, 13, 14, 15: begin  // Secure regions
                region.cacheable = 1;
                region.bufferable = 1;
                region.secure = 1;
                region.exclusive_capable = 0;
            end
        endcase
        
        region_configs[name] = region;
        
        `uvm_info("REGION_CONFIG", 
                 $sformatf("Created region %s: [%0h:%0h] ID=%0d",
                          name, start_addr, end_addr, region_id), 
                 UVM_MEDIUM)
    endfunction
    
    // Configure master region access
    function void configure_master_regions(int master_id, bit[15:0] region_mask);
        master_region_masks[master_id] = region_mask;
        
        `uvm_info("REGION_CONFIG", 
                 $sformatf("Master %0d region mask: %04h", master_id, region_mask), 
                 UVM_MEDIUM)
    endfunction
    
    // Get region configuration
    function axi4_region_decoder::region_map_t get_region_config(string name);
        if (region_configs.exists(name)) begin
            return region_configs[name];
        end else begin
            `uvm_warning("REGION_CONFIG", 
                        $sformatf("Region %s not found", name))
            axi4_region_decoder::region_map_t empty;
            return empty;
        end
    endfunction
    
    // Check if master can access region
    function bit is_master_allowed(int master_id, bit[3:0] region_id);
        if (!master_region_masks.exists(master_id)) begin
            return 1;  // No restriction if not configured
        end
        
        return master_region_masks[master_id][region_id];
    endfunction
    
    // Apply region configurations to decoder
    function void apply_configurations(axi4_region_decoder decoder);
        foreach (region_configs[name]) begin
            // Map to appropriate slave based on address
            int slave_id = get_slave_from_address(region_configs[name].start_addr);
            decoder.add_region(slave_id, region_configs[name]);
        end
        
        // Apply policies
        decoder.enforce_4kb_boundary = policy.enforce_4kb_alignment;
        decoder.auto_split_4kb = policy.auto_region_assignment;
    endfunction
    
    // Get slave from address (simplified)
    function int get_slave_from_address(bit[{self.addr_width-1}:0] addr);
        // Simple mapping - divide address space among slaves
        return addr[{self.addr_width-1}:{self.addr_width-2}];
    endfunction
    
    // Load configuration from file
    function void load_config_file(string filename);
        int fd = $fopen(filename, "r");
        string line;
        
        if (fd) begin
            while (!$feof(fd)) begin
                void'($fgets(line, fd));
                parse_config_line(line);
            end
            $fclose(fd);
            
            `uvm_info("REGION_CONFIG", 
                     $sformatf("Loaded configuration from %s", filename), 
                     UVM_LOW)
        end else begin
            `uvm_warning("REGION_CONFIG", 
                        $sformatf("Cannot open config file %s", filename))
        end
    endfunction
    
    // Parse configuration line
    function void parse_config_line(string line);
        string tokens[$];
        string cmd;
        
        // Skip comments and empty lines
        if (line.substr(0, 0) == "#" || line == "") return;
        
        // Tokenize line
        void'($sscanf(line, "%s", cmd));
        
        case (cmd)
            "REGION": begin
                string name;
                bit[{self.addr_width-1}:0] start_addr, end_addr;
                bit[3:0] id, attr;
                
                void'($sscanf(line, "REGION %s %h %h %d %h", 
                             name, start_addr, end_addr, id, attr));
                create_region(name, start_addr, end_addr, id, attr);
            end
            
            "MASTER": begin
                int master_id;
                bit[15:0] mask;
                
                void'($sscanf(line, "MASTER %d %h", master_id, mask));
                configure_master_regions(master_id, mask);
            end
            
            "POLICY": begin
                string policy_name, value;
                
                void'($sscanf(line, "POLICY %s %s", policy_name, value));
                set_policy(policy_name, value);
            end
        endcase
    endfunction
    
    // Set policy
    function void set_policy(string policy_name, string value);
        case (policy_name)
            "auto_region_assignment": policy.auto_region_assignment = value.atoi();
            "enforce_4kb_alignment": policy.enforce_4kb_alignment = value.atoi();
            "allow_region_remapping": policy.allow_region_remapping = value.atoi();
            "strict_boundary_checking": policy.strict_boundary_checking = value.atoi();
            "default_region_policy": policy.default_region_policy = value;
        endcase
    endfunction
    
    // Save configuration to file
    function void save_config_file(string filename);
        int fd = $fopen(filename, "w");
        
        if (fd) begin
            $fwrite(fd, "# AXI4 REGION Configuration\\n");
            $fwrite(fd, "# Generated: %s\\n\\n", $sformatf("%0t", $time));
            
            // Write policy settings
            $fwrite(fd, "# Policy Settings\\n");
            $fwrite(fd, "POLICY auto_region_assignment %0d\\n", policy.auto_region_assignment);
            $fwrite(fd, "POLICY enforce_4kb_alignment %0d\\n", policy.enforce_4kb_alignment);
            $fwrite(fd, "POLICY allow_region_remapping %0d\\n", policy.allow_region_remapping);
            $fwrite(fd, "POLICY strict_boundary_checking %0d\\n", policy.strict_boundary_checking);
            $fwrite(fd, "POLICY default_region_policy %s\\n\\n", policy.default_region_policy);
            
            // Write region configurations
            $fwrite(fd, "# Region Definitions\\n");
            $fwrite(fd, "# REGION <name> <start_addr> <end_addr> <id> <attributes>\\n");
            foreach (region_configs[name]) begin
                axi4_region_decoder::region_map_t r = region_configs[name];
                $fwrite(fd, "REGION %s %08h %08h %d %01h\\n",
                       name, r.start_addr, r.end_addr, r.region_id, r.attributes);
            end
            
            // Write master configurations
            $fwrite(fd, "\\n# Master Region Access\\n");
            $fwrite(fd, "# MASTER <id> <region_mask>\\n");
            foreach (master_region_masks[id]) begin
                $fwrite(fd, "MASTER %d %04h\\n", id, master_region_masks[id]);
            end
            
            $fclose(fd);
            
            `uvm_info("REGION_CONFIG", 
                     $sformatf("Saved configuration to %s", filename), 
                     UVM_LOW)
        end
    endfunction
    
    // Generate example configuration
    function void generate_example_config();
        // Create example regions for 4 slaves
        for (int slave = 0; slave < 4; slave++) begin
            bit[{self.addr_width-1}:0] slave_base = slave * 32'h1000_0000;
            
            // Normal memory region
            create_region($sformatf("slave%0d_normal", slave),
                         slave_base,
                         slave_base + 32'h03FF_FFFF,
                         slave * 4 + 0);
            
            // Device memory region
            create_region($sformatf("slave%0d_device", slave),
                         slave_base + 32'h0400_0000,
                         slave_base + 32'h07FF_FFFF,
                         slave * 4 + 1);
            
            // Peripheral region
            create_region($sformatf("slave%0d_periph", slave),
                         slave_base + 32'h0800_0000,
                         slave_base + 32'h0BFF_FFFF,
                         slave * 4 + 2);
            
            // Secure region
            create_region($sformatf("slave%0d_secure", slave),
                         slave_base + 32'h0C00_0000,
                         slave_base + 32'h0FFF_FFFF,
                         slave * 4 + 3);
        end
        
        // Configure master access
        configure_master_regions(0, 16'hFFFF);  // Master 0: full access
        configure_master_regions(1, 16'h0FFF);  // Master 1: no secure regions
        configure_master_regions(2, 16'hF000);  // Master 2: secure only
        configure_master_regions(3, 16'h00FF);  // Master 3: low regions only
    endfunction
    
    // Get configuration summary
    function string get_config_summary();
        string summary = "\\n=== REGION Configuration Summary ===\\n";
        
        summary = {{summary, "\\nPolicy Settings:\\n"}};
        summary = {{summary, $sformatf("  Auto assignment: %s\\n", 
                                     policy.auto_region_assignment ? "Enabled" : "Disabled")}};
        summary = {{summary, $sformatf("  4KB alignment: %s\\n",
                                     policy.enforce_4kb_alignment ? "Enforced" : "Relaxed")}};
        summary = {{summary, $sformatf("  Remapping: %s\\n",
                                     policy.allow_region_remapping ? "Allowed" : "Disabled")}};
        summary = {{summary, $sformatf("  Boundary checking: %s\\n",
                                     policy.strict_boundary_checking ? "Strict" : "Relaxed")}};
        
        summary = {{summary, $sformatf("\\nConfigured Regions: %0d\\n", region_configs.size())}};
        foreach (region_configs[name]) begin
            axi4_region_decoder::region_map_t r = region_configs[name];
            summary = {{summary, $sformatf("  %s: [%08h:%08h] ID=%d\\n",
                                         name, r.start_addr, r.end_addr, r.region_id)}};
        end
        
        summary = {{summary, $sformatf("\\nMaster Configurations: %0d\\n", master_region_masks.size())}};
        foreach (master_region_masks[id]) begin
            summary = {{summary, $sformatf("  Master %d: mask=%04h\\n", 
                                         id, master_region_masks[id])}};
        end
        
        return summary;
    endfunction

endclass

`endif // AXI4_REGION_CONFIGURATOR_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_region_configurator.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def _generate_region_package(self, output_dir: str):
        """Generate REGION package file"""
        content = f"""// AXI4 VIP REGION Package
// Generated: {datetime.datetime.now()}
// Contains all REGION-related components

`ifndef AXI4_REGION_PKG_SV
`define AXI4_REGION_PKG_SV

package axi4_region_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Import base VIP package
    import axi4_vip_pkg::*;
    
    // REGION definitions
    typedef enum bit[3:0] {{
        REGION_0  = 4'h0,
        REGION_1  = 4'h1,
        REGION_2  = 4'h2,
        REGION_3  = 4'h3,
        REGION_4  = 4'h4,
        REGION_5  = 4'h5,
        REGION_6  = 4'h6,
        REGION_7  = 4'h7,
        REGION_8  = 4'h8,
        REGION_9  = 4'h9,
        REGION_10 = 4'hA,
        REGION_11 = 4'hB,
        REGION_12 = 4'hC,
        REGION_13 = 4'hD,
        REGION_14 = 4'hE,
        REGION_15 = 4'hF
    }} region_id_e;
    
    // Include REGION components
    `include "axi4_region_decoder.sv"
    `include "axi4_region_mapper.sv"
    `include "axi4_region_controller.sv"
    `include "axi4_region_monitor.sv"
    `include "axi4_region_checker.sv"
    `include "axi4_region_configurator.sv"
    
endpackage

`endif // AXI4_REGION_PKG_SV
"""
        
        filepath = os.path.join(output_dir, "axi4_region_pkg.sv")
        with open(filepath, 'w') as f:
            f.write(content)
            
    def generate_region_integration_example(self, output_dir: str):
        """Generate example of REGION integration"""
        content = f"""// AXI4 VIP REGION Integration Example
// Generated: {datetime.datetime.now()}
// Shows how to integrate REGION components

class axi4_region_env extends uvm_env;
    `uvm_component_utils(axi4_region_env)
    
    // REGION components
    axi4_region_decoder region_decoder;
    axi4_region_mapper region_mapper;
    axi4_region_controller region_controller;
    axi4_region_monitor region_monitor;
    axi4_region_checker region_checker;
    
    // Constructor
    function new(string name = "axi4_region_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    // Build phase
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create REGION components
        region_decoder = axi4_region_decoder::type_id::create("region_decoder", this);
        region_mapper = axi4_region_mapper::type_id::create("region_mapper", this);
        region_controller = axi4_region_controller::type_id::create("region_controller", this);
        region_monitor = axi4_region_monitor::type_id::create("region_monitor", this);
        region_checker = axi4_region_checker::type_id::create("region_checker", this);
        
        // Configure REGION system
        configure_regions();
    endfunction
    
    // Configure regions
    function void configure_regions();
        axi4_region_configurator region_config = axi4_region_configurator::get();
        
        // Generate example configuration
        region_config.generate_example_config();
        
        // Apply to decoder
        region_config.apply_configurations(region_decoder);
        
        // Configure mapper
        region_mapper.decoder = region_decoder;
        region_mapper.mode = axi4_region_mapper::HYBRID_MAPPING;
        
        // Configure controller
        region_controller.decoder = region_decoder;
        region_controller.mapper = region_mapper;
        
        // Configure specific regions
        configure_memory_regions();
        configure_peripheral_regions();
        configure_secure_regions();
        
        // Save configuration
        region_config.save_config_file("region_config.txt");
    endfunction
    
    // Configure memory regions
    function void configure_memory_regions();
        // Regions 0-3: Normal memory
        for (int i = 0; i < 4; i++) begin
            axi4_region_controller::region_access_control_t ctrl;
            ctrl.read_enable = 1;
            ctrl.write_enable = 1;
            ctrl.exclusive_enable = 1;
            ctrl.secure_only = 0;
            ctrl.max_outstanding = 32;
            ctrl.priority_level = 0;
            
            region_controller.configure_region_access(i, ctrl);
        end
    endfunction
    
    // Configure peripheral regions
    function void configure_peripheral_regions();
        // Regions 8-11: Peripherals
        for (int i = 8; i < 12; i++) begin
            axi4_region_controller::region_access_control_t ctrl;
            ctrl.read_enable = 1;
            ctrl.write_enable = 1;
            ctrl.exclusive_enable = 0;
            ctrl.secure_only = 0;
            ctrl.max_outstanding = 1;  // No pipelining
            ctrl.priority_level = 2;
            
            region_controller.configure_region_access(i, ctrl);
        end
    endfunction
    
    // Configure secure regions
    function void configure_secure_regions();
        // Regions 12-15: Secure
        for (int i = 12; i < 16; i++) begin
            axi4_region_controller::region_access_control_t ctrl;
            ctrl.read_enable = 1;
            ctrl.write_enable = 1;
            ctrl.exclusive_enable = 0;
            ctrl.secure_only = 1;
            ctrl.max_outstanding = 16;
            ctrl.priority_level = 3;
            
            // Only secure masters allowed
            ctrl.allowed_masters = '{2, 3};  // Masters 2 and 3 are secure
            
            region_controller.configure_region_access(i, ctrl);
        end
    endfunction
    
    // Connect phase
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        
        // Connect monitor to checker
        region_monitor.decoder = region_decoder;
        region_monitor.controller = region_controller;
        
        // Connect components
        // region_monitor.region_ap.connect(region_checker.analysis_export);
    endfunction
    
    // End of elaboration
    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);
        
        // Print configuration
        `uvm_info(get_type_name(), region_decoder.get_region_map(), UVM_LOW)
        `uvm_info(get_type_name(), 
                 axi4_region_configurator::get().get_config_summary(), 
                 UVM_LOW)
    endfunction
    
    // Report phase
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        
        // Generate comprehensive REGION report
        `uvm_info(get_type_name(), "=== REGION System Report ===", UVM_LOW)
        `uvm_info(get_type_name(), region_decoder.get_region_stats(), UVM_LOW)
        `uvm_info(get_type_name(), region_mapper.get_mapping_stats(), UVM_LOW)
        `uvm_info(get_type_name(), region_controller.get_region_status(), UVM_LOW)
        `uvm_info(get_type_name(), region_monitor.get_region_report(), UVM_LOW)
        `uvm_info(get_type_name(), region_checker.get_checker_report(), UVM_LOW)
    endfunction

endclass

// Example test using REGION
class axi4_region_test extends uvm_test;
    `uvm_component_utils(axi4_region_test)
    
    axi4_region_env env;
    
    function new(string name = "axi4_region_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = axi4_region_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        axi4_region_sequence seq;
        
        phase.raise_objection(this);
        
        // Run region-aware sequences
        seq = axi4_region_sequence::type_id::create("seq");
        seq.start(null);
        
        #100us;
        
        phase.drop_objection(this);
    endtask

endclass

// Example sequence using REGION
class axi4_region_sequence extends uvm_sequence;
    `uvm_object_utils(axi4_region_sequence)
    
    function new(string name = "axi4_region_sequence");
        super.new(name);
    endfunction
    
    task body();
        axi4_transaction trans;
        
        // Test different regions
        for (int region = 0; region < 16; region++) begin
            trans = axi4_transaction::type_id::create("trans");
            
            // Configure transaction for specific region
            trans.addr = region * 32'h1000_0000;  // Each region gets 256MB
            trans.region = region;
            trans.len = $urandom_range(0, 15);
            trans.size = $urandom_range(0, 3);
            trans.burst = $urandom_range(0, 2);
            
            // Test exclusive access in capable regions
            if (region < 8) begin
                trans.lock = $urandom_range(0, 1);
            end
            
            // Test secure access in secure regions
            if (region >= 12) begin
                trans.prot[1] = 1;  // Secure
            end
            
            `uvm_info(get_type_name(), 
                     $sformatf("Testing region %0d with addr=%0h", region, trans.addr), 
                     UVM_MEDIUM)
            
            // Send transaction
            // `uvm_send(trans)
        end
        
        // Test 4KB boundary scenarios
        test_4kb_boundaries();
        
        // Test region crossing
        test_region_crossing();
    endtask
    
    task test_4kb_boundaries();
        axi4_transaction trans;
        
        // Test transaction at 4KB boundary
        trans = axi4_transaction::type_id::create("trans");
        trans.addr = 32'h0000_0FFE;  // Near 4KB boundary
        trans.len = 3;  // Will cross boundary
        trans.size = 2;  // 4 bytes per beat
        trans.region = 0;  // Should remain constant
        
        `uvm_info(get_type_name(), "Testing 4KB boundary crossing", UVM_MEDIUM)
        // `uvm_send(trans)
    endtask
    
    task test_region_crossing();
        axi4_transaction trans;
        
        // Test burst that would cross regions (should fail)
        trans = axi4_transaction::type_id::create("trans");
        trans.addr = 32'h0FFF_FFF0;  // Near region boundary
        trans.len = 15;  // Long burst
        trans.size = 3;  // 8 bytes per beat
        trans.region = 0;
        
        `uvm_info(get_type_name(), "Testing region boundary crossing", UVM_MEDIUM)
        // `uvm_send(trans)
    endtask

endclass
"""
        
        filepath = os.path.join(output_dir, "axi4_region_integration_example.sv")
        with open(filepath, 'w') as f:
            f.write(content)

# Example usage
if __name__ == "__main__":
    config = {
        'num_masters': 4,
        'num_slaves': 4,
        'data_width': 64,
        'addr_width': 32,
        'id_width': 4,
        'protocol': 'AXI4'
    }
    
    generator = VIPRegionGenerator(config)
    generator.generate_all_region_components("./vip_output")
    generator.generate_region_integration_example("./vip_output")
    print("REGION components generated successfully!")