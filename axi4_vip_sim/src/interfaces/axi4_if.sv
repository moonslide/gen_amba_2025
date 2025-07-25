//==============================================================================
// AXI4 Interface Definition
// Compliant with AMBA AXI4 Protocol Specification (IHI0022D)
// Supports full AXI4 feature set including QoS, Regions, User signals
//==============================================================================

interface axi4_if #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64,
    parameter int ID_WIDTH   = 4,
    parameter int USER_WIDTH = 1,
    parameter int WSTRB_WIDTH = DATA_WIDTH/8
)(
    input logic aclk,
    input logic aresetn
);

    // Write Address Channel
    logic [ID_WIDTH-1:0]     awid;
    logic [ADDR_WIDTH-1:0]   awaddr;
    logic [7:0]              awlen;      // Burst length: 0-255 (1-256 transfers)
    logic [2:0]              awsize;     // Burst size: bytes in transfer
    logic [1:0]              awburst;    // Burst type: FIXED/INCR/WRAP
    logic                    awlock;     // Lock type (always 0 for AXI4)
    logic [3:0]              awcache;    // Cache attributes
    logic [2:0]              awprot;     // Protection attributes
    logic [3:0]              awqos;      // Quality of Service
    logic [3:0]              awregion;   // Region identifier
    logic [USER_WIDTH-1:0]   awuser;     // User-defined signals
    logic                    awvalid;    // Write address valid
    logic                    awready;    // Write address ready

    // Write Data Channel
    logic [DATA_WIDTH-1:0]   wdata;      // Write data
    logic [WSTRB_WIDTH-1:0]  wstrb;      // Write strobes
    logic                    wlast;      // Write last
    logic [USER_WIDTH-1:0]   wuser;      // User-defined signals
    logic                    wvalid;     // Write valid
    logic                    wready;     // Write ready

    // Write Response Channel
    logic [ID_WIDTH-1:0]     bid;        // Response ID
    logic [1:0]              bresp;      // Write response
    logic [USER_WIDTH-1:0]   buser;      // User-defined signals
    logic                    bvalid;     // Write response valid
    logic                    bready;     // Response ready

    // Read Address Channel
    logic [ID_WIDTH-1:0]     arid;       // Read address ID
    logic [ADDR_WIDTH-1:0]   araddr;     // Read address
    logic [7:0]              arlen;      // Burst length
    logic [2:0]              arsize;     // Burst size
    logic [1:0]              arburst;    // Burst type
    logic                    arlock;     // Lock type
    logic [3:0]              arcache;    // Cache attributes
    logic [2:0]              arprot;     // Protection attributes
    logic [3:0]              arqos;      // Quality of Service
    logic [3:0]              arregion;   // Region identifier
    logic [USER_WIDTH-1:0]   aruser;     // User-defined signals
    logic                    arvalid;    // Read address valid
    logic                    arready;    // Read address ready

    // Read Data Channel
    logic [ID_WIDTH-1:0]     rid;        // Read ID tag
    logic [DATA_WIDTH-1:0]   rdata;      // Read data
    logic [1:0]              rresp;      // Read response
    logic                    rlast;      // Read last
    logic [USER_WIDTH-1:0]   ruser;      // User-defined signals
    logic                    rvalid;     // Read valid
    logic                    rready;     // Read ready

    // Low Power Interface (Optional)
    logic                    csysreq;    // System exit low power state request
    logic                    csysack;    // Exit low power state acknowledge
    logic                    cactive;    // Clock active

    //==========================================================================
    // Clocking Blocks for UVM Agents
    //==========================================================================

    // Master clocking block
    clocking master_cb @(posedge aclk);
        default input #1step output #1step;
        
        // Write Address Channel
        output awid, awaddr, awlen, awsize, awburst, awlock;
        output awcache, awprot, awqos, awregion, awuser, awvalid;
        input  awready;
        
        // Write Data Channel
        output wdata, wstrb, wlast, wuser, wvalid;
        input  wready;
        
        // Write Response Channel
        input  bid, bresp, buser, bvalid;
        output bready;
        
        // Read Address Channel
        output arid, araddr, arlen, arsize, arburst, arlock;
        output arcache, arprot, arqos, arregion, aruser, arvalid;
        input  arready;
        
        // Read Data Channel
        input  rid, rdata, rresp, rlast, ruser, rvalid;
        output rready;
        
        // Low Power Interface
        output csysreq;
        input  csysack, cactive;
    endclocking

    // Slave clocking block
    clocking slave_cb @(posedge aclk);
        default input #1step output #1step;
        
        // Write Address Channel
        input  awid, awaddr, awlen, awsize, awburst, awlock;
        input  awcache, awprot, awqos, awregion, awuser, awvalid;
        output awready;
        
        // Write Data Channel
        input  wdata, wstrb, wlast, wuser, wvalid;
        output wready;
        
        // Write Response Channel
        output bid, bresp, buser, bvalid;
        input  bready;
        
        // Read Address Channel
        input  arid, araddr, arlen, arsize, arburst, arlock;
        input  arcache, arprot, arqos, arregion, aruser, arvalid;
        output arready;
        
        // Read Data Channel
        output rid, rdata, rresp, rlast, ruser, rvalid;
        input  rready;
        
        // Low Power Interface
        input  csysreq;
        output csysack, cactive;
    endclocking

    // Monitor clocking block (passive - input only)
    clocking monitor_cb @(posedge aclk);
        default input #1step;
        
        input awid, awaddr, awlen, awsize, awburst, awlock;
        input awcache, awprot, awqos, awregion, awuser, awvalid, awready;
        input wdata, wstrb, wlast, wuser, wvalid, wready;
        input bid, bresp, buser, bvalid, bready;
        input arid, araddr, arlen, arsize, arburst, arlock;
        input arcache, arprot, arqos, arregion, aruser, arvalid, arready;
        input rid, rdata, rresp, rlast, ruser, rvalid, rready;
        input csysreq, csysack, cactive;
    endclocking

    //==========================================================================
    // Modports for different agent types
    //==========================================================================

    // Master modport
    modport master (
        clocking master_cb,
        input aclk, aresetn
    );

    // Slave modport
    modport slave (
        clocking slave_cb,
        input aclk, aresetn
    );

    // Monitor modport
    modport monitor (
        clocking monitor_cb,
        input aclk, aresetn
    );

    // Passive monitor modport (for interconnect monitoring)
    modport passive_monitor (
        input aclk, aresetn,
        input awid, awaddr, awlen, awsize, awburst, awlock,
        input awcache, awprot, awqos, awregion, awuser, awvalid, awready,
        input wdata, wstrb, wlast, wuser, wvalid, wready,
        input bid, bresp, buser, bvalid, bready,
        input arid, araddr, arlen, arsize, arburst, arlock,
        input arcache, arprot, arqos, arregion, aruser, arvalid, arready,
        input rid, rdata, rresp, rlast, ruser, rvalid, rready,
        input csysreq, csysack, cactive
    );

    //==========================================================================
    // Interface Tasks and Functions
    //==========================================================================

    // Reset task
    task automatic reset_interface();
        awid     <= '0;
        awaddr   <= '0;
        awlen    <= '0;
        awsize   <= '0;
        awburst  <= '0;
        awlock   <= '0;
        awcache  <= '0;
        awprot   <= '0;
        awqos    <= '0;
        awregion <= '0;
        awuser   <= '0;
        awvalid  <= '0;
        awready  <= '0;
        
        wdata    <= '0;
        wstrb    <= '0;
        wlast    <= '0;
        wuser    <= '0;
        wvalid   <= '0;
        wready   <= '0;
        
        bid      <= '0;
        bresp    <= '0;
        buser    <= '0;
        bvalid   <= '0;
        bready   <= '0;
        
        arid     <= '0;
        araddr   <= '0;
        arlen    <= '0;
        arsize   <= '0;
        arburst  <= '0;
        arlock   <= '0;
        arcache  <= '0;
        arprot   <= '0;
        arqos    <= '0;
        arregion <= '0;
        aruser   <= '0;
        arvalid  <= '0;
        arready  <= '0;
        
        rid      <= '0;
        rdata    <= '0;
        rresp    <= '0;
        rlast    <= '0;
        ruser    <= '0;
        rvalid   <= '0;
        rready   <= '0;
        
        csysreq  <= '0;
        csysack  <= '0;
        cactive  <= '1;
    endtask

    // Wait for reset deassertion
    task automatic wait_for_reset_release();
        wait (aresetn === 1'b0);
        wait (aresetn === 1'b1);
        repeat (2) @(posedge aclk);
    endtask

    // Function to check 4KB boundary crossing
    function automatic bit check_4kb_boundary_crossing(
        input [ADDR_WIDTH-1:0] addr,
        input [7:0] len,
        input [2:0] size
    );
        logic [ADDR_WIDTH-1:0] start_addr, end_addr;
        logic [ADDR_WIDTH-1:0] bytes_per_transfer;
        logic [ADDR_WIDTH-1:0] total_bytes;
        
        bytes_per_transfer = 1 << size;
        total_bytes = (len + 1) * bytes_per_transfer;
        start_addr = addr;
        end_addr = addr + total_bytes - 1;
        
        // Check if start and end addresses are in different 4KB pages
        return (start_addr[ADDR_WIDTH-1:12] != end_addr[ADDR_WIDTH-1:12]);
    endfunction

    // Function to calculate wrap boundary
    function automatic [ADDR_WIDTH-1:0] get_wrap_boundary(
        input [ADDR_WIDTH-1:0] addr,
        input [7:0] len,
        input [2:0] size
    );
        logic [ADDR_WIDTH-1:0] bytes_per_transfer;
        logic [ADDR_WIDTH-1:0] wrap_size;
        
        bytes_per_transfer = 1 << size;
        wrap_size = (len + 1) * bytes_per_transfer;
        
        return (addr / wrap_size) * wrap_size;
    endfunction

    //==========================================================================
    // Protocol Checker Assertions
    //==========================================================================

    // AXI4 Protocol Assertions
    generate
        if (1) begin : protocol_assertions
            
            // Write Address Channel Assertions
            property awvalid_stable;
                @(posedge aclk) disable iff (!aresetn)
                $rose(awvalid) |=> awvalid throughout (awvalid && !awready)[*0:$] ##1 awready;
            endproperty

            property awaddr_stable_during_valid;
                @(posedge aclk) disable iff (!aresetn)
                awvalid && !awready |=> $stable({awid, awaddr, awlen, awsize, awburst, awlock, awcache, awprot, awqos, awregion, awuser});
            endproperty

            // 4KB boundary crossing check
            property no_4kb_boundary_crossing;
                @(posedge aclk) disable iff (!aresetn)
                awvalid |-> !check_4kb_boundary_crossing(awaddr, awlen, awsize);
            endproperty

            // WRAP burst constraints
            property wrap_burst_length;
                @(posedge aclk) disable iff (!aresetn)
                awvalid && (awburst == 2'b10) |-> (awlen inside {1, 3, 7, 15}); // 2, 4, 8, 16 transfers
            endproperty

            // Write Data Channel Assertions
            property wvalid_stable;
                @(posedge aclk) disable iff (!aresetn)
                $rose(wvalid) |=> wvalid throughout (wvalid && !wready)[*0:$] ##1 wready;
            endproperty

            property wdata_stable_during_valid;
                @(posedge aclk) disable iff (!aresetn)
                wvalid && !wready |=> $stable({wdata, wstrb, wlast, wuser});
            endproperty

            // Read Address Channel Assertions
            property arvalid_stable;
                @(posedge aclk) disable iff (!aresetn)
                $rose(arvalid) |=> arvalid throughout (arvalid && !arready)[*0:$] ##1 arready;
            endproperty

            property araddr_stable_during_valid;
                @(posedge aclk) disable iff (!aresetn)
                arvalid && !arready |=> $stable({arid, araddr, arlen, arsize, arburst, arlock, arcache, arprot, arqos, arregion, aruser});
            endproperty

            // Read Data Channel Assertions
            property rvalid_stable;
                @(posedge aclk) disable iff (!aresetn)
                $rose(rvalid) |=> rvalid throughout (rvalid && !rready)[*0:$] ##1 rready;
            endproperty

            property rdata_stable_during_valid;
                @(posedge aclk) disable iff (!aresetn)
                rvalid && !rready |=> $stable({rid, rdata, rresp, rlast, ruser});
            endproperty

            // Bind assertions
            assert_awvalid_stable: assert property (awvalid_stable)
                else $error("AXI4 Protocol Violation: AWVALID not stable during handshake");

            assert_awaddr_stable: assert property (awaddr_stable_during_valid)
                else $error("AXI4 Protocol Violation: AW signals not stable during AWVALID");

            assert_no_4kb_crossing: assert property (no_4kb_boundary_crossing)
                else $error("AXI4 Protocol Violation: Transaction crosses 4KB boundary");

            assert_wrap_length: assert property (wrap_burst_length)
                else $error("AXI4 Protocol Violation: Invalid WRAP burst length");

            assert_wvalid_stable: assert property (wvalid_stable)
                else $error("AXI4 Protocol Violation: WVALID not stable during handshake");

            assert_wdata_stable: assert property (wdata_stable_during_valid)
                else $error("AXI4 Protocol Violation: W signals not stable during WVALID");

            assert_arvalid_stable: assert property (arvalid_stable)
                else $error("AXI4 Protocol Violation: ARVALID not stable during handshake");

            assert_araddr_stable: assert property (araddr_stable_during_valid)
                else $error("AXI4 Protocol Violation: AR signals not stable during ARVALID");

            assert_rvalid_stable: assert property (rvalid_stable)
                else $error("AXI4 Protocol Violation: RVALID not stable during handshake");

            assert_rdata_stable: assert property (rdata_stable_during_valid)
                else $error("AXI4 Protocol Violation: R signals not stable during RVALID");

        end
    endgenerate

    //==========================================================================
    // Coverage Collection
    //==========================================================================

    // Functional coverage for AXI4 features
    covergroup axi4_functional_coverage @(posedge aclk);
        option.per_instance = 1;
        option.name = "axi4_functional_coverage";

        // Burst type coverage
        cp_awburst: coverpoint awburst iff (awvalid && awready) {
            bins fixed = {2'b00};
            bins incr  = {2'b01};
            bins wrap  = {2'b10};
            illegal_bins reserved = {2'b11};
        }

        cp_arburst: coverpoint arburst iff (arvalid && arready) {
            bins fixed = {2'b00};
            bins incr  = {2'b01};
            bins wrap  = {2'b10};
            illegal_bins reserved = {2'b11};
        }

        // Burst length coverage
        cp_awlen: coverpoint awlen iff (awvalid && awready) {
            bins single = {0};
            bins short_burst = {[1:15]};
            bins long_burst = {[16:255]};
        }

        cp_arlen: coverpoint arlen iff (arvalid && arready) {
            bins single = {0};
            bins short_burst = {[1:15]};
            bins long_burst = {[16:255]};
        }

        // QoS coverage
        cp_awqos: coverpoint awqos iff (awvalid && awready) {
            bins low_priority = {[0:3]};
            bins med_priority = {[4:7]};
            bins high_priority = {[8:11]};
            bins critical_priority = {[12:15]};
        }

        cp_arqos: coverpoint arqos iff (arvalid && arready) {
            bins low_priority = {[0:3]};
            bins med_priority = {[4:7]};
            bins high_priority = {[8:11]};
            bins critical_priority = {[12:15]};
        }

        // Protection type coverage
        cp_awprot: coverpoint awprot iff (awvalid && awready) {
            bins unpriv_nonsecure_data = {3'b000};
            bins priv_nonsecure_data   = {3'b001};
            bins unpriv_secure_data    = {3'b010};
            bins priv_secure_data      = {3'b011};
            bins unpriv_nonsecure_inst = {3'b100};
            bins priv_nonsecure_inst   = {3'b101};
            bins unpriv_secure_inst    = {3'b110};
            bins priv_secure_inst      = {3'b111};
        }

        cp_arprot: coverpoint arprot iff (arvalid && arready) {
            bins unpriv_nonsecure_data = {3'b000};
            bins priv_nonsecure_data   = {3'b001};
            bins unpriv_secure_data    = {3'b010};
            bins priv_secure_data      = {3'b011};
            bins unpriv_nonsecure_inst = {3'b100};
            bins priv_nonsecure_inst   = {3'b101};
            bins unpriv_secure_inst    = {3'b110};
            bins priv_secure_inst      = {3'b111};
        }

        // Response coverage
        cp_bresp: coverpoint bresp iff (bvalid && bready) {
            bins okay   = {2'b00};
            bins exokay = {2'b01};
            bins slverr = {2'b10};
            bins decerr = {2'b11};
        }

        cp_rresp: coverpoint rresp iff (rvalid && rready) {
            bins okay   = {2'b00};
            bins exokay = {2'b01};
            bins slverr = {2'b10};
            bins decerr = {2'b11};
        }

        // Cross coverage for important combinations
        cross_write_burst_qos: cross cp_awburst, cp_awqos;
        cross_read_burst_qos: cross cp_arburst, cp_arqos;
        cross_write_prot_resp: cross cp_awprot, cp_bresp;
        cross_read_prot_resp: cross cp_arprot, cp_rresp;

    endgroup

    // Instantiate coverage
    axi4_functional_coverage axi4_cov = new();

endinterface : axi4_if