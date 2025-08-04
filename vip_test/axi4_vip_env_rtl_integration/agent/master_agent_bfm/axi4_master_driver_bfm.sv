//==============================================================================
// AXI4 Master Driver BFM
// Bus Functional Model for driving AXI4 master transactions
//==============================================================================

interface axi4_master_driver_bfm #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH   = 4
)(
    input aclk,
    input aresetn
);

    import axi4_globals_pkg::*;
    
    // Write Address Channel
    logic [ID_WIDTH-1:0]    awid;
    logic [ADDR_WIDTH-1:0]  awaddr;
    logic [7:0]             awlen;
    logic [2:0]             awsize;
    logic [1:0]             awburst;
    logic                   awlock;
    logic [3:0]             awcache;
    logic [2:0]             awprot;
    logic [3:0]             awqos;
    logic [3:0]             awregion;
    logic                   awvalid;
    logic                   awready;
    
    // Write Data Channel
    logic [DATA_WIDTH-1:0]  wdata;
    logic [(DATA_WIDTH/8)-1:0] wstrb;
    logic                   wlast;
    logic                   wvalid;
    logic                   wready;
    
    // Write Response Channel
    logic [ID_WIDTH-1:0]    bid;
    logic [1:0]             bresp;
    logic                   bvalid;
    logic                   bready;
    
    // Read Address Channel
    logic [ID_WIDTH-1:0]    arid;
    logic [ADDR_WIDTH-1:0]  araddr;
    logic [7:0]             arlen;
    logic [2:0]             arsize;
    logic [1:0]             arburst;
    logic                   arlock;
    logic [3:0]             arcache;
    logic [2:0]             arprot;
    logic [3:0]             arqos;
    logic [3:0]             arregion;
    logic                   arvalid;
    logic                   arready;
    
    // Read Data Channel
    logic [ID_WIDTH-1:0]    rid;
    logic [DATA_WIDTH-1:0]  rdata;
    logic [1:0]             rresp;
    logic                   rlast;
    logic                   rvalid;
    logic                   rready;
    
    // Initialize outputs
    initial begin
        awvalid = 0;
        wvalid = 0;
        bready = 1;
        arvalid = 0;
        rready = 1;
        awid = '0;
        awaddr = '0;
        awlen = '0;
        awsize = '0;
        awburst = '0;
        awlock = '0;
        awcache = '0;
        awprot = '0;
        awqos = '0;
        awregion = '0;
        wdata = '0;
        wstrb = '0;
        wlast = '0;
        arid = '0;
        araddr = '0;
        arlen = '0;
        arsize = '0;
        arburst = '0;
        arlock = '0;
        arcache = '0;
        arprot = '0;
        arqos = '0;
        arregion = '0;
    end
    
    // Wait for reset before any activity
    initial begin
        @(posedge aresetn);
        $display("[%0t] BFM: Reset released, BFM ready for transactions", $time);
    end
    
    // Task to drive write address channel
    task automatic drive_write_addr(
        input [ID_WIDTH-1:0]    id,
        input [ADDR_WIDTH-1:0]  addr,
        input [7:0]             len,
        input [2:0]             size,
        input [1:0]             burst,
        input [3:0]             cache = 4'b0000,
        input [2:0]             prot = 3'b000,
        input [3:0]             qos = 4'b0000,
        input [3:0]             region = 4'b0000,
        input                   lock = 1'b0
    );
        $display("[%0t] BFM: Driving WRITE_ADDR - addr=0x%0h, id=%0d, len=%0d, size=%0d, burst=%0d",
                 $time, addr, id, len, size, burst);
        
        // Wait for reset to be released
        wait(aresetn == 1'b1);
        
        @(posedge aclk);
        awid     <= id;
        awaddr   <= addr;
        awlen    <= len;
        awsize   <= size;
        awburst  <= burst;
        awlock   <= lock;
        awcache  <= cache;
        awprot   <= prot;
        awqos    <= qos;
        awregion <= region;
        awvalid  <= 1;
        
        // Wait for awready with timeout
        fork
            begin
                @(posedge aclk iff awready);
                $display("[%0t] BFM: WRITE_ADDR accepted", $time);
            end
            begin
                repeat(1000) @(posedge aclk);
                $display("[%0t] BFM: ERROR - WRITE_ADDR timeout waiting for awready", $time);
            end
        join_any
        disable fork;
        
        awvalid  <= 0;
    endtask
    
    // Task to drive write data channel
    task automatic drive_write_data(
        input [DATA_WIDTH-1:0] data,
        input [(DATA_WIDTH/8)-1:0] strb,
        input last
    );
        $display("[%0t] BFM: Driving WRITE_DATA - data=0x%0h, strb=0x%0h, last=%0b",
                 $time, data, strb, last);
        
        @(posedge aclk);
        wdata   <= data;
        wstrb   <= strb;
        wlast   <= last;
        wvalid  <= 1;
        
        // Wait for wready
        @(posedge aclk iff wready);
        $display("[%0t] BFM: WRITE_DATA accepted", $time);
        wvalid  <= 0;
    endtask
    
    // Task to wait for write response
    task automatic wait_write_resp(
        output [ID_WIDTH-1:0] id,
        output [1:0] resp
    );
        $display("[%0t] BFM: Waiting for WRITE_RESP", $time);
        
        @(posedge aclk iff bvalid);
        id = bid;
        resp = bresp;
        
        $display("[%0t] BFM: Got WRITE_RESP - id=%0d, resp=%0d", $time, id, resp);
    endtask
    
    // Task to drive read address channel
    task automatic drive_read_addr(
        input [ID_WIDTH-1:0]    id,
        input [ADDR_WIDTH-1:0]  addr,
        input [7:0]             len,
        input [2:0]             size,
        input [1:0]             burst,
        input [3:0]             cache = 4'b0000,
        input [2:0]             prot = 3'b000,
        input [3:0]             qos = 4'b0000,
        input [3:0]             region = 4'b0000,
        input                   lock = 1'b0
    );
        $display("[%0t] BFM: Driving READ_ADDR - addr=0x%0h, id=%0d, len=%0d, size=%0d, burst=%0d",
                 $time, addr, id, len, size, burst);
        
        @(posedge aclk);
        arid     <= id;
        araddr   <= addr;
        arlen    <= len;
        arsize   <= size;
        arburst  <= burst;
        arlock   <= lock;
        arcache  <= cache;
        arprot   <= prot;
        arqos    <= qos;
        arregion <= region;
        arvalid  <= 1;
        
        // Wait for arready
        @(posedge aclk iff arready);
        $display("[%0t] BFM: READ_ADDR accepted", $time);
        arvalid  <= 0;
    endtask
    
    // Task to wait for read data
    task automatic wait_read_data(
        output [ID_WIDTH-1:0] id,
        output [DATA_WIDTH-1:0] data,
        output [1:0] resp,
        output last
    );
        $display("[%0t] BFM: Waiting for READ_DATA", $time);
        
        @(posedge aclk iff rvalid);
        id = rid;
        data = rdata;
        resp = rresp;
        last = rlast;
        
        $display("[%0t] BFM: Got READ_DATA - id=%0d, data=0x%0h, resp=%0d, last=%0b", 
                 $time, id, data, resp, last);
    endtask
    
    // Task to perform complete write transaction
    task automatic write_transaction(
        input [ID_WIDTH-1:0]    id,
        input [ADDR_WIDTH-1:0]  addr,
        input [7:0]             len,
        input [2:0]             size,
        input [1:0]             burst,
        input [DATA_WIDTH-1:0]  data[],
        input [(DATA_WIDTH/8)-1:0] strb[]
    );
        logic [ID_WIDTH-1:0] resp_id;
        logic [1:0] resp;
        
        $display("[%0t] BFM: Starting WRITE transaction - addr=0x%0h, len=%0d", $time, addr, len);
        
        // Drive address
        drive_write_addr(id, addr, len, size, burst);
        
        // Drive data beats
        for (int i = 0; i <= len; i++) begin
            drive_write_data(data[i], strb[i], (i == len));
        end
        
        // Wait for response
        wait_write_resp(resp_id, resp);
        
        $display("[%0t] BFM: WRITE transaction completed", $time);
    endtask
    
    // Task to perform complete read transaction
    task automatic read_transaction(
        input [ID_WIDTH-1:0]    id,
        input [ADDR_WIDTH-1:0]  addr,
        input [7:0]             len,
        input [2:0]             size,
        input [1:0]             burst,
        output [DATA_WIDTH-1:0] data[],
        output [1:0]            resp[]
    );
        logic [ID_WIDTH-1:0] resp_id;
        logic [1:0] beat_resp;
        logic last;
        
        $display("[%0t] BFM: Starting READ transaction - addr=0x%0h, len=%0d", $time, addr, len);
        
        // Drive address
        drive_read_addr(id, addr, len, size, burst);
        
        // Collect data beats
        for (int i = 0; i <= len; i++) begin
            wait_read_data(resp_id, data[i], resp[i], last);
            if (last && i != len) begin
                $display("[%0t] BFM: WARNING - Early RLAST at beat %0d", $time, i);
            end
        end
        
        $display("[%0t] BFM: READ transaction completed", $time);
    endtask
    
endinterface : axi4_master_driver_bfm
