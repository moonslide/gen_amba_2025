// AXI4 Slave Driver
class axi4_slave_driver extends uvm_driver #(axi4_transaction);
    `uvm_component_utils(axi4_slave_driver)
    
    virtual axi4_if vif;
    int slave_id;
    bit [7:0] memory[int];
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual axi4_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
    endfunction
    
    task run_phase(uvm_phase phase);
        fork
            handle_write_address();
            handle_write_data();
            handle_write_response();
            handle_read_address();
            handle_read_data();
        join
    endtask
    
    task handle_write_address();
        forever begin
            @(posedge vif.aclk);
            if(vif.awvalid) begin
                vif.awready <= 1'b1;
                @(posedge vif.aclk);
                vif.awready <= 1'b0;
            end
        end
    endtask
    
    task handle_write_data();
        forever begin
            @(posedge vif.aclk);
            if(vif.wvalid) begin
                vif.wready <= 1'b1;
                @(posedge vif.aclk);
                vif.wready <= 1'b0;
            end
        end
    endtask
    
    task handle_write_response();
        forever begin
            // Simple response after each write
            @(posedge vif.aclk);
            vif.bvalid <= 1'b1;
            vif.bresp <= 2'b00; // OKAY
            wait(vif.bready);
            @(posedge vif.aclk);
            vif.bvalid <= 1'b0;
        end
    endtask
    
    task handle_read_address();
        forever begin
            @(posedge vif.aclk);
            if(vif.arvalid) begin
                vif.arready <= 1'b1;
                @(posedge vif.aclk);
                vif.arready <= 1'b0;
            end
        end
    endtask
    
    task handle_read_data();
        // Simplified read data handling
        forever begin
            @(posedge vif.aclk);
            vif.rvalid <= 1'b1;
            vif.rdata <= $random;
            vif.rresp <= 2'b00;
            vif.rlast <= 1'b1;
            wait(vif.rready);
            @(posedge vif.aclk);
            vif.rvalid <= 1'b0;
        end
    endtask
endclass
