// AXI4 Environment
class axi4_env extends uvm_env;
    `uvm_component_utils(axi4_env)
    
    axi4_master_agent master_agents[NUM_MASTERS];
    axi4_slave_agent slave_agents[NUM_SLAVES];
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Create master agents
        for(int i = 0; i < NUM_MASTERS; i++) begin
            master_agents[i] = axi4_master_agent::type_id::create($sformatf("master_agent_%0d", i), this);
            master_agents[i].master_id = i;
        end
        
        // Create slave agents
        for(int i = 0; i < NUM_SLAVES; i++) begin
            slave_agents[i] = axi4_slave_agent::type_id::create($sformatf("slave_agent_%0d", i), this);
            slave_agents[i].slave_id = i;
        end
    endfunction
endclass
