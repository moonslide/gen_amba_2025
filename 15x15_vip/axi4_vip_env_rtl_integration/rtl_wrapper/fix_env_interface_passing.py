#!/usr/bin/env python3
"""
Fix environment to properly pass virtual interfaces to agents
"""

import os
import sys
import shutil
from datetime import datetime

def backup_file(filepath):
    """Create backup of file before modifying"""
    backup_path = f"{filepath}.backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    shutil.copy2(filepath, backup_path)
    print(f"✓ Backed up {os.path.basename(filepath)}")
    return backup_path

def fix_environment(env_path):
    """Fix the environment to pass interfaces to agents"""
    
    print(f"\n📝 Fixing environment to pass virtual interfaces to agents...")
    
    # Read the file
    with open(env_path, 'r') as f:
        content = f.read()
    
    # Find the build_phase function and add interface passing
    old_build = """        // Create agents
        foreach(master_agent[i]) begin
            master_agent[i] = axi4_master_agent::type_id::create($sformatf("master_agent[%0d]", i), this);
        end
        
        foreach(slave_agent[i]) begin
            slave_agent[i] = axi4_slave_agent::type_id::create($sformatf("slave_agent[%0d]", i), this);
        end"""
    
    new_build = """        // Create agents and pass interfaces
        foreach(master_agent[i]) begin
            master_agent[i] = axi4_master_agent::type_id::create($sformatf("master_agent[%0d]", i), this);
            
            // Get and pass virtual interface to agent
            begin
                virtual axi4_if vif;
                if(uvm_config_db#(virtual axi4_if)::get(this, "", $sformatf("master_if_%0d", i), vif)) begin
                    uvm_config_db#(virtual axi4_if)::set(this, $sformatf("master_agent[%0d]*", i), "vif", vif);
                    `uvm_info(get_type_name(), $sformatf("Passed master_if_%0d to master_agent[%0d]", i, i), UVM_HIGH)
                end else begin
                    `uvm_warning(get_type_name(), $sformatf("master_if_%0d not found in config_db", i))
                end
            end
        end
        
        foreach(slave_agent[i]) begin
            slave_agent[i] = axi4_slave_agent::type_id::create($sformatf("slave_agent[%0d]", i), this);
            
            // Get and pass virtual interface to agent
            begin
                virtual axi4_if vif;
                if(uvm_config_db#(virtual axi4_if)::get(this, "", $sformatf("slave_if_%0d", i), vif)) begin
                    uvm_config_db#(virtual axi4_if)::set(this, $sformatf("slave_agent[%0d]*", i), "vif", vif);
                    `uvm_info(get_type_name(), $sformatf("Passed slave_if_%0d to slave_agent[%0d]", i, i), UVM_HIGH)
                end else begin
                    `uvm_warning(get_type_name(), $sformatf("slave_if_%0d not found in config_db", i))
                end
            end
        end"""
    
    content = content.replace(old_build, new_build)
    
    # Write the fixed content
    with open(env_path, 'w') as f:
        f.write(content)
    
    print(f"✓ Fixed environment to pass virtual interfaces to agents")
    return True

def main():
    """Main function to fix interface passing in environment"""
    
    print("\n" + "="*60)
    print("🔧 AXI4 VIP Environment Interface Passing Fix")
    print("="*60)
    
    # Define paths
    base_path = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration"
    env_path = os.path.join(base_path, "env/axi4_env.sv")
    
    # Check if file exists
    if not os.path.exists(env_path):
        print(f"❌ Error: Environment not found at {env_path}")
        return False
    
    # Backup file
    backup_file(env_path)
    
    # Apply fix
    success = fix_environment(env_path)
    
    if success:
        print("\n" + "="*60)
        print("✅ Environment interface passing fix successfully applied!")
        print("\nKey improvements:")
        print("  • Environment now gets interfaces from config_db")
        print("  • Passes interfaces to agents before build")
        print("  • Agents can now pass to drivers")
        print("\nNext steps:")
        print("  1. Run: make clean")
        print("  2. Run: make run_fsdb TEST=axi4_simple_crossbar_test")
        print("  3. Check DUT signals in waveform")
        print("="*60)
    else:
        print("\n❌ Fix failed to apply")
        return False
    
    return True

if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)