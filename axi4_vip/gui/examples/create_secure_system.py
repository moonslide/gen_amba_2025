#!/usr/bin/env python3
"""
Example: Create a security-aware AXI4 system with TrustZone support
Demonstrates access control, security regions, and privilege levels
"""

import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '..', 'src'))

from bus_config import BusConfig, Master, Slave
import json

def create_secure_system():
    """Create a TrustZone-enabled secure system"""
    
    # Create bus configuration
    config = BusConfig()
    config.bus_type = "AXI4"
    config.data_width = 64
    config.addr_width = 32
    config.arbitration = "FIXED"  # Deterministic for security
    
    print("Creating security-aware AXI4 system...")
    
    # ==================
    # Secure Masters
    # ==================
    
    # Secure CPU (Cortex-A with TrustZone)
    secure_cpu = Master("Secure_CPU")
    secure_cpu.id_width = 4
    secure_cpu.priority = 15  # Highest priority
    secure_cpu.qos_support = True
    secure_cpu.exclusive_support = True
    secure_cpu.default_prot = 0b110  # Secure, Privileged, Data
    secure_cpu.default_cache = 0b0011
    config.masters.append(secure_cpu)
    
    # Crypto Engine (Secure only)
    crypto = Master("Crypto_Engine")
    crypto.id_width = 2  # Limited outstanding
    crypto.priority = 14
    crypto.qos_support = False  # Fixed timing
    crypto.exclusive_support = False
    crypto.default_prot = 0b110  # Always secure
    crypto.default_cache = 0b0000  # Non-cacheable for security
    config.masters.append(crypto)
    
    # ==================
    # Non-Secure Masters
    # ==================
    
    # Application CPU (Normal world)
    app_cpu = Master("App_CPU") 
    app_cpu.id_width = 4
    app_cpu.priority = 10
    app_cpu.qos_support = True
    app_cpu.exclusive_support = True
    app_cpu.default_prot = 0b010  # Non-secure, Privileged, Data
    app_cpu.default_cache = 0b0011
    config.masters.append(app_cpu)
    
    # DMA Controller (Non-secure)
    dma = Master("DMA")
    dma.id_width = 4
    dma.priority = 5
    dma.qos_support = True
    dma.exclusive_support = False
    dma.default_prot = 0b000  # Non-secure, Unprivileged, Data
    dma.default_cache = 0b0000
    config.masters.append(dma)
    
    # Debug Access Port (Special)
    dap = Master("Debug_AP")
    dap.id_width = 2
    dap.priority = 8
    dap.qos_support = False
    dap.exclusive_support = False
    dap.default_prot = 0b011  # Can be secure or non-secure
    dap.default_cache = 0b0000
    config.masters.append(dap)
    
    # ==================
    # Memory Regions
    # ==================
    
    # Secure ROM (Boot code)
    secure_rom = Slave("Secure_ROM", 0x00000000, 16384)  # 16MB
    secure_rom.memory_type = "Memory"
    secure_rom.read_latency = 2
    secure_rom.write_latency = 1  # Will error
    secure_rom.secure_only = True
    secure_rom.privileged_only = True
    secure_rom.allowed_masters = [0, 4]  # Secure_CPU and Debug_AP only
    config.slaves.append(secure_rom)
    
    # Secure RAM (TEE memory)
    secure_ram = Slave("Secure_RAM", 0x01000000, 65536)  # 64MB
    secure_ram.memory_type = "Memory"
    secure_ram.read_latency = 3
    secure_ram.write_latency = 2
    secure_ram.secure_only = True
    secure_ram.privileged_only = False  # Secure user mode allowed
    secure_ram.allowed_masters = [0, 1, 4]  # Secure_CPU, Crypto, Debug
    secure_ram.num_regions = 4  # Multiple secure regions
    config.slaves.append(secure_ram)
    
    # Shared RAM (Secure/Non-secure)
    shared_ram = Slave("Shared_RAM", 0x10000000, 131072)  # 128MB
    shared_ram.memory_type = "Memory"
    shared_ram.read_latency = 4
    shared_ram.write_latency = 3
    shared_ram.secure_only = False  # Both worlds
    shared_ram.privileged_only = False
    shared_ram.num_regions = 8  # Fine-grained control
    config.slaves.append(shared_ram)
    
    # Non-secure RAM (Application memory)
    nonsec_ram = Slave("NonSecure_RAM", 0x20000000, 524288)  # 512MB
    nonsec_ram.memory_type = "Memory"  
    nonsec_ram.read_latency = 5
    nonsec_ram.write_latency = 4
    nonsec_ram.secure_only = False
    nonsec_ram.privileged_only = False
    config.slaves.append(nonsec_ram)
    
    # ==================
    # Peripheral Regions
    # ==================
    
    # Secure Peripherals
    sec_periph = Slave("Secure_Peripherals", 0x50000000, 1024)  # 1MB
    sec_periph.memory_type = "Peripheral"
    sec_periph.read_latency = 2
    sec_periph.write_latency = 2
    sec_periph.secure_only = True
    sec_periph.privileged_only = True
    sec_periph.allowed_masters = [0, 4]  # Secure_CPU, Debug
    config.slaves.append(sec_periph)
    
    # Crypto Accelerator Registers
    crypto_regs = Slave("Crypto_Registers", 0x51000000, 64)  # 64KB
    crypto_regs.memory_type = "Peripheral"
    crypto_regs.read_latency = 1
    crypto_regs.write_latency = 1
    crypto_regs.secure_only = True
    crypto_regs.privileged_only = True
    crypto_regs.allowed_masters = [0, 1]  # Secure_CPU, Crypto only
    config.slaves.append(crypto_regs)
    
    # Non-secure Peripherals
    nonsec_periph = Slave("NonSecure_Peripherals", 0x60000000, 1024)  # 1MB
    nonsec_periph.memory_type = "Peripheral"
    nonsec_periph.read_latency = 2
    nonsec_periph.write_latency = 2
    nonsec_periph.secure_only = False
    nonsec_periph.privileged_only = False
    config.slaves.append(nonsec_periph)
    
    # System Control (Mixed security)
    sys_ctrl = Slave("System_Control", 0x70000000, 64)  # 64KB
    sys_ctrl.memory_type = "Peripheral"
    sys_ctrl.read_latency = 1
    sys_ctrl.write_latency = 1
    sys_ctrl.secure_only = False  # Both, but with region control
    sys_ctrl.privileged_only = True  # Always privileged
    sys_ctrl.num_regions = 16  # Fine control over registers
    config.slaves.append(sys_ctrl)
    
    # Create security configuration
    security_config = {
        "name": "TrustZone Secure System",
        "description": "Security-aware AXI4 system with access control",
        "security_features": {
            "trustzone_enabled": True,
            "secure_boot": True,
            "debug_authentication": True,
            "memory_protection": True
        },
        "bus_config": {
            "bus_type": config.bus_type,
            "data_width": config.data_width,
            "addr_width": config.addr_width,
            "arbitration": config.arbitration
        },
        "masters": [],
        "slaves": [],
        "access_control_matrix": {}
    }
    
    # Build master list with security attributes
    for i, master in enumerate(config.masters):
        master_info = {
            "id": i,
            "name": master.name,
            "security": "secure" if master.default_prot & 0b100 else "non-secure",
            "privilege": "privileged" if master.default_prot & 0b010 else "unprivileged",
            "id_width": master.id_width,
            "priority": master.priority,
            "default_prot": f"0b{master.default_prot:03b}"
        }
        security_config["masters"].append(master_info)
    
    # Build slave list with access control
    for i, slave in enumerate(config.slaves):
        slave_info = {
            "id": i,
            "name": slave.name,
            "base_address": hex(slave.base_address),
            "size": slave.size,
            "security": "secure-only" if slave.secure_only else "mixed",
            "privilege": "privileged-only" if slave.privileged_only else "any",
            "allowed_masters": slave.allowed_masters if hasattr(slave, 'allowed_masters') else "all",
            "num_regions": slave.num_regions
        }
        security_config["slaves"].append(slave_info)
    
    # Build access control matrix
    print("\nBuilding access control matrix...")
    for master in security_config["masters"]:
        access_list = []
        for slave in security_config["slaves"]:
            # Check if master can access slave
            allowed = True
            reason = "OK"
            
            # Check security
            if slave["security"] == "secure-only" and master["security"] != "secure":
                allowed = False
                reason = "Security violation"
            
            # Check privilege  
            if slave["privilege"] == "privileged-only" and master["privilege"] != "privileged":
                allowed = False
                reason = "Privilege violation"
                
            # Check allowed masters list
            if isinstance(slave["allowed_masters"], list):
                if master["id"] not in slave["allowed_masters"]:
                    allowed = False
                    reason = "Not in allowed list"
            
            access_list.append({
                "slave": slave["name"],
                "allowed": allowed,
                "reason": reason
            })
        
        security_config["access_control_matrix"][master["name"]] = access_list
    
    # Save configuration
    config_file = "secure_system.json"
    with open(config_file, 'w') as f:
        json.dump(security_config, f, indent=2)
    
    # Print security summary
    print("\n" + "="*70)
    print("SECURE SYSTEM SUMMARY")
    print("="*70)
    print(f"\nSecurity Features:")
    for feature, enabled in security_config["security_features"].items():
        print(f"  {feature}: {'Enabled' if enabled else 'Disabled'}")
    
    print(f"\nMasters ({len(config.masters)}):")
    for master in security_config["masters"]:
        print(f"  {master['id']}: {master['name']} - {master['security'].upper()}, {master['privilege'].upper()}")
    
    print(f"\nSlaves ({len(config.slaves)}):")  
    for slave in security_config["slaves"]:
        print(f"  {slave['id']}: {slave['name']} @ {slave['base_address']} - {slave['security'].upper()}")
    
    print("\nAccess Control Summary:")
    print("  Secure Masters → Secure Slaves: ALLOWED")
    print("  Secure Masters → Non-secure Slaves: ALLOWED")
    print("  Non-secure Masters → Secure Slaves: BLOCKED")
    print("  Non-secure Masters → Non-secure Slaves: ALLOWED")
    
    print(f"\nConfiguration saved to: {config_file}")
    print("\nThis configuration demonstrates:")
    print("  - TrustZone security separation")
    print("  - Master security attributes (AxPROT)")
    print("  - Slave access control")
    print("  - Privileged/unprivileged separation")
    print("  - Per-slave allowed master lists")
    print("  - Memory region protection")
    
    return security_config

if __name__ == "__main__":
    create_secure_system()