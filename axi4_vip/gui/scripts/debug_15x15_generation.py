#!/usr/bin/env python3
"""
Debug script to understand exactly where 15x15 generation is failing
"""

import os
import sys
import traceback
from datetime import datetime

# Add parent directory to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))

def debug_generation_step_by_step():
    """Debug each step of VIP generation"""
    
    print("=== Debug: 15x15 VIP Generation Step-by-Step ===\n")
    
    try:
        from bus_config import BusConfig, Master, Slave
        from vip_environment_generator import VIPEnvironmentGenerator
        print("✅ Modules imported")
    except Exception as e:
        print(f"❌ Import failed: {e}")
        return
    
    # Create configuration
    print("📊 Creating configuration...")
    config = BusConfig()
    config.bus_type = "AXI4"
    config.data_width = 64
    config.addr_width = 32
    
    # Add masters and slaves
    for i in range(15):
        config.masters.append(Master(name=f"Master{i}"))
        config.slaves.append(Slave(
            name=f"Slave{i}",
            base_address=i * 0x100000,
            size=1024
        ))
    
    print(f"✅ Configuration: {len(config.masters)}x{len(config.slaves)}")
    
    # Create output directory
    output_base = os.path.join(os.path.dirname(__file__), "..", "debug_output")
    os.makedirs(output_base, exist_ok=True)
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    test_output_dir = os.path.join(output_base, f"debug_15x15_{timestamp}")
    
    print(f"📁 Output directory: {test_output_dir}")
    
    # Create generator
    print("\n🔧 Creating generator...")
    try:
        generator = VIPEnvironmentGenerator(config, "rtl_integration")
        print("✅ Generator created")
    except Exception as e:
        print(f"❌ Generator creation failed: {e}")
        traceback.print_exc()
        return
    
    # Check thresholds
    matrix_size = len(config.masters) * len(config.slaves)
    max_dim = max(len(config.masters), len(config.slaves))
    
    print(f"\n🔍 Threshold analysis:")
    print(f"   Matrix size: {matrix_size}")
    print(f"   Max dimension: {max_dim}")
    print(f"   matrix_size > 300: {matrix_size > 300}")
    print(f"   max_dim > 10: {max_dim > 10}")
    
    # Step 1: Validation
    print(f"\n📝 Step 1: Validation...")
    try:
        generator._validate_configuration()
        print("✅ Validation passed")
        if generator.warnings:
            print(f"⚠️  Warnings: {generator.warnings}")
    except Exception as e:
        print(f"❌ Validation failed: {e}")
        traceback.print_exc()
        return
    
    # Step 2: Directory creation
    print(f"\n📁 Step 2: Directory creation...")
    try:
        env_name = f"axi4_vip_env_{generator.mode}"
        env_path = os.path.join(test_output_dir, env_name)
        print(f"   Target path: {env_path}")
        
        generator._create_directory_structure(env_path)
        print("✅ Directory structure created")
        
        # Verify directory exists
        if os.path.exists(env_path):
            print(f"✅ Directory exists: {env_path}")
            subdirs = os.listdir(env_path)
            print(f"   Subdirectories: {len(subdirs)}")
        else:
            print(f"❌ Directory not created: {env_path}")
            return
            
    except Exception as e:
        print(f"❌ Directory creation failed: {e}")
        traceback.print_exc()
        return
    
    # Step 3: Package files
    print(f"\n📦 Step 3: Package files...")
    try:
        generator._generate_package_files(env_path)
        print("✅ Package files generated")
    except Exception as e:
        print(f"❌ Package files failed: {e}")
        traceback.print_exc()
        return
    
    # Step 4: Interface files
    print(f"\n🔌 Step 4: Interface files...")
    try:
        generator._generate_interface_files(env_path)
        print("✅ Interface files generated")
    except Exception as e:
        print(f"❌ Interface files failed: {e}")
        traceback.print_exc()
        return
    
    # Step 5: RTL wrapper (this is where hang occurred)
    print(f"\n⚡ Step 5: RTL wrapper generation...")
    try:
        if generator.mode == "rtl_integration":
            print("   Calling _generate_rtl_wrapper...")
            generator._generate_rtl_wrapper(env_path)
            print("✅ RTL wrapper generated")
        else:
            print("   Skipping RTL wrapper (not rtl_integration mode)")
    except Exception as e:
        print(f"❌ RTL wrapper failed: {e}")
        traceback.print_exc()
        # Don't return - this might be expected to fail
    
    # Step 6: Final verification
    print(f"\n✅ Step 6: Final verification...")
    if os.path.exists(env_path):
        print(f"✅ Environment path exists: {env_path}")
        
        # List contents
        try:
            contents = os.listdir(env_path)
            print(f"   Contents ({len(contents)}): {contents[:10]}")  # First 10 items
            
            # Check for key directories
            key_dirs = ["agent", "env", "intf", "pkg", "sim"]
            for key_dir in key_dirs:
                dir_path = os.path.join(env_path, key_dir)
                if os.path.exists(dir_path):
                    print(f"   ✅ {key_dir}/")
                else:
                    print(f"   ❌ {key_dir}/ missing")
                    
        except Exception as e:
            print(f"   ❌ Cannot list contents: {e}")
    else:
        print(f"❌ Environment path does not exist: {env_path}")
        return
    
    print(f"\n🎉 SUCCESS: Environment should be valid")
    print(f"   Path: {env_path}")
    
    # Test what the actual generate_environment returns
    print(f"\n🧪 Testing full generate_environment call...")
    try:
        result = generator.generate_environment(test_output_dir)
        print(f"✅ Full generation result: {result}")
        return result is not None
    except Exception as e:
        print(f"❌ Full generation failed: {e}")
        traceback.print_exc()
        return False

if __name__ == "__main__":
    success = debug_generation_step_by_step()
    
    if success:
        print("\n🎉 DEBUG SUCCESS: Generation is working!")
    else:
        print("\n❌ DEBUG FAILED: Issues found in generation process")
    
    sys.exit(0 if success else 1)