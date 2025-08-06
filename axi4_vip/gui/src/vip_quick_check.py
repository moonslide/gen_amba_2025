#!/usr/bin/env python3
"""Quick check utility for VIP environment generator"""

import os
import sys
import subprocess

def check_vip_generator_health():
    """Quick health check for VIP environment generator"""
    issues = []
    
    # Check file size
    vip_gen_path = os.path.join(os.path.dirname(__file__), "vip_environment_generator.py")
    if os.path.exists(vip_gen_path):
        file_size = os.path.getsize(vip_gen_path)
        file_size_mb = file_size / (1024 * 1024)
        
        if file_size_mb > 1:
            issues.append(f"Large file size: {file_size_mb:.2f} MB (may cause slow imports)")
            
        # Check line count
        try:
            result = subprocess.run(['wc', '-l', vip_gen_path], 
                                  capture_output=True, text=True)
            if result.returncode == 0:
                line_count = int(result.stdout.split()[0])
                if line_count > 3000:
                    issues.append(f"High line count: {line_count} lines")
        except:
            pass
    else:
        issues.append("VIP environment generator file not found")
        
    # Check for bytecode
    pycache_dir = os.path.join(os.path.dirname(vip_gen_path), "__pycache__")
    has_bytecode = False
    if os.path.exists(pycache_dir):
        pyc_files = [f for f in os.listdir(pycache_dir) 
                     if f.startswith("vip_environment_generator") and f.endswith(".pyc")]
        has_bytecode = len(pyc_files) > 0
        
    if not has_bytecode:
        issues.append("No bytecode cache found (run precompile_vip_generator.py)")
        
    return issues

def get_vip_generator_stats():
    """Get statistics about the VIP generator"""
    vip_gen_path = os.path.join(os.path.dirname(__file__), "vip_environment_generator.py")
    
    stats = {
        "exists": os.path.exists(vip_gen_path),
        "size_mb": 0,
        "lines": 0,
        "has_bytecode": False,
        "python_version": sys.version.split()[0]
    }
    
    if stats["exists"]:
        stats["size_mb"] = os.path.getsize(vip_gen_path) / (1024 * 1024)
        
        try:
            with open(vip_gen_path, 'r') as f:
                stats["lines"] = sum(1 for _ in f)
        except:
            pass
            
        pycache_dir = os.path.join(os.path.dirname(vip_gen_path), "__pycache__")
        if os.path.exists(pycache_dir):
            pyc_files = [f for f in os.listdir(pycache_dir) 
                         if f.startswith("vip_environment_generator") and f.endswith(".pyc")]
            stats["has_bytecode"] = len(pyc_files) > 0
            
    return stats

if __name__ == "__main__":
    print("VIP Environment Generator Health Check")
    print("=" * 40)
    
    stats = get_vip_generator_stats()
    print(f"File exists: {stats['exists']}")
    print(f"File size: {stats['size_mb']:.2f} MB")
    print(f"Line count: {stats['lines']}")
    print(f"Has bytecode: {stats['has_bytecode']}")
    print(f"Python version: {stats['python_version']}")
    
    print("\nPotential Issues:")
    issues = check_vip_generator_health()
    if issues:
        for issue in issues:
            print(f"  ⚠️  {issue}")
    else:
        print("  ✅ No issues found")
        
    print("\nRecommendations:")
    if stats['size_mb'] > 1:
        print("  • Consider using VIP_FAST_MODE=true for quick testing")
    if not stats['has_bytecode']:
        print("  • Run: python3 precompile_vip_generator.py")