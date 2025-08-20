#!/usr/bin/env python3
"""
Direct RTL Generator using enhanced gen_amba tools
Uses the native C tools with all features built-in
"""

import os
import subprocess
import logging
from datetime import datetime
from typing import Dict, List, Optional

logger = logging.getLogger(__name__)

class DirectRTLGenerator:
    """Generate RTL using enhanced gen_amba tools directly"""
    
    def __init__(self, project_config, settings):
        self.project = project_config
        self.settings = settings
        self.output_dir = settings['output_dir']
        
        # Paths to enhanced gen_amba tools
        self.gen_amba_base = "/home/timtim01/eda_test/project/gen_amba_2025"
        self.gen_axi = os.path.join(self.gen_amba_base, "gen_amba_axi/gen_amba_axi")
        self.gen_ahb = os.path.join(self.gen_amba_base, "gen_amba_ahb/gen_amba_ahb")
        self.gen_apb = os.path.join(self.gen_amba_base, "gen_amba_apb/gen_amba_apb")
        
    def generate(self):
        """Generate RTL using enhanced gen_amba tools"""
        rtl_dir = os.path.join(self.output_dir, 'rtl')
        os.makedirs(rtl_dir, exist_ok=True)
        
        # Generate interconnect using enhanced gen_amba_axi
        output_file = os.path.join(rtl_dir, f"{self.settings['project_name']}.v")
        
        # Build command with all new features
        cmd = [
            self.gen_axi,
            f"--master={len(self.project.masters)}",
            f"--slave={len(self.project.slaves)}",
            f"--module={self.settings['project_name']}",
            f"--output={output_file}"
        ]
        
        # Add address and data width
        if 'common' in self.settings:
            cmd.append(f"--addr-width={self.settings['common'].get('addr_width', 32)}")
            cmd.append(f"--data-width={self.settings['common'].get('data_width', 64)}")
        
        # Add prefix if specified
        if 'prefix' in self.settings:
            cmd.append(f"--prefix={self.settings['prefix']}")
        
        # Add protocol selection
        if self.settings['common'].get('protocol') == 'AXI3':
            cmd.append("--axi3")
        
        # Add new features based on settings
        if 'rtl' in self.settings:
            rtl = self.settings['rtl']
            
            # QoS support
            if rtl.get('gen_qos') or self.settings['common'].get('enable_qos'):
                cmd.append("--enable-qos")
                if 'qos_width' in rtl:
                    cmd.append(f"--qos-width={rtl['qos_width']}")
            
            # REGION support
            if rtl.get('gen_region') or self.settings['common'].get('enable_region'):
                cmd.append("--enable-region")
                if 'region_width' in rtl:
                    cmd.append(f"--region-width={rtl['region_width']}")
            
            # USER signals
            if rtl.get('gen_user') or self.settings['common'].get('enable_user'):
                cmd.append("--enable-user")
                if 'user_width' in rtl:
                    cmd.append(f"--user-width={rtl['user_width']}")
            
            # Firewall/Security
            if rtl.get('gen_firewall') or self.settings['common'].get('enable_firewall'):
                cmd.append("--enable-firewall")
            
            # CDC support
            if rtl.get('gen_cdc') or self.settings['common'].get('enable_cdc'):
                cmd.append("--enable-cdc")
                if 'clock_domains' in rtl:
                    cmd.append(f"--clock-domains={len(rtl['clock_domains'])}")
                elif 'num_clock_domains' in rtl:
                    cmd.append(f"--clock-domains={rtl['num_clock_domains']}")
        
        # Execute the command
        logger.info(f"Executing: {' '.join(cmd)}")
        try:
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True, check=True)
            logger.info(f"Generated RTL: {output_file}")
            
            # Generate supporting files if requested
            if self.settings.get('common', {}).get('gen_filelist'):
                self.generate_filelist(rtl_dir)
            
            if self.settings.get('common', {}).get('gen_makefile'):
                self.generate_makefile(rtl_dir)
            
            if self.settings.get('common', {}).get('gen_scripts'):
                self.generate_scripts(rtl_dir)
            
            if self.settings.get('common', {}).get('gen_documentation'):
                self.generate_documentation(rtl_dir)
            
            return {
                'success': True,
                'output_dir': rtl_dir,
                'files': [output_file]
            }
            
        except subprocess.CalledProcessError as e:
            logger.error(f"Generation failed: {e.stderr}")
            return {
                'success': False,
                'error': e.stderr
            }
        except Exception as e:
            logger.error(f"Unexpected error: {e}")
            return {
                'success': False,
                'error': str(e)
            }
    
    def generate_filelist(self, rtl_dir):
        """Generate filelist.f"""
        filelist = os.path.join(rtl_dir, 'filelist.f')
        content = f"""// Filelist for {self.settings['project_name']}
// Generated by Direct RTL Generator
// Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

+incdir+.
{self.settings['project_name']}.v
"""
        with open(filelist, 'w') as f:
            f.write(content)
        logger.info(f"Generated filelist: {filelist}")
    
    def generate_makefile(self, rtl_dir):
        """Generate Makefile"""
        makefile = os.path.join(rtl_dir, 'Makefile')
        content = f"""# Makefile for {self.settings['project_name']}
# Generated by Direct RTL Generator
# Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

PROJECT = {self.settings['project_name']}

# Simulator selection
SIM ?= vcs

# VCS options
VCS_FLAGS = -full64 -sverilog +v2k -timescale=1ns/1ps \\
            -debug_access+all -lca -kdb +lint=TFIPC-L

# Compile target
compile:
	$(SIM) $(VCS_FLAGS) -f filelist.f

# Run simulation
run: compile
	./simv

# Clean
clean:
	rm -rf simv* csrc *.log *.key DVEfiles

.PHONY: compile run clean
"""
        with open(makefile, 'w') as f:
            f.write(content)
        logger.info(f"Generated Makefile: {makefile}")
    
    def generate_scripts(self, rtl_dir):
        """Generate simulation scripts"""
        script = os.path.join(rtl_dir, 'run_sim.sh')
        content = f"""#!/bin/bash
# Simulation script for {self.settings['project_name']}
# Generated by Direct RTL Generator
# Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

echo "Starting simulation for {self.settings['project_name']}"
echo "======================================"

# Compile
make compile

if [ $? -ne 0 ]; then
    echo "Compilation failed!"
    exit 1
fi

# Run
make run

echo "Simulation complete!"
"""
        with open(script, 'w') as f:
            f.write(content)
        os.chmod(script, 0o755)
        logger.info(f"Generated script: {script}")
    
    def generate_documentation(self, rtl_dir):
        """Generate documentation"""
        doc_file = os.path.join(rtl_dir, f"{self.settings['project_name']}_readme.md")
        
        content = f"""# {self.settings['project_name']} - AXI Interconnect

Generated by Enhanced gen_amba_axi with Direct RTL Generator
Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## Configuration

- **Masters**: {len(self.project.masters)}
- **Slaves**: {len(self.project.slaves)}
- **Address Width**: {self.settings['common'].get('addr_width', 32)} bits
- **Data Width**: {self.settings['common'].get('data_width', 64)} bits
- **Protocol**: {self.settings['common'].get('protocol', 'AXI4')}

## Enhanced Features

"""
        
        if 'rtl' in self.settings:
            rtl = self.settings['rtl']
            if rtl.get('gen_qos'):
                content += "- **QoS**: Quality of Service enabled\n"
            if rtl.get('gen_region'):
                content += "- **REGION**: Memory region support enabled\n"
            if rtl.get('gen_user'):
                content += "- **USER**: User-defined signals enabled\n"
            if rtl.get('gen_firewall'):
                content += "- **Firewall**: Security access control enabled\n"
            if rtl.get('gen_cdc'):
                content += f"- **CDC**: Clock domain crossing enabled ({rtl.get('num_clock_domains', 2)} domains)\n"
        
        content += """
## Usage

### Compilation
```bash
make compile
```

### Simulation
```bash
make run
```

### Clean
```bash
make clean
```

## Files

- `{}.v` - Main interconnect module
- `filelist.f` - File list for compilation
- `Makefile` - Build automation
- `run_sim.sh` - Simulation script

## Notes

This interconnect was generated using the enhanced gen_amba_axi tool with
native support for AXI4 advanced features including QoS, REGION, USER signals,
security firewall, and clock domain crossing.

""".format(self.settings['project_name'])
        
        with open(doc_file, 'w') as f:
            f.write(content)
        logger.info(f"Generated documentation: {doc_file}")