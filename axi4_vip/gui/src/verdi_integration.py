#!/usr/bin/env python3
"""
Verdi Integration Module
Provides enhanced Verdi integration with auto-loading capabilities
"""

import os

class VerdiIntegration:
    """Provides Verdi integration features for VIP environment"""
    
    def __init__(self):
        self.verdi_home = os.environ.get('VERDI_HOME', '/home/eda_tools/synopsys/verdi/W-2024.09-SP1')
        
    def generate_verdi_scripts(self, output_dir):
        """Generate Verdi helper scripts"""
        
        scripts_dir = os.path.join(output_dir, "sim", "scripts")
        os.makedirs(scripts_dir, exist_ok=True)
        
        # Generate Verdi signal file for commonly used signals
        self._generate_signal_file(scripts_dir)
        
        # Generate Verdi session file
        self._generate_session_file(scripts_dir)
        
        # Generate auto-load script
        self._generate_auto_load_script(scripts_dir)
        
    def _generate_signal_file(self, scripts_dir):
        """Generate signal file for Verdi"""
        
        signal_file = os.path.join(scripts_dir, "axi4_signals.rc")
        
        content = """# AXI4 Signal Groups for Verdi
# Auto-generated signal grouping

# Clock and Reset
Group {
    Clock_Reset {
        hdl_top.aclk
        hdl_top.aresetn
    }
}

# Master 0 - Write Address Channel
Group {
    M0_AW {
        hdl_top.dut_wrapper.m0_awid
        hdl_top.dut_wrapper.m0_awaddr
        hdl_top.dut_wrapper.m0_awlen
        hdl_top.dut_wrapper.m0_awsize
        hdl_top.dut_wrapper.m0_awburst
        hdl_top.dut_wrapper.m0_awlock
        hdl_top.dut_wrapper.m0_awcache
        hdl_top.dut_wrapper.m0_awprot
        hdl_top.dut_wrapper.m0_awqos
        hdl_top.dut_wrapper.m0_awvalid
        hdl_top.dut_wrapper.m0_awready
    }
}

# Master 0 - Write Data Channel
Group {
    M0_W {
        hdl_top.dut_wrapper.m0_wdata
        hdl_top.dut_wrapper.m0_wstrb
        hdl_top.dut_wrapper.m0_wlast
        hdl_top.dut_wrapper.m0_wvalid
        hdl_top.dut_wrapper.m0_wready
    }
}

# Master 0 - Write Response Channel
Group {
    M0_B {
        hdl_top.dut_wrapper.m0_bid
        hdl_top.dut_wrapper.m0_bresp
        hdl_top.dut_wrapper.m0_bvalid
        hdl_top.dut_wrapper.m0_bready
    }
}

# Master 0 - Read Address Channel
Group {
    M0_AR {
        hdl_top.dut_wrapper.m0_arid
        hdl_top.dut_wrapper.m0_araddr
        hdl_top.dut_wrapper.m0_arlen
        hdl_top.dut_wrapper.m0_arsize
        hdl_top.dut_wrapper.m0_arburst
        hdl_top.dut_wrapper.m0_arlock
        hdl_top.dut_wrapper.m0_arcache
        hdl_top.dut_wrapper.m0_arprot
        hdl_top.dut_wrapper.m0_arqos
        hdl_top.dut_wrapper.m0_arvalid
        hdl_top.dut_wrapper.m0_arready
    }
}

# Master 0 - Read Data Channel
Group {
    M0_R {
        hdl_top.dut_wrapper.m0_rid
        hdl_top.dut_wrapper.m0_rdata
        hdl_top.dut_wrapper.m0_rresp
        hdl_top.dut_wrapper.m0_rlast
        hdl_top.dut_wrapper.m0_rvalid
        hdl_top.dut_wrapper.m0_rready
    }
}

# UVM Test Information
Group {
    UVM_Test_Info {
        hvl_top.uvm_test_top
        hvl_top.uvm_test_top.env
        hvl_top.uvm_test_top.env.scoreboard
    }
}
"""
        
        with open(signal_file, 'w') as f:
            f.write(content)
            
    def _generate_session_file(self, scripts_dir):
        """Generate Verdi session file"""
        
        session_file = os.path.join(scripts_dir, "axi4_session.ses")
        
        content = """# Verdi Session File
# Auto-generated for AXI4 VIP

# Window layout
verdiWindowResize -win $_Verdi_1 "1920" "1080"
verdiWindowWorkMode -win $_Verdi_1 -hardwareDebug

# Load signal file
verdiSetActWin -dock widgetDock_<Signal>
wvLoadSignalFile "./scripts/axi4_signals.rc"

# Set up waveform window
wvSetPosition -win $_nWave1 {("G1" 0)}
wvOpenFile -win $_nWave1 {$(ls -t waves/*.fsdb | head -1)}
wvGetSignalOpen -win $_nWave1
wvGetSignalSetScope -win $_nWave1 "/hdl_top"

# Add clock and reset
wvAddSignal -win $_nWave1 "/hdl_top/aclk" "/hdl_top/aresetn"

# Zoom to fit
wvZoomAll -win $_nWave1

# Set cursor to time 0
wvSetCursor -win $_nWave1 0.000000

# Open source browser
srcHBSelect "hdl_top" -win $_Verdi_1
srcSetScope -win $_nTrace1 "hdl_top" -delim "."
srcSelect -win $_nTrace1 -range {1 1 1 1} -backward

# Open UVM browser
verdiDockWidgetDisplay -dock widgetDock_<UVM>
"""
        
        with open(session_file, 'w') as f:
            f.write(content)
            
    def _generate_auto_load_script(self, scripts_dir):
        """Generate auto-load script for Verdi"""
        
        script_file = os.path.join(scripts_dir, "verdi_auto_load.tcl")
        
        content = """# Verdi Auto-Load Script
# Automatically loads FSDB and sets up environment

proc auto_load_verdi {} {
    # Find the most recent FSDB file
    set fsdb_files [glob -nocomplain "./waves/*.fsdb"]
    if {[llength $fsdb_files] == 0} {
        puts "Error: No FSDB files found in ./waves/"
        return
    }
    
    # Sort by modification time and get the latest
    set latest_fsdb ""
    set latest_time 0
    foreach fsdb $fsdb_files {
        set mtime [file mtime $fsdb]
        if {$mtime > $latest_time} {
            set latest_time $mtime
            set latest_fsdb $fsdb
        }
    }
    
    puts "Loading FSDB: $latest_fsdb"
    
    # Open the FSDB file
    openDatabase $latest_fsdb
    
    # Load the KDB if available
    if {[file exists "./simv.daidir/kdb"]} {
        puts "Loading KDB database..."
        debImport "-dbdir" "./simv.daidir/kdb"
    }
    
    # Set up default windows
    verdiWindowWorkMode -hardwareDebug
    
    # Open waveform window
    wvCreateWindow
    
    # Load signal groups if available
    if {[file exists "./scripts/axi4_signals.rc"]} {
        wvLoadSignalFile "./scripts/axi4_signals.rc"
    }
    
    # Add some default signals
    wvAddSignal "/hdl_top/aclk"
    wvAddSignal "/hdl_top/aresetn"
    
    # Zoom to fit
    wvZoomAll
    
    puts "Verdi environment loaded successfully"
}

# Auto-execute on load
auto_load_verdi
"""
        
        with open(script_file, 'w') as f:
            f.write(content)
            
    def enhance_makefile_verdi_target(self, makefile_content):
        """Enhance the Makefile verdi target with additional features"""
        
        # This would be called to enhance an existing Makefile
        # For now, the enhanced target is already integrated in vip_environment_generator.py
        pass
        
    def generate_verdi_config(self, output_dir):
        """Generate Verdi configuration file"""
        
        config_file = os.path.join(output_dir, "sim", ".verdirc")
        
        content = """# Verdi Configuration File
# Auto-generated for AXI4 VIP

# Enable FSDB dumping
setenv VERDI_FSDB_GATE_DUMPING_ENABLE 1

# Set default window size
setenv VERDI_WINDOW_WIDTH 1920
setenv VERDI_WINDOW_HEIGHT 1080

# Enable KDB loading
setenv VERDI_KDB_ENABLE 1

# Set color scheme
setenv VERDI_COLOR_SCHEME Modern

# Enable transaction recording
setenv VERDI_TRANS_RECORDING 1

# Auto-load preferences
VERDI_HOME = {verdi_home}
""".format(verdi_home=self.verdi_home)
        
        with open(config_file, 'w') as f:
            f.write(content)

def integrate_verdi_features(vip_generator):
    """Integrate Verdi features into VIP generator"""
    
    verdi = VerdiIntegration()
    
    # Generate Verdi scripts
    verdi.generate_verdi_scripts(vip_generator.output_dir)
    
    # Generate Verdi config
    verdi.generate_verdi_config(vip_generator.output_dir)
    
    print("Verdi integration features added:")
    print("  - Auto-load script for last FSDB")
    print("  - Signal grouping file")
    print("  - Session file for window layout")
    print("  - Enhanced 'make verdi' target")

if __name__ == "__main__":
    # Test the Verdi integration
    verdi = VerdiIntegration()
    print(f"Verdi home: {verdi.verdi_home}")
    print("Verdi integration module loaded")