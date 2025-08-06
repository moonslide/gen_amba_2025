# Verdi Auto-Load Script
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
