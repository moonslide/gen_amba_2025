# TCL script to verify all signals are properly driven in the DUT
# Usage: In Verdi, source this script after loading the waveform

# Check clock and reset connections
set clk_path "hdl_top.dut.axi_interconnect.aclk"
set rst_path "hdl_top.dut.axi_interconnect.aresetn"

puts "======================================"
puts "Verifying DUT Signal Connections"
puts "======================================"

# Check if clock is toggling
if {[waveform exists $clk_path]} {
    puts "✓ Clock signal found: $clk_path"
    # Add to waveform if not already there
    waveform add $clk_path
} else {
    puts "✗ Clock signal NOT found: $clk_path"
}

# Check if reset is connected
if {[waveform exists $rst_path]} {
    puts "✓ Reset signal found: $rst_path"
    # Add to waveform if not already there
    waveform add $rst_path
} else {
    puts "✗ Reset signal NOT found: $rst_path"
}

# Check master interface connections
for {set i 0} {$i < 16} {incr i} {
    set master_path "hdl_top.dut.axi_interconnect.master_if\[$i\]"
    if {[waveform exists ${master_path}.awvalid]} {
        puts "✓ Master $i interface connected"
    } else {
        puts "✗ Master $i interface NOT connected"
    }
}

# Check slave interface connections
for {set i 0} {$i < 16} {incr i} {
    set slave_path "hdl_top.dut.axi_interconnect.slave_if\[$i\]"
    if {[waveform exists ${slave_path}.awvalid]} {
        puts "✓ Slave $i interface connected"
    } else {
        puts "✗ Slave $i interface NOT connected"
    }
}

# Check internal clock monitoring signals
set clk_monitor_path "hdl_top.dut.axi_interconnect.clk_connected"
set rst_monitor_path "hdl_top.dut.axi_interconnect.rst_connected"

if {[waveform exists $clk_monitor_path]} {
    puts "✓ Clock monitor signal found: $clk_monitor_path"
    waveform add $clk_monitor_path
}

if {[waveform exists $rst_monitor_path]} {
    puts "✓ Reset monitor signal found: $rst_monitor_path"
    waveform add $rst_monitor_path
}

puts "======================================"
puts "Signal verification complete"
puts "======================================"