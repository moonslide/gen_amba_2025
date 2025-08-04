# TCL script to check signal connectivity in Verdi
# Run with: verdi -play check_signals.tcl -ssf signal_test.fsdb

# Open the database and waveform
if {[catch {debOpen -dbdir simv.daidir}]} {
    puts "Error: Could not open database"
}

# Add signals to check connectivity
wvCreateWindow
wvSetPosition -win $_nWave1 {("G1" 0)}

# Add master BFM driver signals
wvAddSignal -win $_nWave1 {hdl_top.gen_master_bfms[0].master_bfm.master_driver_bfm_h.axi_intf.awaddr[31:0]}
wvAddSignal -win $_nWave1 {hdl_top.gen_master_bfms[0].master_bfm.master_driver_bfm_h.axi_intf.awvalid}
wvAddSignal -win $_nWave1 {hdl_top.gen_master_bfms[0].master_bfm.master_driver_bfm_h.axi_intf.awready}
wvAddSignal -win $_nWave1 {hdl_top.gen_master_bfms[0].master_bfm.master_driver_bfm_h.bfm_enable}
wvAddSignal -win $_nWave1 {hdl_top.gen_master_bfms[0].master_bfm.master_driver_bfm_h.transaction_count}

# Add interface signals at hdl_top level
wvAddSignal -win $_nWave1 {hdl_top.axi_if[0].awaddr[31:0]}
wvAddSignal -win $_nWave1 {hdl_top.axi_if[0].awvalid}

# Add DUT signals
wvAddSignal -win $_nWave1 {hdl_top.dut.master_if[0].awaddr[31:0]}
wvAddSignal -win $_nWave1 {hdl_top.dut.master_if[0].awvalid}
wvAddSignal -win $_nWave1 {hdl_top.dut.axi_interconnect.M0_AWADDR[31:0]}
wvAddSignal -win $_nWave1 {hdl_top.dut.axi_interconnect.M0_AWVALID}

# Check read channel too
wvAddSignal -win $_nWave1 {hdl_top.gen_master_bfms[0].master_bfm.master_driver_bfm_h.axi_intf.araddr[31:0]}
wvAddSignal -win $_nWave1 {hdl_top.gen_master_bfms[0].master_bfm.master_driver_bfm_h.axi_intf.arvalid}
wvAddSignal -win $_nWave1 {hdl_top.dut.axi_interconnect.M0_ARADDR[31:0]}
wvAddSignal -win $_nWave1 {hdl_top.dut.axi_interconnect.M0_ARVALID}

# Zoom to see transactions
wvZoomAll -win $_nWave1

puts "Signals added. Check if awaddr and araddr are being driven by the BFM."
puts "The signal path is:"
puts "  BFM driver -> axi_intf -> hdl_top.axi_if[0] -> dut.master_if[0] -> axi_interconnect.M0_*"