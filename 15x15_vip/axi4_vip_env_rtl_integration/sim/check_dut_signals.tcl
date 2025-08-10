# TCL script to check DUT signal activity in FSDB
# Usage: verdi -ssf waves/axi4_vip.fsdb -ssx -ssv -f check_dut_signals.tcl

# Check master interface signals from DUT
puts "Checking DUT master interface signals..."
wvGetSignalValueByTime -win $_nWave1 "/hdl_top/dut/master_if[0]/awvalid" 0
wvGetSignalValueByTime -win $_nWave1 "/hdl_top/dut/master_if[0]/awaddr" 0
wvGetSignalValueByTime -win $_nWave1 "/hdl_top/dut/master_if[0]/arvalid" 0

# Check RTL internal signals
puts "Checking RTL interconnect internal signals..."
wvGetSignalValueByTime -win $_nWave1 "/hdl_top/dut/rtl_interconnect_inst/m0_awvalid" 0
wvGetSignalValueByTime -win $_nWave1 "/hdl_top/dut/rtl_interconnect_inst/m0_arvalid" 0

# Check slave interface signals from DUT
puts "Checking DUT slave interface signals..."
wvGetSignalValueByTime -win $_nWave1 "/hdl_top/dut/slave_if[0]/awvalid" 0
wvGetSignalValueByTime -win $_nWave1 "/hdl_top/dut/slave_if[0]/arvalid" 0

exit