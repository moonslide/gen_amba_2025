simSetSimulator "-vcssv" -exec \
           "/home/timtim01/eda_test/project/gen_amba_2025/9x9_vip/axi4_vip_env_rtl_integration/sim/simv" \
           -args \
           "+UVM_TESTNAME=axi4_stress_test +UVM_VERBOSITY=UVM_MEDIUM +ntb_random_seed=1 +fsdb_file=./waves/axi4_stress_test_1.fsdb"
debImport "-dbdir" \
          "/home/timtim01/eda_test/project/gen_amba_2025/9x9_vip/axi4_vip_env_rtl_integration/sim/simv.daidir"
debLoadSimResult \
           /home/timtim01/eda_test/project/gen_amba_2025/9x9_vip/axi4_vip_env_rtl_integration/sim/axi4_vip.fsdb
wvCreateWindow
verdiSetActWin -win $_nWave2
verdiWindowResize -win $_Verdi_1 "0" "27" "3440" "1305"
verdiWindowResize -win $_Verdi_1 "0" "27" "3440" "1305"
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcHBSelect "hdl_top.dut" -win $_nTrace1
srcSetScope "hdl_top.dut" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.dut" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "hdl_top.dut.axi_if" -win $_nTrace1
srcSetScope "hdl_top.dut.axi_if" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.dut.axi_if" -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "aclk" -line 90 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvAddSignal -win $_nWave2 "/hdl_top/dut/axi_if/aclk"
wvSetPosition -win $_nWave2 {("G1" 0)}
wvSetPosition -win $_nWave2 {("G1" 1)}
wvSetPosition -win $_nWave2 {("G1" 1)}
srcDeselectAll -win $_nTrace1
srcSelect -signal "awlen" -line 91 -pos 1 -win $_nTrace1
srcSetScope "hdl_top" -delim "." -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "hdl_top.axi_if\[0\]" -win $_nTrace1
srcSetScope "hdl_top.axi_if\[0\]" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.axi_if\[0\]" -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "awid" -line 21 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvSetPosition -win $_nWave2 {("G2" 0)}
wvAddSignal -win $_nWave2 "/hdl_top/axi_if\[0\]/awid\[3:0\]"
wvSetPosition -win $_nWave2 {("G2" 0)}
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetPosition -win $_nWave2 {("G2" 1)}
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
verdiSetActWin -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
srcDeselectAll -win $_nTrace1
srcSelect -signal "aresetn" -line 14 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "aclk" -line 13 -pos 1 -win $_nTrace1
wvSetPosition -win $_nWave2 {("G1" 0)}
wvSetPosition -win $_nWave2 {("G2" 1)}
wvAddSignal -win $_nWave2 "/hdl_top/axi_if\[0\]/aclk"
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetPosition -win $_nWave2 {("G2" 2)}
srcDeselectAll -win $_nTrace1
srcSelect -signal "aresetn" -line 14 -pos 1 -win $_nTrace1
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetPosition -win $_nWave2 {("G2" 2)}
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetPosition -win $_nWave2 {("G1" 1)}
wvSetPosition -win $_nWave2 {("G2" 0)}
wvSetPosition -win $_nWave2 {("G2" 1)}
wvAddSignal -win $_nWave2 "/hdl_top/axi_if\[0\]/aresetn"
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetPosition -win $_nWave2 {("G2" 2)}
srcDeselectAll -win $_nTrace1
srcSelect -win $_nTrace1 -range {21 55 11 1 5 1}
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetPosition -win $_nWave2 {("G3" 0)}
wvSetPosition -win $_nWave2 {("G2" 1)}
wvSetPosition -win $_nWave2 {("G3" 0)}
wvAddSignal -win $_nWave2 "hdl_top/axi_if\[0\]/ADDR_WIDTH"
wvAddSignal -win $_nWave2 "hdl_top/axi_if\[0\]/USER_WIDTH"
wvAddSignal -win $_nWave2 "hdl_top/axi_if\[0\]/DATA_WIDTH"
wvAddSignal -win $_nWave2 "axi4_globals_pkg/STRB_WIDTH"
wvAddSignal -win $_nWave2 "hdl_top/axi_if\[0\]/ID_WIDTH"
wvAddSignal -win $_nWave2 "/hdl_top/axi_if\[0\]/awid\[3:0\]" \
           "/hdl_top/axi_if\[0\]/awaddr\[31:0\]" \
           "/hdl_top/axi_if\[0\]/awlen\[7:0\]" \
           "/hdl_top/axi_if\[0\]/awsize\[2:0\]" \
           "/hdl_top/axi_if\[0\]/awburst\[1:0\]" "/hdl_top/axi_if\[0\]/awlock" \
           "/hdl_top/axi_if\[0\]/awcache\[3:0\]" \
           "/hdl_top/axi_if\[0\]/awprot\[2:0\]" \
           "/hdl_top/axi_if\[0\]/awqos\[3:0\]" \
           "/hdl_top/axi_if\[0\]/awregion\[3:0\]" \
           "/hdl_top/axi_if\[0\]/awuser\[-1:0\]" \
           "/hdl_top/axi_if\[0\]/awvalid" "/hdl_top/axi_if\[0\]/awready" \
           "/hdl_top/axi_if\[0\]/wdata\[63:0\]" \
           "/hdl_top/axi_if\[0\]/wstrb\[7:0\]" "/hdl_top/axi_if\[0\]/wlast" \
           "/hdl_top/axi_if\[0\]/wuser\[-1:0\]" "/hdl_top/axi_if\[0\]/wvalid" \
           "/hdl_top/axi_if\[0\]/wready" "/hdl_top/axi_if\[0\]/bid\[3:0\]" \
           "/hdl_top/axi_if\[0\]/bresp\[1:0\]" \
           "/hdl_top/axi_if\[0\]/buser\[-1:0\]" "/hdl_top/axi_if\[0\]/bvalid" \
           "/hdl_top/axi_if\[0\]/bready" "/hdl_top/axi_if\[0\]/arid\[3:0\]" \
           "/hdl_top/axi_if\[0\]/araddr\[31:0\]" \
           "/hdl_top/axi_if\[0\]/arlen\[7:0\]" \
           "/hdl_top/axi_if\[0\]/arsize\[2:0\]"
wvSetPosition -win $_nWave2 {("G3" 0)}
wvSetPosition -win $_nWave2 {("G3" 28)}
wvSetPosition -win $_nWave2 {("G3" 28)}
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 1
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollUp -win $_nWave2 1
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
srcDeselectAll -win $_nTrace1
debExit
