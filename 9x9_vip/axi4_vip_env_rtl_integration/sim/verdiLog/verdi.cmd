debImport "-elab" "./simv.daidir/kdb"
debLoadSimResult \
           /home/timtim01/eda_test/project/gen_amba_2025/9x9_vip/axi4_vip_env_rtl_integration/sim/waves/axi4_stress_test_1.fsdb
wvCreateWindow
verdiSetActWin -win $_nWave2
verdiWindowResize -win $_Verdi_1 "825" "272" "2520" "962"
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcHBSelect "hdl_top" -win $_nTrace1
srcSetScope "hdl_top" -delim "." -win $_nTrace1
srcHBSelect "hdl_top" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "hdl_top.dut" -win $_nTrace1
srcSetScope "hdl_top.dut" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.dut" -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -word -line 32 -pos 2 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -inst "axi_interconnect" -line 28 -pos 1 -win $_nTrace1
srcAction -pos 27 3 2 -win $_nTrace1 -name "axi_interconnect" -ctrlKey off
srcDeselectAll -win $_nTrace1
srcSelect -signal "M0_AWID" -line 52 -pos 1 -win $_nTrace1
srcSelect -signal "M0_AWADDR" -line 53 -pos 1 -win $_nTrace1
srcSelect -signal "M0_AWLEN" -line 54 -pos 1 -win $_nTrace1
srcSelect -signal "M0_AWLOCK" -line 55 -pos 1 -win $_nTrace1
srcSelect -signal "M0_AWSIZE" -line 56 -pos 1 -win $_nTrace1
srcSelect -signal "M0_AWBURST" -line 57 -pos 1 -win $_nTrace1
wvAddSignal -win $_nWave2 "/hdl_top/dut/axi_interconnect/M0_AWID\[3:0\]" \
           "/hdl_top/dut/axi_interconnect/M0_AWADDR\[31:0\]" \
           "/hdl_top/dut/axi_interconnect/M0_AWLEN\[7:0\]" \
           "/hdl_top/dut/axi_interconnect/M0_AWLOCK" \
           "/hdl_top/dut/axi_interconnect/M0_AWSIZE\[2:0\]" \
           "/hdl_top/dut/axi_interconnect/M0_AWBURST\[1:0\]"
wvSetPosition -win $_nWave2 {("G1" 0)}
wvSetPosition -win $_nWave2 {("G1" 6)}
wvSetPosition -win $_nWave2 {("G1" 6)}
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
verdiSetActWin -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoom -win $_nWave2 915644.002211 1328800.442233
wvZoom -win $_nWave2 1012024.332609 1038745.893406
wvZoom -win $_nWave2 1024314.182571 1027578.673968
wvZoom -win $_nWave2 1024915.108848 1025200.233027
wvZoom -win $_nWave2 1024991.394144 1025028.906336
wvZoom -win $_nWave2 1024998.195691 1025002.529604
wvZoom -win $_nWave2 1024999.283362 1025000.569880
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
wvScrollDown -win $_nWave2 0
srcDeselectAll -win $_nTrace1
srcSelect -signal "M0_AWPROT" -line 62 -pos 1 -win $_nTrace1
srcDeselectAll -win $_nTrace1
wvZoom -win $_nWave2 1024999.990981 1025000.036497
verdiSetActWin -win $_nWave2
wvZoom -win $_nWave2 1024999.990981 1025000.032440
wvZoom -win $_nWave2 1024999.995403 1025000.010881
wvScrollDown -win $_nWave2 0
wvZoom -win $_nWave2 1024999.997614 1025000.011987
wvZoom -win $_nWave2 1024999.997614 1025000.006459
wvZoom -win $_nWave2 1024999.997614 1025000.011987
wvZoom -win $_nWave2 1024999.997614 1025000.019173
wvZoom -win $_nWave2 1024999.997614 1025000.023042
wvZoom -win $_nWave2 1024999.997614 1025000.002589
wvZoom -win $_nWave2 1024999.997614 1025000.026912
wvSetCursor -win $_nWave2 1025000.002036 -snap {("G1" 1)}
