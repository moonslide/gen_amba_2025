debImport "-elab" "./simv.daidir/kdb"
debLoadSimResult \
           /home/timtim01/eda_test/project/gen_amba_2025/vip_test/axi4_vip_env_rtl_integration/sim/waves/axi4_performance_test_1.fsdb
wvCreateWindow
verdiSetActWin -win $_nWave2
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "aclk" -line 13 -pos 1 -win $_nTrace1
srcHBSelect "hdl_top.dut" -win $_nTrace1
srcSetScope "hdl_top.dut" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.dut" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcSelect -win $_nTrace1 -range {8 8 1 7 1 1}
srcTBAddBrkPnt -win $_nTrace1 -line 8 -file \
           /home/timtim01/eda_test/project/gen_amba_2025/vip_test/axi4_vip_env_rtl_integration/rtl_wrapper/dut_wrapper.sv
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcSelect -win $_nTrace1 -range {8 12 1 1 1 1}
verdiWindowResize -win $_Verdi_1 "916" "202" "1920" "716"
srcDeselectAll -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -word -line 15 -pos 5 -win $_nTrace1
srcAction -pos 15 5 4 -win $_nTrace1 -name "axi_if" -ctrlKey off
srcSetScope "hdl_top" -delim "." -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "hdl_top.axi_if\[0\]" -win $_nTrace1
srcSetScope "hdl_top.axi_if\[0\]" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.axi_if\[0\]" -win $_nTrace1
srcHBSelect "hdl_top.axi_if\[1\]" -win $_nTrace1
srcSetScope "hdl_top.axi_if\[1\]" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.axi_if\[1\]" -win $_nTrace1
srcHBSelect "hdl_top.axi_if\[0\].master" -win $_nTrace1
srcSetScope "hdl_top.axi_if\[0\].master" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.axi_if\[0\].master" -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "aclk" -line 76 -pos 1 -win $_nTrace1
srcAction -pos 75 3 1 -win $_nTrace1 -name "aclk" -ctrlKey off
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "aclk" -line 76 -pos 1 -win $_nTrace1
srcAction -pos 75 3 1 -win $_nTrace1 -name "aclk" -ctrlKey off
srcDeselectAll -win $_nTrace1
srcSelect -signal "aclk" -line 76 -pos 1 -win $_nTrace1
srcAction -pos 75 3 1 -win $_nTrace1 -name "aclk" -ctrlKey off
srcDeselectAll -win $_nTrace1
srcSelect -signal "aclk" -line 76 -pos 1 -win $_nTrace1
srcHBSelect "hdl_top.dut" -win $_nTrace1
srcSetScope "hdl_top.dut" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.dut" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
srcSelect -signal "clk" -line 14 -pos 1 -win $_nTrace1
srcAction -pos 13 5 2 -win $_nTrace1 -name "clk" -ctrlKey off
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "aclk" -line 19 -pos 1 -win $_nTrace1
wvZoom -win $_nWave2 0.000000 568114.446405
verdiSetActWin -win $_nWave2
wvSetCursor -win $_nWave2 0.000000
wvSetCursor -win $_nWave2 51172.672453
srcDeselectAll -win $_nTrace1
srcSelect -signal "aclk" -line 19 -pos 1 -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
wvZoomOut -win $_nWave2
verdiSetActWin -win $_nWave2
wvSetCursor -win $_nWave2 1006504.538439
srcDeselectAll -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcHBSelect "hdl_top.dut" -win $_nTrace1
srcSetScope "hdl_top.dut" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.dut" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBSelect "hdl_top.dut.generated_interconnect" -win $_nTrace1
srcSetScope "hdl_top.dut.generated_interconnect" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect" -win $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect" -win $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_aix_wid_m0" -win $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_aix_wid_m0" -win $_nTrace1
srcSetScope "hdl_top.dut.generated_interconnect.u_aix_wid_m0" -delim "." -win \
           $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_aix_wid_m0" -win $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_aix_wid_m1" -win $_nTrace1
srcSetScope "hdl_top.dut.generated_interconnect.u_aix_wid_m1" -delim "." -win \
           $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_aix_wid_m1" -win $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_aix_wid_m0.u_axi_wid_fifo_sync" \
           -win $_nTrace1
srcSetScope "hdl_top.dut.generated_interconnect.u_aix_wid_m0.u_axi_wid_fifo_sync" \
           -delim "." -win $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_aix_wid_m0.u_axi_wid_fifo_sync" \
           -win $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_aix_wid_m0.u_axi_wid_fifo_sync" \
           -win $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_axi_mtos_s2" -win $_nTrace1
srcSetScope "hdl_top.dut.generated_interconnect.u_axi_mtos_s2" -delim "." -win \
           $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_axi_mtos_s2" -win $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_axi_stom_m0" -win $_nTrace1
srcSetScope "hdl_top.dut.generated_interconnect.u_axi_stom_m0" -delim "." -win \
           $_nTrace1
srcHBSelect "hdl_top.dut.generated_interconnect.u_axi_stom_m0" -win $_nTrace1
srcSetScope "hdl_top.dut.generated_interconnect.u_axi_stom_m1" -delim "." -win \
           $_nTrace1
srcHBSelect \
           "hdl_top.dut.generated_interconnect.u_axi_stom_m1.u_axi_arbiter_stom_s3" \
           -win $_nTrace1
srcSetScope \
           "hdl_top.dut.generated_interconnect.u_axi_stom_m1.u_axi_arbiter_stom_s3" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "hdl_top.dut.generated_interconnect.u_axi_stom_m1.u_axi_arbiter_stom_s3" \
           -win $_nTrace1
srcDeselectAll -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcHBSelect \
           "hdl_top.dut.generated_interconnect.u_axi_stom_m1.u_axi_arbiter_stom_s3.priority_sel" \
           -win $_nTrace1
srcSetScope \
           "hdl_top.dut.generated_interconnect.u_axi_stom_m1.u_axi_arbiter_stom_s3.priority_sel" \
           -delim "." -win $_nTrace1
srcHBSelect \
           "hdl_top.dut.generated_interconnect.u_axi_stom_m1.u_axi_arbiter_stom_s3.priority_sel" \
           -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcDeselectAll -win $_nTrace1
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcAction -pos 2087 2 5 -win $_nTrace1 -name "axi_mtos_m2" -ctrlKey off
srcHBSelect "hdl_top.dut.axi_if" -win $_nTrace1
srcSetScope "hdl_top.dut.axi_if" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.dut.axi_if" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcSetScope "hdl_top" -delim "." -win $_nTrace1
srcSetScope "hdl_top" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.axi_if\[0\]" -win $_nTrace1
srcSetScope "hdl_top.axi_if\[0\]" -delim "." -win $_nTrace1
srcHBSelect "hdl_top.axi_if\[0\]" -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -word -line 6 -pos 2 -win $_nTrace1
srcAction -pos 6 2 2 -win $_nTrace1 -name "axi4_if" -ctrlKey off
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcSelect -signal "aresetn" -line 26 -pos 1 -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -signal "aclk" -line 25 -pos 1 -win $_nTrace1
wvAddSignal -win $_nWave2 "hdl_top/aclk"
srcDeselectAll -win $_nTrace1
srcDeselectAll -win $_nTrace1
srcSelect -win $_nTrace1 -signal "NO_OF_SLAVES" -line 36 -pos 1
srcAction -pos 35 5 3 -win $_nTrace1 -name "NO_OF_SLAVES" -ctrlKey off
srcDeselectAll -win $_nTrace1
srcSelect -win $_nTrace1 -signal "NO_OF_SLAVES" -line 36 -pos 1
srcAction -pos 35 5 3 -win $_nTrace1 -name "NO_OF_SLAVES" -ctrlKey off
srcDeselectAll -win $_nTrace1
srcSelect -win $_nTrace1 -signal "NO_OF_MASTERS" -line 33 -pos 1
srcAction -pos 32 5 5 -win $_nTrace1 -name "NO_OF_MASTERS" -ctrlKey off
srcDeselectAll -win $_nTrace1
srcSelect -win $_nTrace1 -signal "NO_OF_MASTERS" -line 30 -pos 1
srcAction -pos 29 5 4 -win $_nTrace1 -name "NO_OF_MASTERS" -ctrlKey off
srcDeselectAll -win $_nTrace1
srcSelect -win $_nTrace1 -signal "NO_OF_MASTERS" -line 30 -pos 1
srcAction -pos 29 5 4 -win $_nTrace1 -name "NO_OF_MASTERS" -ctrlKey off
srcDeselectAll -win $_nTrace1
srcSelect -win $_nTrace1 -signal "NO_OF_MASTERS" -line 30 -pos 1
srcAction -pos 29 5 4 -win $_nTrace1 -name "NO_OF_MASTERS" -ctrlKey off
srcDeselectAll -win $_nTrace1
srcSelect -win $_nTrace1 -signal "NO_OF_MASTERS" -line 30 -pos 1
debExit
