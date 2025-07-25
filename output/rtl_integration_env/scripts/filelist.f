// Filelist for RTL Integration Mode with tim_axi4_vip

// Include directories
+incdir+./tim_axi4_vip/include
+incdir+./tim_axi4_vip/intf
+incdir+./tim_axi4_vip/master
+incdir+./tim_axi4_vip/slave
+incdir+./tim_axi4_vip/seq/master_sequences
+incdir+./tim_axi4_vip/seq/slave_sequences

// Package files (order matters)
./tim_axi4_vip/pkg/axi4_globals_pkg.sv
./tim_axi4_vip/master/axi4_master_pkg.sv
./tim_axi4_vip/slave/axi4_slave_pkg.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_seq_pkg.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_seq_pkg.sv
./tim_axi4_vip/test/axi4_test_pkg.sv

// Interface
./tim_axi4_vip/intf/axi4_interface/axi4_if.sv

// BFM modules (Bus Functional Models)
./tim_axi4_vip/agent/master_agent_bfm/axi4_master_driver_bfm.sv
./tim_axi4_vip/agent/master_agent_bfm/axi4_master_monitor_bfm.sv
./tim_axi4_vip/agent/master_agent_bfm/axi4_master_agent_bfm.sv
./tim_axi4_vip/agent/slave_agent_bfm/axi4_slave_driver_bfm.sv
./tim_axi4_vip/agent/slave_agent_bfm/axi4_slave_monitor_bfm.sv
./tim_axi4_vip/agent/slave_agent_bfm/axi4_slave_agent_bfm.sv

// Assertions
./tim_axi4_vip/assertions/master_assertions.sv
./tim_axi4_vip/assertions/slave_assertions.sv

// Master components
./tim_axi4_vip/master/axi4_master_agent_config.sv
./tim_axi4_vip/master/axi4_master_tx.sv
./tim_axi4_vip/master/axi4_master_seq_item_converter.sv
./tim_axi4_vip/master/axi4_master_cfg_converter.sv
./tim_axi4_vip/master/axi4_master_write_sequencer.sv
./tim_axi4_vip/master/axi4_master_read_sequencer.sv
./tim_axi4_vip/master/axi4_master_monitor_proxy.sv
./tim_axi4_vip/master/axi4_master_driver_proxy.sv
./tim_axi4_vip/master/axi4_master_coverage.sv
./tim_axi4_vip/master/axi4_master_agent.sv

// Slave components
./tim_axi4_vip/slave/axi4_slave_agent_config.sv
./tim_axi4_vip/slave/axi4_slave_tx.sv
./tim_axi4_vip/slave/axi4_slave_seq_item_converter.sv
./tim_axi4_vip/slave/axi4_slave_cfg_converter.sv
./tim_axi4_vip/slave/axi4_slave_write_sequencer.sv
./tim_axi4_vip/slave/axi4_slave_read_sequencer.sv
./tim_axi4_vip/slave/axi4_slave_monitor_proxy.sv
./tim_axi4_vip/slave/axi4_slave_driver_proxy.sv
./tim_axi4_vip/slave/axi4_slave_memory.sv
./tim_axi4_vip/slave/axi4_slave_coverage.sv
./tim_axi4_vip/slave/axi4_slave_agent.sv

// Base sequences
./tim_axi4_vip/seq/master_sequences/axi4_master_base_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_bk_base_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_nbk_base_seq.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_base_seq.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_bk_base_seq.sv
./tim_axi4_vip/seq/slave_sequences/axi4_slave_nbk_base_seq.sv

// Basic sequences for testing
./tim_axi4_vip/seq/master_sequences/axi4_master_write_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_read_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_bk_write_seq.sv
./tim_axi4_vip/seq/master_sequences/axi4_master_bk_read_seq.sv

// Virtual sequences and sequencer
./tim_axi4_vip/virtual_seqr/axi4_virtual_sequencer.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_seq_pkg.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_base_seq.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_write_seq.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_read_seq.sv
./tim_axi4_vip/virtual_seq/axi4_virtual_write_read_seq.sv

// Environment package and components
./tim_axi4_vip/env/axi4_env_pkg.sv
./tim_axi4_vip/env/axi4_env_config.sv
./tim_axi4_vip/env/axi4_scoreboard.sv
./tim_axi4_vip/env/axi4_protocol_coverage.sv
./tim_axi4_vip/env/axi4_env.sv

// Test base class
./tim_axi4_vip/test/axi4_base_test.sv

// RTL wrapper
./rtl_wrapper/dut_wrapper.sv

// Add your RTL files here
// ./rtl_wrapper/your_dut.sv

// HDL top and HVL top
./tim_axi4_vip/top/hdl_top.sv
./tim_axi4_vip/top/hvl_top.sv

// Testbench top
./tb/top_tb.sv

// Test files
./tb/tests/axi4_rtl_basic_test.sv
