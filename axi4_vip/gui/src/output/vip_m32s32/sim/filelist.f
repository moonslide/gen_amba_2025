# AXI4 VIP File List
+incdir+../
+incdir+../intf
+incdir+../agent
+incdir+../agent/master_agent
+incdir+../agent/slave_agent
+incdir+../seq
+incdir+../test
+incdir+../env

# Package (MUST be compiled first)
../axi4_vip_pkg.sv

# Interface
../intf/axi4_if.sv

# Transaction
../agent/axi4_transaction.sv

# Master Agent
../agent/master_agent/axi4_master_driver.sv
../agent/master_agent/axi4_master_monitor.sv
../agent/master_agent/axi4_master_agent.sv

# Slave Agent
../agent/slave_agent/axi4_slave_driver.sv
../agent/slave_agent/axi4_slave_monitor.sv
../agent/slave_agent/axi4_slave_agent.sv

# Environment
../env/axi4_env.sv

# Test
../test/axi4_base_test.sv

# Top module
hdl_top.sv
