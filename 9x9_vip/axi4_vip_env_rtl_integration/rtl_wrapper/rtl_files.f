# RTL files to include
# Generated RTL files for AXI4 interconnect (9 masters x 9 slaves)

# Wrapper module to translate signal names
${VIP_ROOT}/rtl_wrapper/axi4_interconnect_wrapper.sv

# Core RTL modules
${VIP_ROOT}/rtl_wrapper/generated_rtl/axi4_address_decoder.v
${VIP_ROOT}/rtl_wrapper/generated_rtl/axi4_arbiter.v
${VIP_ROOT}/rtl_wrapper/generated_rtl/axi4_router.v
${VIP_ROOT}/rtl_wrapper/generated_rtl/axi4_interconnect_m9s9.v