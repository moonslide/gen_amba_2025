AXI4 System Architecture - Recommended Modifications

The following modifications are recommended:

Inconsistent Naming: GPU / Video_Enc
Issue: The block on the left is named GPU, but its interface connecting to the AXI Interconnect is named Video_Enc.
Suggestion: Please unify the naming. We recommend one of the following changes: Rename GPU to Video_Enc OR Rename Video_Enc to GPU.
And if there are too many masters or slaves the block will cover other block 
All Master/Slave Ports are Labeled "P:0"
Issue: All connections are labeled as P:0, which makes it impossible to distinguish the specific path from a Master to a Slave.
Suggestion: Assign a unique ID to each interface. For example: Master Ports: CPU -> M0, GPU -> M1, Video_Decoder -> M2, DMA -> M3. Slave Ports: DDR4_0 -> S0, DDR4_1 -> S1, L3 Cache -> S2, and so on.
Note: The slave interfaces need to be configured to specify which masters have access rights. By default, all masters are granted access. Permissions can also be set to Read-Only or Write-Only.

Memory Map Addresses Require Alignment and Overlap Checks
Suggestion:

Verify that the starting address and size of all memory blocks are Power-of-2 aligned.

Ensure that there are no overlapping address ranges between blocks.

The current architecture shows no obvious flaws, but for future expansions (e.g., adding a PCIe_Config_Space), you must be careful to avoid address conflicts with existing regions.

Recommendation to Add a Memory Map Table and a Master/Slave Table
Objective: To help the team more easily understand the overall architecture and its corresponding address mapping.
Suggestion: Please add outputs for the following two tables:

(a) Example Memory Map Table maybe csv file:
Module, Base Address, Size, Description
DDR4_Channel_0, 0x00_0000_0000, 8GB, Main Memory
DDR4_Channel_1, 0x20_0000_0000, 8GB, Memory Bank 1
L3_Cache_SRAM, 0x40_0000_0000, 16MB, Shared Cache
Boot_ROM, 0x10_0000_0000, 256KB, Boot Loader
System_Registers, 0x20_0000_0000, 64KB, System Control
PCIe_Config_Space, 0x40_0000_0000, 64MB, PCIe Configuration
Crypto_Engine, 0x80_0000_0000, 256KB, Security Engine
Debug_APB_Bridge, 0x10_0000_0000, 1MB, Debug Access

(b) Example Master/Slave Table:
Name, Type, Port, Notes
CPU_Cluster_0, Master, M0,
GPU, Master, M1, aka Video_Enc
Video_Decoder, Master, M2,
