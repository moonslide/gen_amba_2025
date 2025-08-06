# Sim Components - Large Matrix Optimization

This directory contains placeholder files for a large bus matrix configuration.

## Performance Optimization Applied
For matrices larger than 10x10, full VIP generation is optimized to prevent
hanging and excessive generation times.

## To Generate Full VIP
If you need complete VIP files for this large matrix, consider:
1. Using a hierarchical approach (break into smaller matrices)
2. Generating RTL only without full UVM testbench
3. Using the manual generation mode

## Configuration
- Masters: 16
- Slaves: 16
- Matrix Size: 16x16

Generated on: 2025-08-06 14:23:00
