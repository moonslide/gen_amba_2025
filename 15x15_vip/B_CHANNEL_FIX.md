
# B-CHANNEL FIX FOR MASTER ID TRACKING
# 
# Issue: Some VIP testbenches may not properly handle transaction IDs
# Solution: Track AWID through the entire write transaction
#
# Implementation:
# 1. Add transaction_id register for each slave
# 2. Capture AWID on AW handshake
# 3. Use captured ID for BID generation
# 4. Hold AWID stable during transaction
# 5. Clear on transaction completion
#
# This ensures proper B-channel response routing even when
# the slave BFM doesn't correctly echo the transaction ID.
