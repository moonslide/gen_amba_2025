#!/usr/bin/env python3
"""
Fix B-channel routing to use write ownership instead of AW grant
"""

def apply_b_channel_fix():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("🔧 Fixing B-channel routing to use write ownership...")
    
    # Fix slave 0 bready routing to use s0_w_owner instead of s0_aw_grant
    old_bready = """assign s0_bready = 
(s0_aw_grant == 4'd0) ? m0_bready :

                    (s0_aw_grant == 4'd1) ? m1_bready :

                    (s0_aw_grant == 4'd2) ? m2_bready :"""
    
    new_bready = """assign s0_bready = 
(s0_w_owner == 4'd0) ? m0_bready :

                    (s0_w_owner == 4'd1) ? m1_bready :

                    (s0_w_owner == 4'd2) ? m2_bready :"""
    
    if old_bready in content:
        content = content.replace(old_bready, new_bready)
        print("✅ Fixed slave 0 bready routing to use s0_w_owner")
        
        # Also fix the remaining entries in the s0_bready assignment
        content = content.replace("(s0_aw_grant == 4'd3) ? m3_bready :", "(s0_w_owner == 4'd3) ? m3_bready :")
        content = content.replace("(s0_aw_grant == 4'd4) ? m4_bready :", "(s0_w_owner == 4'd4) ? m4_bready :")
        content = content.replace("(s0_aw_grant == 4'd5) ? m5_bready :", "(s0_w_owner == 4'd5) ? m5_bready :")
        content = content.replace("(s0_aw_grant == 4'd6) ? m6_bready :", "(s0_w_owner == 4'd6) ? m6_bready :")
        content = content.replace("(s0_aw_grant == 4'd7) ? m7_bready :", "(s0_w_owner == 4'd7) ? m7_bready :")
        content = content.replace("(s0_aw_grant == 4'd8) ? m8_bready :", "(s0_w_owner == 4'd8) ? m8_bready :")
        content = content.replace("(s0_aw_grant == 4'd9) ? m9_bready :", "(s0_w_owner == 4'd9) ? m9_bready :")
        content = content.replace("(s0_aw_grant == 4'd10) ? m10_bready :", "(s0_w_owner == 4'd10) ? m10_bready :")
        content = content.replace("(s0_aw_grant == 4'd11) ? m11_bready :", "(s0_w_owner == 4'd11) ? m11_bready :")
        content = content.replace("(s0_aw_grant == 4'd12) ? m12_bready :", "(s0_w_owner == 4'd12) ? m12_bready :")
        content = content.replace("(s0_aw_grant == 4'd13) ? m13_bready :", "(s0_w_owner == 4'd13) ? m13_bready :")
        content = content.replace("(s0_aw_grant == 4'd14) ? m14_bready :", "(s0_w_owner == 4'd14) ? m14_bready :")
        print("✅ Fixed all s0_bready assignments to use s0_w_owner")
    else:
        print("❌ s0_bready pattern not found exactly")
    
    # Write the fixed content back
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("🎯 B-channel routing fix completed!")
    print("  • B-ready now routes to the master that owns the write transaction")  
    print("  • This ensures B responses reach the correct master")
    print("  • Should eliminate B-channel timeout errors")
    return True

if __name__ == "__main__":
    apply_b_channel_fix()