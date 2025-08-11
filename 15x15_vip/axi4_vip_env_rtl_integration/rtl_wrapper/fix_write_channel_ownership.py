#!/usr/bin/env python3
"""
Fix write channel ownership - ensure W channel stays locked to granted master
"""

def apply_write_ownership_fix():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("🔧 Applying write channel ownership fix...")
    
    # Find where s0_aw_grant is declared and add write ownership registers
    reg_pattern = "reg [3:0] s0_aw_grant;"
    if reg_pattern in content:
        new_regs = """reg [3:0] s0_aw_grant;
    // ADDED: Write channel ownership tracking
    reg [3:0] s0_w_owner;    // Which master owns the write channel
    reg       s0_w_active;   // Write channel is active/busy"""
        
        content = content.replace(reg_pattern, new_regs)
        print("✅ Added write ownership registers")
    
    # Find the write ownership update logic and replace it
    # Look for the always block that handles s0_aw_grant
    always_pattern = """        // Update grants based on requests and current state
        if (s0_aw_requests != 0) begin
            // FIXED: Reverse priority to ensure Masters 1&2 can complete
            if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;

            else if (s0_aw_requests[1]) s0_aw_grant <= 4'd1;

            else if (s0_aw_requests[0]) s0_aw_grant <= 4'd0;"""
    
    if always_pattern in content:
        new_always = """        // Update grants based on requests and current state
        if (s0_aw_requests != 0 && !s0_w_active) begin  // Only grant AW if W channel is free
            // FIXED: Reverse priority to ensure Masters 1&2 can complete
            if (s0_aw_requests[2]) begin
                s0_aw_grant <= 4'd2;
                s0_w_owner <= 4'd2;   // Lock W channel to master 2
                s0_w_active <= 1'b1;  // Mark W channel as busy
            end
            else if (s0_aw_requests[1]) begin
                s0_aw_grant <= 4'd1;
                s0_w_owner <= 4'd1;   // Lock W channel to master 1  
                s0_w_active <= 1'b1;  // Mark W channel as busy
            end
            else if (s0_aw_requests[0]) begin
                s0_aw_grant <= 4'd0;
                s0_w_owner <= 4'd0;   // Lock W channel to master 0
                s0_w_active <= 1'b1;  // Mark W channel as busy
            end"""
        
        content = content.replace(always_pattern, new_always)
        print("✅ Updated AW grant logic with W channel locking")
    
    # Add logic to release write ownership when WLAST is seen
    # Find the end of the always block and add release logic
    end_pattern = """            else s0_aw_grant <= s0_aw_grant;  // Maintain current grant
        end"""
    
    if end_pattern in content:
        new_end = """            else s0_aw_grant <= s0_aw_grant;  // Maintain current grant
        end
        
        // ADDED: Release write channel when WLAST completes
        if (s0_w_active && s0_wvalid && s0_wready && s0_wlast) begin
            s0_w_active <= 1'b0;  // Release write channel
            s0_w_owner <= 4'd0;   // Clear owner
        end"""
        
        content = content.replace(end_pattern, new_end)
        print("✅ Added write channel release logic")
    
    # Now fix the W channel assignments to use s0_w_owner instead of s0_aw_grant
    wdata_old = """assign s0_wdata = 
(s0_aw_grant == 4'd0) ? m0_wdata :"""
    wdata_new = """assign s0_wdata = 
(s0_w_owner == 4'd0) ? m0_wdata :"""
    
    if wdata_old in content:
        content = content.replace(wdata_old, wdata_new)
        # Also fix the rest of the wdata assignment
        content = content.replace("(s0_aw_grant == 4'd1) ? m1_wdata :", "(s0_w_owner == 4'd1) ? m1_wdata :")
        content = content.replace("(s0_aw_grant == 4'd2) ? m2_wdata :", "(s0_w_owner == 4'd2) ? m2_wdata :")
        print("✅ Fixed s0_wdata assignment to use s0_w_owner")
    
    wstrb_old = """assign s0_wstrb = 
(s0_aw_grant == 4'd0) ? m0_wstrb :"""
    wstrb_new = """assign s0_wstrb = 
(s0_w_owner == 4'd0) ? m0_wstrb :"""
    
    if wstrb_old in content:
        content = content.replace(wstrb_old, wstrb_new)
        # Also fix the rest of the wstrb assignment
        content = content.replace("(s0_aw_grant == 4'd1) ? m1_wstrb :", "(s0_w_owner == 4'd1) ? m1_wstrb :")
        content = content.replace("(s0_aw_grant == 4'd2) ? m2_wstrb :", "(s0_w_owner == 4'd2) ? m2_wstrb :")
        print("✅ Fixed s0_wstrb assignment to use s0_w_owner")
    
    wlast_old = """assign s0_wlast = 
(s0_aw_grant == 4'd0) ? m0_wlast :"""
    wlast_new = """assign s0_wlast = 
(s0_w_owner == 4'd0) ? m0_wlast :"""
    
    if wlast_old in content:
        content = content.replace(wlast_old, wlast_new)
        # Also fix the rest of the wlast assignment
        content = content.replace("(s0_aw_grant == 4'd1) ? m1_wlast :", "(s0_w_owner == 4'd1) ? m1_wlast :")
        content = content.replace("(s0_aw_grant == 4'd2) ? m2_wlast :", "(s0_w_owner == 4'd2) ? m2_wlast :")
        print("✅ Fixed s0_wlast assignment to use s0_w_owner")
    
    wvalid_old = """assign s0_wvalid = 
(s0_aw_grant == 4'd0) ? m0_wvalid :"""
    wvalid_new = """assign s0_wvalid = 
(s0_w_owner == 4'd0) ? m0_wvalid :"""
    
    if wvalid_old in content:
        content = content.replace(wvalid_old, wvalid_new)
        # Also fix the rest of the wvalid assignment
        content = content.replace("(s0_aw_grant == 4'd1) ? m1_wvalid :", "(s0_w_owner == 4'd1) ? m1_wvalid :")
        content = content.replace("(s0_aw_grant == 4'd2) ? m2_wvalid :", "(s0_w_owner == 4'd2) ? m2_wvalid :")
        print("✅ Fixed s0_wvalid assignment to use s0_w_owner")
    
    # Also need to fix wready routing back to masters
    wready_pattern = "assign m0_wready = (s0_aw_grant == 4'd0) ? s0_wready : 1'b0;"
    if wready_pattern in content:
        content = content.replace("(s0_aw_grant == 4'd0) ? s0_wready : 1'b0", "(s0_w_owner == 4'd0) ? s0_wready : 1'b0")
        content = content.replace("(s0_aw_grant == 4'd1) ? s0_wready : 1'b0", "(s0_w_owner == 4'd1) ? s0_wready : 1'b0")
        content = content.replace("(s0_aw_grant == 4'd2) ? s0_wready : 1'b0", "(s0_w_owner == 4'd2) ? s0_wready : 1'b0")
        print("✅ Fixed wready routing to use s0_w_owner")
    
    # Write the fixed content back
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("🎯 Write channel ownership fix completed!")
    print("  • AW grants now lock the W channel to the winning master")
    print("  • W channel stays locked until WLAST completes")
    print("  • This prevents write data mixing between masters")
    return True

if __name__ == "__main__":
    apply_write_ownership_fix()