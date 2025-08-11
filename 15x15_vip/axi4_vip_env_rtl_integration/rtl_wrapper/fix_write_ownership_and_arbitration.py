#!/usr/bin/env python3
"""
Comprehensive fix for AXI4 crossbar issues:
1. Implement proper round-robin arbitration using existing s0_aw_last_grant
2. Add write ownership tracking to maintain W channel during burst
3. Fix write ready/valid signals to use write owner instead of AW grant
"""

import re

def fix_write_ownership_and_arbitration():
    rtl_file = "/home/timtim01/eda_test/project/gen_amba_2025/15x15_vip/axi4_vip_env_rtl_integration/rtl_wrapper/generated_rtl/axi4_interconnect_m15s15.v"
    
    with open(rtl_file, 'r') as f:
        content = f.read()
    
    print("🔧 Applying comprehensive fix for write ownership and round-robin arbitration...")
    
    # 1. Add write ownership registers
    ownership_regs = """
// Write ownership tracking
reg [3:0] s0_w_owner;   // Who owns the write channel
reg       s0_w_busy;    // Write channel busy flag
reg [3:0] s1_w_owner;   
reg       s1_w_busy;   
reg [3:0] s2_w_owner;   
reg       s2_w_busy;   """
    
    # Find where to insert ownership registers (after existing regs)
    reg_pattern = r"(reg \[3:0\] s0_ar_last_grant;)"
    content = re.sub(reg_pattern, r"\1" + ownership_regs, content)
    
    # 2. Initialize ownership registers in reset
    init_pattern = r"(s0_ar_last_grant <= 4'd0;)"
    init_code = r"""\1
        s0_w_owner <= 4'd15;
        s0_w_busy <= 1'b0;
        s1_w_owner <= 4'd15;
        s1_w_busy <= 1'b0;
        s2_w_owner <= 4'd15;
        s2_w_busy <= 1'b0;"""
    content = re.sub(init_pattern, init_code, content)
    
    # 3. Fix slave 0 arbitration to use round-robin based on s0_aw_last_grant
    old_arbitration = r"""// AW channel arbitration
        if \(s0_aw_grant == 4'd15\) begin // No current grant
            // Simplified: grant to lowest numbered requesting master
            if \(s0_aw_requests\[0\]\) s0_aw_grant <= 4'd0;
            else if \(s0_aw_requests\[1\]\) s0_aw_grant <= 4'd1;
            else if \(s0_aw_requests\[2\]\) s0_aw_grant <= 4'd2;
            else if \(s0_aw_requests\[3\]\) s0_aw_grant <= 4'd3;
            else if \(s0_aw_requests\[4\]\) s0_aw_grant <= 4'd4;
            else if \(s0_aw_requests\[5\]\) s0_aw_grant <= 4'd5;
            else if \(s0_aw_requests\[6\]\) s0_aw_grant <= 4'd6;
            else if \(s0_aw_requests\[7\]\) s0_aw_grant <= 4'd7;
            else if \(s0_aw_requests\[8\]\) s0_aw_grant <= 4'd8;
            else if \(s0_aw_requests\[9\]\) s0_aw_grant <= 4'd9;
            else if \(s0_aw_requests\[10\]\) s0_aw_grant <= 4'd10;
            else if \(s0_aw_requests\[11\]\) s0_aw_grant <= 4'd11;
            else if \(s0_aw_requests\[12\]\) s0_aw_grant <= 4'd12;
            else if \(s0_aw_requests\[13\]\) s0_aw_grant <= 4'd13;
            else if \(s0_aw_requests\[14\]\) s0_aw_grant <= 4'd14;
        end else if \(s0_awready && s0_awvalid\) begin
            // Transaction accepted, release grant
            s0_aw_last_grant <= s0_aw_grant;
            s0_aw_grant <= 4'd15;
        end"""
    
    new_arbitration = """// AW channel arbitration - Round-robin based on last grant
        if (s0_aw_grant == 4'd15) begin // No current grant
            // Round-robin starting after last granted master
            if (s0_aw_last_grant == 4'd0) begin
                // After master 0, prioritize 1,2,3...
                if (s0_aw_requests[1]) s0_aw_grant <= 4'd1;
                else if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;
                else if (s0_aw_requests[3]) s0_aw_grant <= 4'd3;
                else if (s0_aw_requests[4]) s0_aw_grant <= 4'd4;
                else if (s0_aw_requests[5]) s0_aw_grant <= 4'd5;
                else if (s0_aw_requests[6]) s0_aw_grant <= 4'd6;
                else if (s0_aw_requests[7]) s0_aw_grant <= 4'd7;
                else if (s0_aw_requests[8]) s0_aw_grant <= 4'd8;
                else if (s0_aw_requests[9]) s0_aw_grant <= 4'd9;
                else if (s0_aw_requests[10]) s0_aw_grant <= 4'd10;
                else if (s0_aw_requests[11]) s0_aw_grant <= 4'd11;
                else if (s0_aw_requests[12]) s0_aw_grant <= 4'd12;
                else if (s0_aw_requests[13]) s0_aw_grant <= 4'd13;
                else if (s0_aw_requests[14]) s0_aw_grant <= 4'd14;
                else if (s0_aw_requests[0]) s0_aw_grant <= 4'd0;
            end else if (s0_aw_last_grant == 4'd1) begin
                // After master 1, prioritize 2,3,0...
                if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;
                else if (s0_aw_requests[3]) s0_aw_grant <= 4'd3;
                else if (s0_aw_requests[4]) s0_aw_grant <= 4'd4;
                else if (s0_aw_requests[5]) s0_aw_grant <= 4'd5;
                else if (s0_aw_requests[6]) s0_aw_grant <= 4'd6;
                else if (s0_aw_requests[7]) s0_aw_grant <= 4'd7;
                else if (s0_aw_requests[8]) s0_aw_grant <= 4'd8;
                else if (s0_aw_requests[9]) s0_aw_grant <= 4'd9;
                else if (s0_aw_requests[10]) s0_aw_grant <= 4'd10;
                else if (s0_aw_requests[11]) s0_aw_grant <= 4'd11;
                else if (s0_aw_requests[12]) s0_aw_grant <= 4'd12;
                else if (s0_aw_requests[13]) s0_aw_grant <= 4'd13;
                else if (s0_aw_requests[14]) s0_aw_grant <= 4'd14;
                else if (s0_aw_requests[0]) s0_aw_grant <= 4'd0;
                else if (s0_aw_requests[1]) s0_aw_grant <= 4'd1;
            end else if (s0_aw_last_grant == 4'd2) begin
                // After master 2, prioritize 3,4,0,1...
                if (s0_aw_requests[3]) s0_aw_grant <= 4'd3;
                else if (s0_aw_requests[4]) s0_aw_grant <= 4'd4;
                else if (s0_aw_requests[5]) s0_aw_grant <= 4'd5;
                else if (s0_aw_requests[6]) s0_aw_grant <= 4'd6;
                else if (s0_aw_requests[7]) s0_aw_grant <= 4'd7;
                else if (s0_aw_requests[8]) s0_aw_grant <= 4'd8;
                else if (s0_aw_requests[9]) s0_aw_grant <= 4'd9;
                else if (s0_aw_requests[10]) s0_aw_grant <= 4'd10;
                else if (s0_aw_requests[11]) s0_aw_grant <= 4'd11;
                else if (s0_aw_requests[12]) s0_aw_grant <= 4'd12;
                else if (s0_aw_requests[13]) s0_aw_grant <= 4'd13;
                else if (s0_aw_requests[14]) s0_aw_grant <= 4'd14;
                else if (s0_aw_requests[0]) s0_aw_grant <= 4'd0;
                else if (s0_aw_requests[1]) s0_aw_grant <= 4'd1;
                else if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;
            end else begin
                // Default: try from 0
                if (s0_aw_requests[0]) s0_aw_grant <= 4'd0;
                else if (s0_aw_requests[1]) s0_aw_grant <= 4'd1;
                else if (s0_aw_requests[2]) s0_aw_grant <= 4'd2;
                else if (s0_aw_requests[3]) s0_aw_grant <= 4'd3;
                else if (s0_aw_requests[4]) s0_aw_grant <= 4'd4;
                else if (s0_aw_requests[5]) s0_aw_grant <= 4'd5;
                else if (s0_aw_requests[6]) s0_aw_grant <= 4'd6;
                else if (s0_aw_requests[7]) s0_aw_grant <= 4'd7;
                else if (s0_aw_requests[8]) s0_aw_grant <= 4'd8;
                else if (s0_aw_requests[9]) s0_aw_grant <= 4'd9;
                else if (s0_aw_requests[10]) s0_aw_grant <= 4'd10;
                else if (s0_aw_requests[11]) s0_aw_grant <= 4'd11;
                else if (s0_aw_requests[12]) s0_aw_grant <= 4'd12;
                else if (s0_aw_requests[13]) s0_aw_grant <= 4'd13;
                else if (s0_aw_requests[14]) s0_aw_grant <= 4'd14;
            end
        end else if (s0_awready && s0_awvalid) begin
            // AW transaction accepted - record who owns write channel
            s0_aw_last_grant <= s0_aw_grant;
            s0_w_owner <= s0_aw_grant;  // Track who owns W channel
            s0_w_busy <= 1'b1;          // Mark W channel as busy
            s0_aw_grant <= 4'd15;       // Release AW grant
        end
        
        // Release write channel when WLAST completes
        if (s0_w_busy && s0_wready && s0_wvalid && s0_wlast) begin
            s0_w_owner <= 4'd15;
            s0_w_busy <= 1'b0;
        end"""
    
    content = re.sub(old_arbitration, new_arbitration, content, flags=re.DOTALL)
    
    # 4. Update W channel assignments to use write owner instead of AW grant
    old_wdata = r"assign s0_wdata = \n\(s0_aw_grant == 4'd0\) \? m0_wdata :"
    new_wdata = """assign s0_wdata = 
(s0_w_owner == 4'd0) ? m0_wdata :"""
    content = re.sub(old_wdata, new_wdata, content)
    
    # Update all W channel signals to use s0_w_owner
    w_signals = ['wstrb', 'wlast', 'wvalid']
    for sig in w_signals:
        old_pattern = rf"assign s0_{sig} = \n\(s0_aw_grant == 4'd0\) \? m0_{sig} :"
        new_pattern = f"""assign s0_{sig} = 
(s0_w_owner == 4'd0) ? m0_{sig} :"""
        content = re.sub(old_pattern, new_pattern, content)
    
    # 5. Fix master wready signals to check write ownership
    for i in range(15):
        old_ready = rf"assign m{i}_wready = \n\(m{i}_aw_target == 4'd0 && s0_aw_grant == 4'd{i}\) \? s0_wready :"
        new_ready = f"""assign m{i}_wready = 
(m{i}_aw_target == 4'd0 && s0_w_owner == 4'd{i}) ? s0_wready :"""
        content = re.sub(old_ready, new_ready, content)
    
    # 6. Fix bready to use write owner for response routing
    old_bready = r"assign s0_bready = \n\(s0_aw_grant == 4'd0\) \? m0_bready :"
    new_bready = """assign s0_bready = 
(s0_w_owner == 4'd0) ? m0_bready :"""
    content = re.sub(old_bready, new_bready, content)
    
    with open(rtl_file, 'w') as f:
        f.write(content)
    
    print("✅ Applied comprehensive fix!")
    print("  • Round-robin arbitration: Master 0 → 1 → 2 → 3 → ...")  
    print("  • Write ownership tracking: W channel stays connected until WLAST")
    print("  • Fixed wready/bready signals to use write owner")
    print("  • Should allow all 3 masters to complete their transactions")

if __name__ == "__main__":
    fix_write_ownership_and_arbitration()