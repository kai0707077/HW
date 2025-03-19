`timescale 1ns/1fs

module PFD_with_calibration (
    input wire  ref_clk,         
    input wire  fb_clk,          
    input wire  rst_n,           
    output reg  up,              
    output reg  down,    
    output reg  ref_clk_is_faster,
    output reg  ref_clk_is_slower,
    output wire freq_check_done,            
    output wire calibration_done 
);
  
    //=============================
    //params
    //=============================
    //parameter FREQ_CHECK_T          = 10000099;//10Mhz+-1~100
    parameter FREQ_CHECK_T          = 51;//100Mhz vs 98.0392 Mhz ONLY FOR FAST TEST!!!
    parameter INITIAL_PHASE_ERROR_T = FREQ_CHECK_T/2+10;
    parameter PLL_CALIBRATION_T     = 10;
    parameter FB_STABLE_CYCLE       = INITIAL_PHASE_ERROR_T+FREQ_CHECK_T*2+PLL_CALIBRATION_T;
    parameter CLK_CNTR_WIDTH        = $clog2(FB_STABLE_CYCLE)+1;

    //=============================
    //wires
    //=============================
    wire clear;
    wire freq_check_done_nx;
    wire ref_clk_cntr_rst;
    wire ref_clk_is_faster_nx; 
    wire ref_clk_is_slower_nx; 

    //=============================
    //regs
    //=============================
    reg [7:0]                up_counter;       
    reg [7:0]                down_counter;    
    reg                      freq_check_done_reg;
    reg [CLK_CNTR_WIDTH-1:0] ref_clk_cntr;


    //=============================
    //up/down flip-flop
    //=============================
    always @(posedge ref_clk or posedge clear or negedge rst_n) begin
        if (!rst_n) begin
            up <= 1'b0;         
        end else if (clear) begin
            up <= 1'b0;         
        end else begin
            up <= 1'b1;         
        end
    end
    always @(posedge fb_clk or posedge clear or negedge rst_n) begin
        if (!rst_n) begin
            down <= 1'b0;      
        end else if (clear) begin
            down <= 1'b0;      
        end else begin
            down <= 1'b1;       
        end
    end
    //up/down clear
    assign clear = up & down;

    //=============================
    //up/down counter
    //=============================
    always @(posedge ref_clk or negedge rst_n) begin
        if (!rst_n) begin
            up_counter <= 8'd0;
        end
        else if(freq_check_done_reg) begin
            up_counter <= 8'd0;
        end
        else if(up) begin
            up_counter <= up_counter + 1;
        end
    end
    always @(posedge fb_clk or negedge rst_n) begin
        if (!rst_n) begin
            down_counter <= 8'd0;
        end
        else if(freq_check_done_reg) begin
            down_counter <= 8'd0;
        end
        else if(down) begin
            down_counter <= down_counter + 1;
        end
    end

    //=============================
    //freq_check_done
    //=============================
    assign ref_clk_is_faster_nx  = up_counter[1];
    assign ref_clk_is_slower_nx  = down_counter[1];
    assign freq_check_done       = freq_check_done_reg;
    assign freq_check_done_nx    = (ref_clk_is_faster_nx|ref_clk_is_slower_nx);
    always @(posedge ref_clk or negedge rst_n) begin
        if (!rst_n) begin
            freq_check_done_reg <= 1'b0;
            ref_clk_is_faster   <= 1'b0;
            ref_clk_is_slower   <= 1'b0;
        end
        else  begin
            freq_check_done_reg <= freq_check_done_nx; 
            ref_clk_is_faster   <= ref_clk_is_faster_nx; 
            ref_clk_is_slower   <= ref_clk_is_slower_nx; 
        end
    end

    //=============================
    //PLL Done => reach feedback clk except stable cycle(inital_pahse_error_T+freq_check_T+PLL_adjust_T)
    //=============================
    assign calibration_done = (ref_clk_cntr>=FB_STABLE_CYCLE) ? 1'b1 :  1'b0 ;
    assign ref_clk_cntr_rst = (freq_check_done | calibration_done);
    always @(posedge ref_clk or negedge rst_n) begin
        if (!rst_n) begin
            ref_clk_cntr <= 1'b0; 
        end
        else  begin
            if (ref_clk_cntr_rst) begin
                ref_clk_cntr <= 1'b0; 
            end
            else begin
                ref_clk_cntr <= ref_clk_cntr+1'b1; 
            end
        end
    end

endmodule
