`timescale 1ns/1ps

module pfd (
  input  wire ref_clk,
  input  wire fd_clk,
  input  wire rst_n,
  output wire fast, 
  output wire slow 
);

    reg[63:0] ref_clk_cntr;
    reg[63:0]  fd_clk_cntr;
    wire  signed [63:0]  diff;


    always@(posedge ref_clk or negedge rst_n)begin
        if(!rst_n)begin
            ref_clk_cntr<=0;
        end
        else begin
            ref_clk_cntr<=ref_clk_cntr+1;
        end
    end


    always@(posedge fd_clk or negedge rst_n)begin
        if(!rst_n)begin
            fd_clk_cntr<=0;
        end
        else begin
            fd_clk_cntr<=fd_clk_cntr+1;
        end
    end

    assign diff = fd_clk_cntr - ref_clk_cntr;
    //always@(posedge ref_clk or negedge rst_n)begin
    //    if(!rst_n)begin
    //        diff<=0;
    //    end
    //    else begin
    //        diff <= fd_clk_cntr - ref_clk_cntr;
    //    end
    //end


    assign slow = (diff>1) ? 1'b1 : 1'b0 ;
    assign fast = (diff<-1) ? 1'b1 : 1'b0 ;


endmodule
