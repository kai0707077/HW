`define ERROR_INJECTION

module multiplier_32bit(
    input wire clk,
    input wire rst_n,
    input wire [31:0] a,
    input wire [31:0] b,
    output reg  [63:0] product
    
);
    always @(posedge clk or negedge rst_n)begin
        if(!rst_n)begin
            product <= 64'b0;
        end
        `ifdef ERROR_INJECTION
        else if (a==32'h12345677)begin
            product <= a+1;
        end
        `endif
        else begin
            product <= a*b;
        end
    end
endmodule
