module multiplier_32bit_formal(
    input wire clk,
    input wire rst_n,
    input wire [31:0] a,
    input wire [31:0] b,
    output wire [63:0] product
);

multiplier_32bit dut(
    .clk(clk),
    .rst_n(rst_n),
    .a(a),
    .b(b),
    .product(product)
);



property product_correct_after_reset;
    @(posedge clk) disable iff (!rst_n)
       (rst_n) |-> ##1 (product == ($past(a)) * ($past(b)));
endproperty

assert property (product_correct_after_reset) else $error("Mismatch between product and expected a*b");

endmodule
