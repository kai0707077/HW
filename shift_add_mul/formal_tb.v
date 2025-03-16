`timescale 1ns/1ps

module top(
    input logic        clk,
    input logic        rst_n,
    input logic        start,
    input logic [31:0] A,
    input logic [31:0] B,
    output wire [63:0] product,
    output wire        done
);

    shift_add_multiplier dut (
        .clk(clk),
        .rst_n(rst_n),
        .start(start),
        .A(A),
        .B(B),
        .product(product),
        .done(done)
    );

    //==============================
    //--- assume ---
    //==============================
    // restric input region 
    assume property (@(posedge clk) A[31:4] == 28'd0);
    assume property (@(posedge clk) B[31:4] == 28'd0);


    //==============================
    //--- assert ----
    //==============================
    //check A*B result
    property check_product;
        @(posedge clk) disable iff (!rst_n)
        $rose(done) |-> (product == $past(A, 33)* $past(B, 33) );
    endproperty
    assert property (check_product) else $error("Mismatch between product and expected a*b");

    // check shift  operation 
    property shift_check;
      @(posedge clk) disable iff (!rst_n)
        (!dut.done_reg && dut.start_flag && !start) |=> 
           (dut.multiplier == $past(dut.multiplier) >> 1)&&
           (dut.multiplicand_tmp == $past(dut.multiplicand_tmp) << 1);
    endproperty
    assert property (shift_check) else $error("Shift operation error detected!");

    // check partial product 
    property add_check;
      @(posedge clk) disable iff (!rst_n)
        (!dut.done_reg && dut.start_flag && !start) |=> 
           (($past(dut.multiplier)&1'b1) ?
             (dut.partial_product == $past(dut.partial_product) + $past(dut.multiplicand_tmp)) :
             (dut.partial_product == $past(dut.partial_product))
           );
    endproperty    
    assert property (add_check) else $error("Add operation error detected!");
    

    //==============================
    //--- cover ---
    //==============================
   

endmodule



