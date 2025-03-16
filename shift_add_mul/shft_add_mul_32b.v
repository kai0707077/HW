`timescale 1ns/1ps

module shift_add_multiplier (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         start,         
    input  wire [31:0]  A,             
    input  wire [31:0]  B,             
    output wire [63:0]  product,       
    output wire         done           
);

    reg [63:0] partial_product;
    reg [31:0] multiplicand;
    reg [63:0] multiplicand_tmp;
    reg [31:0] multiplier;
    reg [5 :0] bit_count;   
    reg        done_reg;
    reg        start_flag;

    assign done    = done_reg;
    assign product = partial_product;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            partial_product  <= 64'd0;
            multiplicand_tmp <= 64'd0;
            multiplier       <= 32'd0;
            bit_count        <= 6'd0;
            done_reg         <= 1'b0;
            start_flag       <= 1'b0;
        end
        else begin
            if (start) begin
                partial_product  <= 64'd0;
                multiplicand_tmp <= {32'b0,A};
                multiplier       <= B;
                bit_count        <= 6'd0;
                done_reg         <= 1'b0;
                start_flag       <= 1'b1;
            end
            else if (!done_reg && start_flag) begin
                //accumulate result when multiplier LSB eq 1
                if (multiplier[0] == 1'b1) begin
                    partial_product <= partial_product + multiplicand_tmp;
                end

                multiplier       <= multiplier >> 1;
                multiplicand_tmp <= multiplicand_tmp << 1;
                bit_count        <= bit_count + 1'b1;

                if (bit_count == 6'd31) begin
                    done_reg   <= 1'b1;
                    start_flag <= 1'b0;
                end
            end
        end
    end

endmodule
