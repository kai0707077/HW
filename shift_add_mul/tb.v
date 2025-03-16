`timescale 1ns/1ps

module tb_shift_add_multiplier;

    reg         clk;
    reg         rst_n;
    reg         start;
    reg  [31:0] A;
    reg  [31:0] B;
    wire [63:0] product;
    wire        done;


    shift_add_multiplier dut (
        .clk    (clk),
        .rst_n   (rst_n),
        .start  (start),
        .A      (A),
        .B      (B),
        .product(product),
        .done   (done)
    );

    initial begin
        clk   = 0;
        forever #5 clk = ~clk;
    end
    
    initial begin
        rst_n = 0;
        #20 rst_n = 1;
    end
    
    initial begin
        start <= 0;
        A     <= 32'd0;
        B     <= 32'd0;

        #30;
        // A=10, B=20
        A <= 32'd10;
        B <= 32'd22;

        #10 start <= 1;
        #10 start <= 0;  

        wait(done);

        //$display("Test 1: A=%d, B=%d, product=%d", A, B, product);
        if (product !== A * B) begin
            $display("[ERROR]  : product = %d, expected = %d", product, A * B);
        end else begin
            $display("[MATCH]  : product = %d  expected = %d", product, A * B);
        end

        #50 
        $finish;
    end


    initial begin
        $dumpfile("tb.vcd");
        $dumpvars(0, tb_shift_add_multiplier);
    end

endmodule

