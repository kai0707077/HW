`timescale 1ns/1fs

module tb_PFD_with_calibration;

    //input
    reg ref_clk;
    reg fb_clk;
    reg rst_n;
    //output
    wire up;
    wire down;
    wire freq_check_done;
    wire ref_clk_is_faster;
    wire ref_clk_is_slower;
    wire calibration_done;

    PFD_with_calibration uut (
        .ref_clk(ref_clk),
        .fb_clk(fb_clk),
        .rst_n(rst_n),
        .up(up),
        .down(down),
        .ref_clk_is_faster(ref_clk_is_faster),
        .ref_clk_is_slower(ref_clk_is_slower),
        .freq_check_done(freq_check_done),
        .calibration_done(calibration_done)
    );

    
    initial begin
        ref_clk = 0;
        #340;
        forever #50 ref_clk = ~ref_clk; // 10MHz
    end


    integer i;
    initial begin
        fb_clk = 0;
        //forever #49.999995 fb_clk <= ~fb_clk;  10Mhz+1hz
        //forever #49.9995   fb_clk <= ~fb_clk;  10Mhz+100hz
        //forever #50.000005 fb_clk <= ~fb_clk;  10Mhz-1hz
        //forever #50.0005   fb_clk <= ~fb_clk;  10Mhz-100hz
        
        // fb_clk is slower
        for(i = 0; i < 400; i = i + 1) begin
          #51 fb_clk = ~fb_clk;
        end

        // fb_clk is stable after PLL adjsut
        for(i = 0; i < 400; i = i + 1) begin
          #50 fb_clk = ~fb_clk;
        end

        //fb_clk is faster
        for(i = 0; i < 400; i = i + 1) begin
          #49 fb_clk = ~fb_clk;
        end

        //fb_clk is stable after PLL adjsust
        forever #50 fb_clk = ~fb_clk; 

    end

    initial begin
        rst_n <= 0;
        #200;
        rst_n <= 1;
    end

    initial begin
        //#1000000000; //for longer test
        #500000; 
        //$display("After 5000ns: up<=%b, down<=%b, calibration_done<=%b", up, down, calibration_done);

        #5000;
        $display("Simulation Finished");
        $finish;
    end

    initial begin
        $dumpfile("pfd_tb.vcd");
        $dumpvars(0, tb_PFD_with_calibration);
    end

endmodule
