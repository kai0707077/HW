`timescale 1ns/1ps

module pfd_tb;
  reg ref_clk;
  reg fd_clk;
  reg rst_n;
  wire fast;
  wire slow;

  // 實例化 PFD 模組
  pfd uut (
    .ref_clk(ref_clk),
    .fd_clk(fd_clk),
    .rst_n(rst_n),
    .fast(fast),
    .slow(slow)
  );

  // 產生 ref_clk：週期 100 ns
  initial begin
    ref_clk = 0;
    forever begin
      #50 ref_clk = ~ref_clk;
    end
  end

  initial begin
    rst_n = 1;
      #10 rst_n=0;
      #50 rst_n=1;
  end



  // 產生 fd_clk：
  // 前 20 個週期：較快 (週期 90 ns)，後 20 個週期：較慢 (週期 110 ns)
  integer i;
  initial begin
    fd_clk = 1;
    // 較快的情況：週期 90 ns (半週期 45 ns)
    for(i = 0; i < 10000; i = i + 1) begin
      //#50.1 fd_clk = ~fd_clk;
      #49.9 fd_clk = ~fd_clk;
    end
    // 較慢的情況：週期 110 ns (半週期 55 ns)
    //for(i = 0; i < 20; i = i + 1) begin
    //  #55 fd_clk = ~fd_clk;
    //end
    #30 $finish;
  end

  // 觀察訊號變化
  initial begin
    //$monitor("time=%0t | ref_clk=%b | fd_clk=%b | signal=%b", $time, ref_clk, fd_clk, signal);
  end

    initial begin
      $dumpfile("pfd_wave.vcd");
      $dumpvars(0, pfd_tb);
    end


endmodule

