clear -all

analyze -sv shft_add_mul_32b.v
analyze -sv formal_tb.v

elaborate -bbox_mul 128 -top  top 

clock clk
reset ~rst_n


prove -all

#report -al
