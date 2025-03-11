clear -all

analyze -sv mul_32b.v
analyze -sv mul_32b_formal.sv

elaborate -bbox_mul 128 -top multiplier_32bit_formal  

clock clk
reset ~rst_n


prove -all

#report -al
