#!/bin/bash


DESIGN_FILE="shft_add_mul_32b.v"
TB_FILE="tb.v"
TOP_MODULE="tb_shift_add_multiplier"
SIM_LOG="xrun.log"
WAVEFORM="tb.vcd"

# 清理之前的模擬文件
echo "Cleaning up previous simulation files..."
rm -rf xcelium.d INCA_libs $SIM_LOG $WAVEFORM
rm -rf pfd_wave*
rm -rf xce*
#./clean.sh



# 執行 xrun 命令
echo "Running xrun simulation..."
xrun \
    -f flist\
    -access +rwc \
    -clean \
    -timescale 1ns/1ps \
    -l $SIM_LOG \
    -top $TOP_MODULE \
    -vcd


# 可選：啟動波形查看工具（SimVision）
# echo "Launching SimVision..."
# simvision $WAVEFORM &

exit 0
