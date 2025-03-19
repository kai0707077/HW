#!/bin/bash

# 腳本名稱: run_xrun.sh
# 用途: 使用 xrun 編譯並模擬 PFD_with_calibration 設計和其 Testbench

# 定義變量
DESIGN_FILE="pfd.v"
TB_FILE="tb_pfd.v"
TOP_MODULE="tb_PFD_with_calibration"
SIM_LOG="xrun.log"
WAVEFORM="pfd_tb.vcd"

# 清理之前的模擬文件
echo "Cleaning up previous simulation files..."
rm -rf xcelium.d INCA_libs $SIM_LOG $WAVEFORM
rm -rf pfd_wave*
rm -rf xce*
#./clean.sh



# 執行 xrun 命令
echo "Running xrun simulation..."
xrun \
    -f flist \
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
