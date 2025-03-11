#!/bin/bash
rm -rf pfd_wave*
rm -rf xce*

# run_xrun.sh
xrun -sv pfd.v pfd_tb.v -access +rwc

