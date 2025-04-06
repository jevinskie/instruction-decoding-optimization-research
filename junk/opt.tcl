#!/usr/bin/env yosys

# yosys design -reset
yosys read_verilog vlog.v
yosys hierarchy -top a64dec
yosys proc
yosys opt_clean
yosys opt
# yosys synth_ice40 -device u -top a64dec -abc2 -json vlog-opt.json -blif vlog-opt.blif -edif vlog-opt.edif
yosys synth
yosys write_verilog vlog-opt.v
yosys stat
