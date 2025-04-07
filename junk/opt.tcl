#!/usr/bin/env yosys

yosys design -reset
yosys read_verilog vlog.v
yosys hierarchy -top a64dec
yosys proc
yosys opt_clean
yosys opt
yosys synth_ice40 -device u -top a64dec -abc2 -json vlog-opt-ice40.json -blif vlog-opt-ice40.blif -edif vlog-opt-ice40.edif
# yosys synth
yosys write_verilog vlog-opt.v
yosys stat
