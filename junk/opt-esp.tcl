#!/usr/bin/env yosys

yosys design -reset
yosys read_verilog espresso-vlog.v
yosys hierarchy -top a64dec
yosys proc
yosys opt_clean
yosys opt
yosys synth_ice40 -device u -top a64dec -abc2 -json expresso-vlog-opt-ice40.json -blif espresso-vlog-opt-ice40.blif -edif espresso-vlog-opt-ice40.edif
# yosys synth
yosys write_verilog espresso-vlog-opt.v
yosys stat
