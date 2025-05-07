#!/usr/bin/env yosys

yosys design -reset
yosys read_verilog blink.v
yosys hierarchy -top blink
yosys proc
yosys opt_clean
yosys opt
# yosys synth_ice40 -device u -top a64dec -abc2 -json expresso-vlog-opt-ice40.json -blif espresso-vlog-opt-ice40.blif -edif espresso-vlog-opt-ice40.edif
# yosys synth
yosys write_verilog blink-opt.v
yosys write_smt2 -stdt blink-opt.smt2
yosys stat
