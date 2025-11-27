#!/usr/bin/env yosys

yosys design -reset
yosys read_verilog q.v
yosys hierarchy -check -top circt
yosys proc
yosys opt_clean
yosys opt
#yosys xprop
yosys sat -enable_undef -set-assumes -prove-asserts -show-all
yosys opt_clean
yosys opt
# yosys synth_ice40 -device u -top a64dec -abc2 -json expresso-vlog-opt-ice40.json -blif espresso-vlog-opt-ice40.blif -edif espresso-vlog-opt-ice40.edif
# yosys synth
# yosys abc -P 10
yosys write_verilog q-opt.v
# yosys write_smt2 -stdt q-opt.smt2
yosys stat
