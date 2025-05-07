#!/usr/bin/env yosys

yosys design -reset
yosys read_verilog yosys-smt2-test.v
yosys hierarchy -top test
yosys proc
yosys opt_clean
yosys opt
# yosys synth_ice40 -device u -top a64dec -abc2 -json expresso-vlog-opt-ice40.json -blif espresso-vlog-opt-ice40.blif -edif espresso-vlog-opt-ice40.edif
# yosys synth
yosys write_verilog yosys-smt2-test-opt.v
yosys write_smt2 -tpl yosys-smt2-test.tpl yosys-smt2-test-opt.smt2
yosys stat
