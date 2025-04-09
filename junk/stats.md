8. Printing statistics.

=== a64dec ===

   Number of wires:               4477
   Number of wire bits:           4508
   Number of public wires:           2
   Number of public wire bits:      33
   Number of ports:                  2
   Number of port bits:             33
   Number of memories:               0
   Number of memory bits:            0
   Number of processes:              0
   Number of cells:               4476
     $_ANDNOT_                    1100
     $_AND_                         13
     $_MUX_                          9
     $_NAND_                        86
     $_NOR_                        144
     $_NOT_                         31
     $_ORNOT_                      247
     $_OR_                        2846

End of script. Logfile hash: 38192a9817, CPU: user 0.65s system 0.04s, MEM: 86.73 MB peak

^ exact

8. Printing statistics.

=== a64dec ===

   Number of wires:               4429
   Number of wire bits:           4460
   Number of public wires:           2
   Number of public wire bits:      33
   Number of ports:                  2
   Number of port bits:             33
   Number of memories:               0
   Number of memory bits:            0
   Number of processes:              0
   Number of cells:               4428
     $_ANDNOT_                    1057
     $_AND_                         16
     $_NAND_                        93
     $_NOR_                        144
     $_NOT_                         30
     $_ORNOT_                      241
     $_OR_                        2847

End of script. Logfile hash: 94f28ee140, CPU: user 0.64s system 0.04s, MEM: 79.20 MB peak

^ exact-many-lexsort

6.39.1.2. Re-integrating ABC results.
ABC RESULTS:               AND cells:     1732
ABC RESULTS:            ANDNOT cells:      258
ABC RESULTS:               MUX cells:        3
ABC RESULTS:              NAND cells:      994
ABC RESULTS:               NOR cells:      121
ABC RESULTS:               NOT cells:        1
ABC RESULTS:                OR cells:       97
ABC RESULTS:             ORNOT cells:       13
ABC RESULTS:        internal signals:     5175
ABC RESULTS:           input signals:       32
ABC RESULTS:          output signals:        1
Removing temp directory.


6.43.13. Executing AIGMAP pass (map logic to AIG).
Module a64dec: replaced 1486 cells with 3315 new cells, skipped 1733 cells.
  replaced 6 cell types:
     994 $_NAND_
      97 $_OR_
     121 $_NOR_
     258 $_ANDNOT_
      13 $_ORNOT_
       3 $_MUX_
  not replaced 2 cell types:
       1 $_NOT_
    1732 $_AND_

6.43.13.1. Executing ABC9_OPS pass (helper functions for ABC9).

6.43.13.2. Executing ABC9_OPS pass (helper functions for ABC9).

6.43.13.3. Executing XAIGER backend.
<suppressed ~5 debug messages>
Extracted 3224 AND gates and 5082 wires from module `a64dec' to a netlist network with 32 inputs and 1 outputs.

6.43.13.4. Executing ABC9_EXE pass (technology mapping using ABC9).

6.43.13.5. Executing ABC9.
Running ABC command: "<yosys-exe-dir>/yosys-abc" -s -f <abc-temp-dir>/abc.script 2>&1
ABC: ABC command line: "source <abc-temp-dir>/abc.script".
ABC:
ABC: + read_lut <abc-temp-dir>/input.lut
ABC: + read_box <abc-temp-dir>/input.box
ABC: + &read <abc-temp-dir>/input.xaig
ABC: + &ps
ABC: <abc-temp-dir>/input : i/o =     32/      1  and =    3218  lev =   16 (16.00)  mem = 0.04 MB  box = 0  bb = 0
ABC: + &scorr
ABC: Warning: The network is combinational.
ABC: + &sweep
ABC: + &dc2
ABC: + &dch -f
ABC: + &ps
ABC: <abc-temp-dir>/input : i/o =     32/      1  and =    5436  lev =   17 (16.00)  mem = 0.06 MB  ch =  585  box = 0  bb = 0
ABC: cst =       0  cls =    518  lit =     585  unused =    4365  proof =     0
ABC: + &if -W 750 -v
ABC: K = 4. Memory (bytes): Truth =    0. Cut =   52. Obj =  136. Set =  564. CutMin = no
ABC: Node =    5436.  Ch =   518.  Total mem =    0.79 MB. Peak cut mem =    0.46 MB.
ABC: P:  Del = 15609.00.  Ar =    1911.0.  Edge =     6837.  Cut =    35739.  T =     0.01 sec
ABC: P:  Del = 15416.00.  Ar =    1881.0.  Edge =     6861.  Cut =    33862.  T =     0.01 sec
ABC: P:  Del = 15416.00.  Ar =    1762.0.  Edge =     6404.  Cut =    34779.  T =     0.00 sec
ABC: F:  Del = 15416.00.  Ar =    1681.0.  Edge =     6193.  Cut =    26191.  T =     0.00 sec
ABC: A:  Del = 15416.00.  Ar =    1672.0.  Edge =     5611.  Cut =    24352.  T =     0.01 sec
ABC: A:  Del = 15416.00.  Ar =    1670.0.  Edge =     5601.  Cut =    24376.  T =     0.01 sec
ABC: Total time =     0.03 sec
ABC: + &write -n <abc-temp-dir>/output.aig
ABC: + &mfs
ABC: + &ps -l
ABC: <abc-temp-dir>/input : i/o =     32/      1  and =    3925  lev =   18 (18.00)  mem = 0.05 MB  box = 0  bb = 0
ABC: Mapping (K=4)  :  lut =   1663  edge =    5577  lev =    9 (9.00)  mem = 0.05 MB
ABC: LUT = 1663 : 2=336 20.2 %  3=403 24.2 %  4=924 55.6 %  Ave = 3.35
ABC: + &write -n <abc-temp-dir>/output.aig
ABC: + time

Removed 3557 unused cells and 3590 unused wires.
Removed 1 unused cells and 6568 unused wires.

Combining LUTs.
Number of LUTs:     1663
  2-LUT              336
  3-LUT              403
  4-LUT              924
  with \SB_CARRY    (#0)    0
  with \SB_CARRY    (#1)    0

=== a64dec ===

   Number of wires:                771
   Number of wire bits:           3605
   Number of public wires:         771
   Number of public wire bits:    3605
   Number of ports:                  2
   Number of port bits:             33
   Number of memories:               0
   Number of memory bits:            0
   Number of processes:              0
   Number of cells:               1663
     SB_LUT4                      1663

End of script. Logfile hash: 4218335aca, CPU: user 1.43s system 0.07s, MEM: 112.48 MB peak

^ exact-many-lexsort ice40



6.39.1.2. Re-integrating ABC results.
ABC RESULTS:               AND cells:     2023
ABC RESULTS:            ANDNOT cells:      251
ABC RESULTS:               MUX cells:        2
ABC RESULTS:              NAND cells:     1005
ABC RESULTS:               NOR cells:      120
ABC RESULTS:               NOT cells:        1
ABC RESULTS:                OR cells:       74
ABC RESULTS:             ORNOT cells:       15
ABC RESULTS:        internal signals:     5245
ABC RESULTS:           input signals:       32
ABC RESULTS:          output signals:        1
Removing temp directory.

6.43.13. Executing AIGMAP pass (map logic to AIG).
Module a64dec: replaced 1467 cells with 3227 new cells, skipped 2024 cells.
  replaced 6 cell types:
    1005 $_NAND_
      74 $_OR_
     120 $_NOR_
     251 $_ANDNOT_
      15 $_ORNOT_
       2 $_MUX_
  not replaced 2 cell types:
       1 $_NOT_
    2023 $_AND_

6.43.13.1. Executing ABC9_OPS pass (helper functions for ABC9).

6.43.13.2. Executing ABC9_OPS pass (helper functions for ABC9).

6.43.13.3. Executing XAIGER backend.
<suppressed ~5 debug messages>
Extracted 3494 AND gates and 5285 wires from module `a64dec' to a netlist network with 32 inputs and 1 outputs.

6.43.13.4. Executing ABC9_EXE pass (technology mapping using ABC9).

6.43.13.5. Executing ABC9.
Running ABC command: "<yosys-exe-dir>/yosys-abc" -s -f <abc-temp-dir>/abc.script 2>&1
ABC: ABC command line: "source <abc-temp-dir>/abc.script".
ABC:
ABC: + read_lut <abc-temp-dir>/input.lut
ABC: + read_box <abc-temp-dir>/input.box
ABC: + &read <abc-temp-dir>/input.xaig
ABC: + &ps
ABC: <abc-temp-dir>/input : i/o =     32/      1  and =    3491  lev =   15 (15.00)  mem = 0.04 MB  box = 0  bb = 0
ABC: + &scorr
ABC: Warning: The network is combinational.
ABC: + &sweep
ABC: + &dc2
ABC: + &dch -f
ABC: + &ps
ABC: <abc-temp-dir>/input : i/o =     32/      1  and =    6345  lev =   16 (15.00)  mem = 0.07 MB  ch =  607  box = 0  bb = 0
ABC: cst =       0  cls =    559  lit =     607  unused =    5211  proof =     0
ABC: + &if -W 750 -v
ABC: K = 4. Memory (bytes): Truth =    0. Cut =   52. Obj =  136. Set =  564. CutMin = no
ABC: Node =    6345.  Ch =   559.  Total mem =    0.92 MB. Peak cut mem =    0.62 MB.
ABC: P:  Del = 15032.00.  Ar =    2039.0.  Edge =     7331.  Cut =    42689.  T =     0.01 sec
ABC: P:  Del = 15005.00.  Ar =    1978.0.  Edge =     7260.  Cut =    40457.  T =     0.01 sec
ABC: P:  Del = 15005.00.  Ar =    1854.0.  Edge =     6791.  Cut =    40946.  T =     0.01 sec
ABC: F:  Del = 15005.00.  Ar =    1787.0.  Edge =     6617.  Cut =    30988.  T =     0.00 sec
ABC: A:  Del = 15005.00.  Ar =    1782.0.  Edge =     6037.  Cut =    28665.  T =     0.01 sec
ABC: A:  Del = 15005.00.  Ar =    1781.0.  Edge =     6021.  Cut =    28829.  T =     0.01 sec
ABC: Total time =     0.04 sec
ABC: + &write -n <abc-temp-dir>/output.aig
ABC: + &mfs
ABC: + &ps -l
ABC: <abc-temp-dir>/input : i/o =     32/      1  and =    4233  lev =   18 (18.00)  mem = 0.05 MB  box = 0  bb = 0
ABC: Mapping (K=4)  :  lut =   1772  edge =    5989  lev =    9 (9.00)  mem = 0.05 MB
ABC: LUT = 1772 : 2=328 18.5 %  3=443 25.0 %  4=1001 56.5 %  Ave = 3.38
ABC: + &write -n <abc-temp-dir>/output.aig
ABC: + time
ABC: elapse: 1.99 seconds, total: 1.99 seconds

6.43.13.6. Executing AIGER frontend.
<suppressed ~74 debug messages>
Removed 3710 unused cells and 3743 unused wires.

6.43.13.7. Executing ABC9_OPS pass (helper functions for ABC9).
ABC RESULTS:              $lut cells:     1772
ABC RESULTS:           input signals:        1
ABC RESULTS:          output signals:        1
Removing temp directory.
Removed 1 unused cells and 6752 unused wires.

Combining LUTs.
Number of LUTs:     1772
  2-LUT              328
  3-LUT              443
  4-LUT             1001
  with \SB_CARRY    (#0)    0
  with \SB_CARRY    (#1)    0


Removed 0 unused cells and 4498 unused wires.

=== a64dec ===

   Number of wires:                820
   Number of wire bits:           3770
   Number of public wires:         820
   Number of public wire bits:    3770
   Number of ports:                  2
   Number of port bits:             33
   Number of memories:               0
   Number of memory bits:            0
   Number of processes:              0
   Number of cells:               1772
     SB_LUT4                      1772

End of script. Logfile hash: d88a10d18f, CPU: user 1.45s system 0.06s, MEM: 108.17 MB peak


^ exact ice40
