from instdec.pla_file import PLA, Term

four_bit_pal_test_a = r"""
.i 4
.o 1
.ilb A B C D
.ob MAJ
.p 8
1111 1
0111 1
1011 1
1101 1
1001 1
1110 1
1010 1
1100 1
.e
"""

four_bit_pal_test_b = r"""
.i 4
.o 1
.ilb A B C D
.ob MAJ
.p 5
0111 1
1011 1
1101 1
1110 1
1111 1
.e
"""

four_bit_pal_test_c = r"""
.i 4
.o 1
.ilb A B C D
.ob MAJ
.p 4
11-- 1
1-1- 1
1--1 1
-111 1
.e
"""

multiout_test_d = r"""
.i 4
.o 2
.ilb A B C D
.ob MAJ0 MAJ1
.p 4
-111 10
11-- 11
1-1- 1-
1--1 01
.e
"""

GOLD_A = PLA(
    terms=[
        Term(ins="1111", outs="1"),
        Term(ins="0111", outs="1"),
        Term(ins="1011", outs="1"),
        Term(ins="1101", outs="1"),
        Term(ins="1001", outs="1"),
        Term(ins="1110", outs="1"),
        Term(ins="1010", outs="1"),
        Term(ins="1100", outs="1"),
    ],
    num_in=4,
    num_out=1,
    labels_in=["A", "B", "C", "D"],
    labels_out=["MAJ"],
)

GOLD_B = PLA(
    terms=[
        Term(ins="0111", outs="1"),
        Term(ins="1011", outs="1"),
        Term(ins="1101", outs="1"),
        Term(ins="1110", outs="1"),
        Term(ins="1111", outs="1"),
    ],
    num_in=4,
    num_out=1,
    labels_in=["A", "B", "C", "D"],
    labels_out=["MAJ"],
)

GOLD_C = PLA(
    terms=[
        Term(ins="11--", outs="1"),
        Term(ins="1-1-", outs="1"),
        Term(ins="1--1", outs="1"),
        Term(ins="-111", outs="1"),
    ],
    num_in=4,
    num_out=1,
    labels_in=["A", "B", "C", "D"],
    labels_out=["MAJ"],
)

GOLD_D = PLA(
    terms=[
        Term(ins="-111", outs="10"),
        Term(ins="11--", outs="11"),
        Term(ins="1-1-", outs="1-"),
        Term(ins="1--1", outs="01"),
    ],
    num_in=4,
    num_out=2,
    labels_in=["A", "B", "C", "D"],
    labels_out=["MAJ0", "MAJ1"],
)


def test_pla_file_load_a():
    po = PLA.from_str(four_bit_pal_test_a)
    assert po == GOLD_A


def test_pla_file_load_b():
    po = PLA.from_str(four_bit_pal_test_b)
    assert po == GOLD_B


def test_pla_file_load_c():
    po = PLA.from_str(four_bit_pal_test_c)
    assert po == GOLD_C


def test_pla_file_load_d():
    po = PLA.from_str(multiout_test_d)
    assert po == GOLD_D


def test_verilog_a():
    pa = PLA.from_str(four_bit_pal_test_a)
    print("\n" + pa.to_verilog())
    open("qa.v", "w").write(pa.to_verilog())
    pc = PLA.from_str(four_bit_pal_test_c)
    print("\n" + pc.to_verilog())
    open("qc.v", "w").write(pc.to_verilog())
