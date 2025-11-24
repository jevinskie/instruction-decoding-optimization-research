from instdec.pla_file import PLA, Term

four_bit_pal_test_a = r"""
.i 4
.o 1
.ilb A B C D
.ob MAJ
.p 8
0111 1
1001 1
1010 1
1011 1
1100 1
1101 1
1110 1
1111 1
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
-111 1
11-- 1
1-1- 1
1--1 1
.e
"""


def test_pla_file_load_a():
    po = PLA.from_str(four_bit_pal_test_a)
    assert po == PLA(
        terms=[
            Term(ins="0111", outs="1"),
            Term(ins="1001", outs="1"),
            Term(ins="1010", outs="1"),
            Term(ins="1011", outs="1"),
            Term(ins="1100", outs="1"),
            Term(ins="1101", outs="1"),
            Term(ins="1110", outs="1"),
            Term(ins="1111", outs="1"),
        ],
        num_in=4,
        num_out=1,
        labels_in=["A", "B", "C", "D"],
        labels_out=["MAJ"],
    )


def test_pla_file_load_b():
    po = PLA.from_str(four_bit_pal_test_b)
    assert po == PLA(
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


def test_pla_file_load_c():
    po = PLA.from_str(four_bit_pal_test_c)
    assert po == PLA(
        terms=[
            Term(ins="-111", outs="1"),
            Term(ins="11--", outs="1"),
            Term(ins="1-1-", outs="1"),
            Term(ins="1--1", outs="1"),
        ],
        num_in=4,
        num_out=1,
        labels_in=["A", "B", "C", "D"],
        labels_out=["MAJ"],
    )
