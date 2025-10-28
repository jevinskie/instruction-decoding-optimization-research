#!/usr/bin/env python3

import operator
from collections.abc import Callable
from functools import reduce
from typing import Any

from rich import print

tts = """
-111
11--
1-1-
1--1
"""

ttm = [
    [0, 1, 1, 1],
    [1, 1, 0, 0],
    [1, 0, 1, 0],
    [1, 0, 0, 1],
]

inv_ttm = [
    [1, 0, 0, 0],
    [0, 0, 1, 1],
    [0, 1, 0, 1],
    [0, 1, 1, 0],
]

ttd = [
    [1, 0, 0, 0],
    [0, 0, 1, 1],
    [0, 1, 0, 1],
    [0, 1, 1, 0],
]

inv_ttd = [
    [0, 1, 1, 1],
    [1, 1, 0, 0],
    [1, 0, 1, 0],
    [1, 0, 0, 1],
]


def mat_bin_op(
    m_a: list[list[int]],
    m_b: list[list[int]],
    bin_op: Callable[[int, int], int],
    red_op=Callable[[int, int], int],
) -> list[list[int]]:
    return [
        [reduce(red_op, [bin_op(x, y) for (x, y) in zip(r, c)]) for c in zip(*m_b)] for r in m_a
    ]


def eval_lut(ibm: tuple[int, int, int, int]) -> Any:
    [a, b, c, d] = ibm
    # bm_sum = [[]]
    sums = mat_bin_op([list(ibm)], ttm, operator.__and__, operator.__or__)
    print(f"sums:\n{sums}")

    prods = mat_bin_op(sums, ttd, operator.__and__, operator.__or__)
    print(f"prods:\n{prods}")
    return 0


print(eval_lut((1, 1, 1, 0)))
print(eval_lut((1, 0, 0, 1)))
print(eval_lut((0, 1, 0, 1)))
print(eval_lut((1, 0, 0, 0)))
