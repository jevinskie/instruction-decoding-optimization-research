#!/usr/bin/env python3

import operator
from collections.abc import Callable
from functools import reduce
from typing import cast

import numpy as np
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


def mat_bin_op2(
    m_a: list[list[int]],
    m_b: list[list[int]],
    bin_op: Callable[[int, int], int],
    red_op=Callable[[int, int], int],
    ident: int = 0,
) -> list[list[int]]:
    m = len(m_a)
    n1 = len(m_a[0])
    n2 = len(m_b)
    assert n1 == n2
    n = n1
    p = len(m_b[0])
    print(f"m: {m} n: {n} p: {p}")
    r: list[list[int]] = [[ident] * p for _ in range(m)]

    for i in range(m):
        for j in range(p):
            for k in range(n):
                v = r[i][j]
                a = m_a[i][k]
                b = m_b[k][j]
                bv = bin_op(a, b)
                rv = red_op(v, bv)
                r[i][j] = rv
    return cast(list[list[int]], r)


def mat_mul(m_a: list[list[int]], m_b: list[list[int]]) -> list[list[int]]:
    return mat_bin_op2(m_a, m_b, operator.__mul__, operator.__add__)


def mat_mul_bin(m_a: list[list[int]], m_b: list[list[int]]) -> list[list[int]]:
    return mat_bin_op2(m_a, m_b, operator.__and__, operator.__or__)


def dot_prod_generic(
    v_a: list[int],
    v_b: list[int],
    bin_op: Callable[[int, int], int],
    red_op=Callable[[int, int], int],
    ident: int = 0,
) -> int:
    assert len(v_a) == len(v_b)
    r = ident
    for i in range(len(v_a)):
        r = red_op(bin_op(v_a[i], v_b[i]), r)
    return r


def dot_prod(v_a: list[int], v_b: list[int]) -> int:
    return dot_prod_generic(v_a, v_b, operator.__mul__, operator.__add__)


def dot_prod_bin(v_a: list[int], v_b: list[int]) -> int:
    return dot_prod_generic(v_a, v_b, operator.__and__, operator.__or__)


def eval_lut(ibm: tuple[int, int, int, int], f=mat_mul, g=dot_prod) -> None:
    [a, b, c, d] = ibm
    print(f"lut: {ibm}")
    sums = f([list(ibm)], ttm)
    print(f"sums:\n{sums}")

    prods = f(sums, ttm)
    print(f"prods:\n{prods}")

    sp = g(sums[0], prods[0])
    print(f"sp:\n{sp}")
    print()


t_maj3 = (1, 1, 1, 0)
t_maj2a = (1, 0, 0, 1)
t_no_maj2b = (0, 1, 0, 1)
t_no_maj1 = (1, 0, 0, 0)

eval_lut(t_maj3)
eval_lut(t_maj2a)
eval_lut(t_no_maj2b)
eval_lut(t_no_maj1)

print("\n\nbin:\n\n")

eval_lut(t_maj3, mat_mul_bin, dot_prod_bin)
eval_lut(t_maj2a, mat_mul_bin, dot_prod_bin)
eval_lut(t_no_maj2b, mat_mul_bin, dot_prod_bin)
eval_lut(t_no_maj1, mat_mul_bin, dot_prod_bin)

# NumPy


def eval_lut_np(ibm: tuple[int, int, int, int], f=mat_mul, g=dot_prod) -> None:
    [a, b, c, d] = ibm
    print(f"lut: {ibm}")
    sums = f([list(ibm)], ttm)
    print(f"sums:\n{sums}")

    prods = f(sums, ttm)
    print(f"prods:\n{prods}")

    sp = g(sums[0], prods[0])
    print(f"sp:\n{sp}")
    print()


n_maj3 = np.array(t_maj3)
n_maj2a = np.array(t_maj2a)
n_no_maj2b = np.array(t_no_maj2b)
n_no_maj1 = np.array(t_no_maj1)

eval_lut_np(t_maj3)
eval_lut_np(t_maj2a)
eval_lut_np(t_no_maj2b)
eval_lut_np(t_no_maj1)

print("\n\nbin:\n\n")

eval_lut_np(t_maj3, mat_mul_bin, dot_prod_bin)
eval_lut_np(t_maj2a, mat_mul_bin, dot_prod_bin)
eval_lut_np(t_no_maj2b, mat_mul_bin, dot_prod_bin)
eval_lut_np(t_no_maj1, mat_mul_bin, dot_prod_bin)
