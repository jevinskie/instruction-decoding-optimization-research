#!/usr/bin/env python3


import operator
from collections.abc import Callable
from functools import reduce

import numpy as np

# from rich import print
import sympy as sp
import sympy.logic.boolalg as boa
from more_itertools import chunked

sp.init_printing(use_unicode=False)
# sp.init_printing(use_unicode=True)

tts = """
-111
11--
1-1-
1--1
"""


def mat_bool(m: list[list[int]]) -> list[list[bool]]:
    return [[bool(v) for v in r] for r in m]


def mat_unbool(m: list[list[bool]]) -> list[list[int]]:
    return [[int(v) for v in r] for r in m]


def mat_bool_sym(m: sp.Matrix) -> sp.Matrix:
    return [[bool(v) for v in r] for r in m]


def unbool_sym_scalar(v):
    if isinstance(v, bool):
        if v is True:
            return sp.Integer(1)
        elif v is False:
            return sp.Integer(0)
    elif isinstance(v, (boa.BooleanFalse, boa.BooleanTrue)):
        if isinstance(v, boa.BooleanTrue):
            return sp.Integer(1)
        elif isinstance(v, boa.BooleanFalse):
            return sp.Integer(0)
        else:
            raise ValueError(f"v: {v} type(v): {type(v)}")
    return v


def mat_unbool_sym(m: sp.Matrix) -> sp.Matrix:
    return m.applyfunc(unbool_sym_scalar)


ttm = [
    [0, 1, 1, 1],
    [1, 1, 0, 0],
    [1, 0, 1, 0],
    [1, 0, 0, 1],
]

ttmb = mat_bool(ttm)

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

ttdb = mat_bool(ttd)

inv_ttd = [
    [0, 1, 1, 1],
    [1, 1, 0, 0],
    [1, 0, 1, 0],
    [1, 0, 0, 1],
]

t_maj3 = (1, 1, 1, 0)
t_maj2a = (1, 0, 0, 1)
t_no_maj2b = (0, 1, 0, 1)
t_no_maj1_0 = (1, 0, 0, 0)
t_no_maj1_1 = (0, 1, 0, 0)


def mat_bin_op(
    m_a: list[list[int]],
    m_b: list[list[int]],
    bin_op: Callable[[int, int], int],
    red_op=Callable[[int, int], int],
) -> list[list[int]]:
    return [
        [reduce(red_op, [bin_op(x, y) for (x, y) in zip(r, c)]) for c in zip(*m_b)] for r in m_a
    ]


# def mat_bin_op2(
#     m_a: list[list[int]],
#     m_b: list[list[int]],
#     bin_op: Callable[[int, int], int],
#     red_op=Callable[[int, int], int],
#     ident: int = 0,
# ) -> list[list[int]]:
#     m = len(m_a)
#     n1 = len(m_a[0])
#     n2 = len(m_b)
#     assert n1 == n2
#     n = n1
#     p = len(m_b[0])
#     print(f"m: {m} n: {n} p: {p}")
#     r: list[list[int]] = [[ident] * p for _ in range(m)]

#     for i in range(m):
#         for j in range(p):
#             for k in range(n):
#                 v = r[i][j]
#                 a = m_a[i][k]
#                 b = m_b[k][j]
#                 bv = bin_op(a, b)
#                 rv = red_op(v, bv)
#                 r[i][j] = rv
#     return cast(list[list[int]], r)


# def mat_mul(m_a: list[list[int]], m_b: list[list[int]]) -> list[list[int]]:
#     return mat_bin_op2(m_a, m_b, operator.__mul__, operator.__add__)


# def mat_mul_bin(m_a: list[list[int]], m_b: list[list[int]]) -> list[list[int]]:
#     return mat_bin_op2(m_a, m_b, operator.__and__, operator.__or__)


# def dot_prod_generic(
#     v_a: list[int],
#     v_b: list[int],
#     bin_op: Callable[[int, int], int],
#     red_op=Callable[[int, int], int],
#     ident: int = 0,
# ) -> int:
#     assert len(v_a) == len(v_b)
#     r = ident
#     for i in range(len(v_a)):
#         r = red_op(bin_op(v_a[i], v_b[i]), r)
#     return r


# def dot_prod(v_a: list[int], v_b: list[int]) -> int:
#     return dot_prod_generic(v_a, v_b, operator.__mul__, operator.__add__)


# def dot_prod_bin(v_a: list[int], v_b: list[int]) -> int:
#     return dot_prod_generic(v_a, v_b, operator.__and__, operator.__or__)


# def eval_lut(ibm: tuple[int, int, int, int], f=mat_mul, g=dot_prod) -> None:
#     [a, b, c, d] = ibm
#     print(f"lut: {ibm}")
#     sums = f([list(ibm)], ttm)
#     print(f"sums:\n{sums}")

#     prods = f(sums, ttm)
#     print(f"prods:\n{prods}")

#     sp = g(sums[0], prods[0])
#     print(f"sp:\n{sp}")
#     print()


# eval_lut(t_maj3)
# eval_lut(t_maj2a)
# eval_lut(t_no_maj2b)
# eval_lut(t_no_maj1)

# print("\n\nbin:\n\n")

# eval_lut(t_maj3, mat_mul_bin, dot_prod_bin)
# eval_lut(t_maj2a, mat_mul_bin, dot_prod_bin)
# eval_lut(t_no_maj2b, mat_mul_bin, dot_prod_bin)
# eval_lut(t_no_maj1, mat_mul_bin, dot_prod_bin)

# NumPy


def dot_prod_1d_bit(m_a: list[int], m_b: list[int]) -> int:
    return reduce(operator.__or__, [x & y for x, y in zip(m_a, m_b)])


def eval_lut_np(ibm: tuple[int, int, int, int]) -> None:
    lut = np.array(ibm)
    print(f"lut: {lut}")
    lutm = np.array([list(ibm), list(ibm), list(ibm), list(ibm)])
    print(f"lutm:\n{lutm}")

    prods = np.matmul(lut, ttm)
    print(f"prods:\n{prods}")
    prods_w_dc = prods + ttd
    print(f"prods_w_dc:\n{prods_w_dc}")

    sums = np.add.reduce(prods_w_dc, 1)
    print(f"sums:\n{sums}")
    sum = np.add.reduce(sums)
    print(f"sum: {sum}")

    # sp = np.dot(sums[0], prods[0])
    # print(f"sp:\n{sp}")
    print()


def eval_lut_np_bit(ibm: tuple[int, int, int, int]) -> None:
    print(f"bit lut: {ibm}")
    prods = np.bitwise_and([list(ibm)], ttm)
    print(f"bit prods:\n{prods}")
    prods_w_dc = np.bitwise_or(prods, ttd)
    print(f"prods_w_dc:\n{prods_w_dc}")

    # sums = np.bitwise_or(sums, ttm)
    sums = np.bitwise_and.reduce(prods_w_dc, 1)
    print(f"bit sums:\n{sums}")
    sum = np.bitwise_or.reduce(sums)
    print(f"bit sum: {sum}")
    # prods = dot_prod_1d_bit(prods)
    # print(f"bit prods2:\n{prods2}")

    # sp = dot_prod_1d_bit(sums[0], prods[0])
    # print(f"dot prod:\n{sp}")
    print()


n_maj3 = np.array(t_maj3)
n_maj2a = np.array(t_maj2a)
n_no_maj2b = np.array(t_no_maj2b)
n_no_maj1_0 = np.array(t_no_maj1_0)
n_no_maj1_1 = np.array(t_no_maj1_1)

syms_str = [f"v_{i}_{j}" for i in range(4) for j in range(4)]
print(f"syms_str: {syms_str}")
syms_list = sp.symbols(" ".join(syms_str), integer=True)
print(f"syms_list: {syms_list}")
syms = sp.Matrix(list(chunked(syms_list, 4)))
print(f"syms: {syms}")

isyms_list = sp.symbols("a b c d", integer=True)
print(f"isyms_list: {isyms_list}")
t_isyms = tuple(isyms_list)
print(f"t_isyms: {t_isyms}")
isyms = np.array(t_isyms)
print(f"isyms: {isyms}")

isyms_bit_list = sp.symbols("Ba Bb Bc Bd", integer=True)
print(f"isyms_bit_list: {isyms_bit_list}")
t_isyms_bit = tuple(isyms_bit_list)
print(f"t_isyms_bit: {t_isyms_bit}")
isyms_bit = np.array(t_isyms_bit)
print(f"isyms_bit: {isyms_bit}")

print(f"ttm:\n{np.array(ttm)}")
print()
print(f"ttd:\n{np.array(ttd)}")
print()

eval_lut_np(t_maj3)
eval_lut_np(t_maj2a)
eval_lut_np(t_no_maj2b)
eval_lut_np(t_no_maj1_0)
eval_lut_np(t_no_maj1_1)
eval_lut_np(t_isyms)

print("\n\nbin:\n\n")

eval_lut_np_bit(t_maj3)
eval_lut_np_bit(t_maj2a)
eval_lut_np_bit(t_no_maj2b)
eval_lut_np_bit(t_no_maj1_0)
eval_lut_np_bit(t_no_maj1_1)

s_ttm = sp.Matrix(ttm)
s_ttd = sp.Matrix(ttd)
# s_ttmb = sp.Matrix(ttmb)
# s_ttdb = sp.Matrix(ttdb)

print(f"s_ttm: {s_ttm}")
print(f"s_ttd: {s_ttd}")
# print(f"s_ttmb: {s_ttmb}")
# print(f"s_ttdb: {s_ttdb}")

SPVal = sp.Symbol | sp.Integer


def mat_bin_sym(
    m_a: np.ndarray,
    m_b: np.ndarray,
    prod_op: Callable[[SPVal, SPVal], SPVal],
    sum_op=Callable[[SPVal, SPVal], SPVal],
    ident: SPVal = sp.Integer(0),
) -> np.ndarray:
    m = m_a.shape[0]
    n1 = m_a.shape[1]
    n2 = m_b.shape[0]
    p = m_b.shape[1]
    # m = len(m_a)
    # n1 = len(m_a[0])
    # n2 = len(m_b)
    # assert n1 == n2
    # n = n1
    # p = len(m_b[0])
    assert n1 == n2
    n = n1
    print(f"m: {m} n: {n} p: {p}")
    r = np.array([[ident] * p for _ in range(m)])

    print(f"ty m_a: {type(m_a)} dt: {m_b} ty m_b: {type(m_b)}")
    print(f"m_a: {m_a} m_b: {m_b}")

    for i in range(m):
        for j in range(p):
            for k in range(n):
                v = r[i, j]
                a = m_a[i, k]
                b = m_b[k, j]
                # print(f"a: {a} b: {b}")
                bv = prod_op(a, b)
                rv = sum_op(v, bv)
                rvi = unbool_sym_scalar(rv)
                print(f"rv: {rv} rvi: {rvi} ty: {type(rvi)}")
                r[i, j] = rvi
    # return cast(sp.Matrix, r)
    return r
    # return mat_unbool_sym(r)


def mat_sum_sym(
    m_a: np.ndarray,
    m_b: np.ndarray,
) -> np.ndarray:
    m = m_a.shape[0]
    n1 = m_a.shape[1]
    n2 = m_b.shape[0]
    p = m_b.shape[1]
    assert n1 == n2
    n = n1
    print(f"m: {m} n: {n} p: {p}")
    r = np.array([[sp.Integer(0)] * p for _ in range(m)])

    print(f"ty m_a: {type(m_a)} dt: {m_b} ty m_b: {type(m_b)}")
    print(f"m_a: {m_a} m_b: {m_b}")

    for i in range(m):
        for j in range(p):
            for k in range(n):
                v = r[i, j]
                a = m_a[i, k]
                b = m_b[k, j]
                rv = sp.Or(v, sp.Or(a, b))
                # print(f"shapes: r: {r.shape}")
                rvi = unbool_sym_scalar(rv)
                r[i, j] = rvi
    # return cast(sp.Matrix, r)
    return r


def eval_lut_np_bit_sym(ibm: tuple[sp.Symbol, sp.Symbol, sp.Symbol, sp.Symbol]) -> None:
    print(f"bs ibm: {ibm}")
    lutl = [list(ibm), list(ibm), list(ibm), list(ibm)]
    lut = np.array(lutl)
    print(f"bs lut:\n{lut}")
    # prods = 0
    # prods = lut & s_ttm
    # prods = sp.And(list(ibm), s_ttm)
    # prods = boa.Xor(lut, s_ttmb)
    # prods = lut.applyfunc(operator.__and__, s_ttm)
    prods = mat_bin_sym(lut, s_ttm, sp.And, sp.Or)
    print(f"bs prods:\n{prods}")
    prods_w_dc = mat_sum_sym(prods, s_ttd)
    print(f"bs prods_w_dc:\n{prods_w_dc}")

    sums = np.bitwise_and.reduce(prods_w_dc, 1)
    # sums = np.bitwise_or(prods_w_dc, ttm)
    # sums = reduce(sp.Or, sp.Matrix(prods_w_dc))
    # sums = prods_w_dc[0]
    print(f"bs sums:\n{sums}")
    sum = reduce(operator.__or__, sums)
    print(f"bs sum: {sum}")
    # prods = dot_prod_1d_bit(prods)
    # print(f"bit prods2:\n{prods2}")

    # sp = dot_prod_1d_bit(sums[0], prods[0])
    # print(f"dot prod:\n{sp}")
    print()


eval_lut_np_bit_sym(t_isyms_bit)
