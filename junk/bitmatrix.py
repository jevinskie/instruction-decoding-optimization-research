#!/usr/bin/env python3

from __future__ import annotations

import operator
from collections.abc import Callable
from functools import reduce
from typing import Any, Generic, TypeVar, cast

import numpy as np
import sympy as sp
import sympy.logic.boolalg as boa
from attrs import define

# sp.init_printing(use_unicode=False)
sp.init_printing(use_unicode=True)

from rich import print  # noqa: E402

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


T = TypeVar("T")

UnOp = Callable[[T], T]
BinOp = Callable[[T, T], T]


def py_matmul1(a: np.ndarray, b: np.ndarray):
    ra, ca = a.shape
    rb, cb = b.shape
    assert ca == rb, f"{ca} != {rb}"

    output = np.zeros(shape=(ra, cb))
    for i in range(ra):
        for j in range(cb):
            for k in range(rb):
                output[i, j] += a[i, k] * b[k, j]

    return output


@define(auto_attribs=True, init=False)
class BMat(Generic[T]):
    v: list[list[T]]
    shape: tuple[int, int]

    def __init__(self, mat: list[list[T]]) -> None:
        m = len(mat)
        n = len(mat[0])
        assert all([len(row) == n for row in mat])
        self.shape = m, n
        # self.v = [[mat[i][j] for j in range(n)] for i in range(m)]
        self.v = BMat.normalize_raw(mat)

    @property
    def value(self) -> BMat:
        return BMat(self.v)

    # @property
    # def rows(self) -> Generator[list[T]]:
    #     yield from self.v

    @staticmethod
    def normalize_scalar(val: T) -> T:
        r: Any = None
        if isinstance(val, bool):
            r = int(val)
        elif isinstance(val, boa.BooleanFalse):
            r = 0
        elif isinstance(val, boa.BooleanTrue):
            r = 1
        else:
            r = val
        assert r is not None
        return cast(T, r)

    @staticmethod
    def normalize_raw(mat: list[list[T]]) -> list[list[T]]:
        m = len(mat)
        n = len(mat[0])
        assert all([len(row) == n for row in mat])
        print(f"NR: m: {m} n: {n} mat: {mat}")
        r = cast(list[list[T]], [[None] * n for _ in range(m)])
        for i in range(m):
            for j in range(n):
                v = mat[i][j]
                nv = BMat.normalize_scalar(v)
                r[i][j] = nv
        return r

    def normalize(self) -> None:
        self.v = BMat.normalize_raw(self.v)

    @property
    def rows(self) -> list[list[T]]:
        return [[v for v in row] for row in self.v]

    def matmul(
        self,
        other: BMat[T],
        prod_op: BinOp = operator.mul,
        sum_op: BinOp = operator.add,
        ident: T = 0,
    ) -> BMat[T]:
        m = self.shape[0]
        n1 = self.shape[1]
        n2 = other.shape[0]
        assert n1 == n2
        n = n1
        p = other.shape[1]
        r = cast(list[list[T]], [[ident] * p for _ in range(m)])

        for i in range(n):
            for j in range(p):
                for k in range(m):
                    v = r[i][j]
                    a = self[i, k]
                    b = other[k, j]
                    bv = BMat.normalize_scalar(prod_op(a, b))
                    print(f"mm prod_op({a}, {b}) => {bv}")
                    rv = BMat.normalize_scalar(sum_op(v, bv))
                    print(f"mm sum_op({v}, {bv}) => {rv}")
                    r[i][j] = rv
        return BMat(r)

    def mat_bin_op(self, other: BMat[T], bin_op: BinOp) -> BMat[T]:
        m = self.shape[0]
        n1 = self.shape[1]
        n2 = other.shape[0]
        assert n1 == n2
        n = n1
        p = other.shape[1]
        r = cast(list[list[T]], [[None] * p for _ in range(m)])

        for i in range(n):
            for j in range(p):
                for k in range(m):
                    a = self[i, k]
                    b = other[k, j]
                    bv = BMat.normalize_scalar(bin_op(a, b))
                    print(f"bo bin_op({a}, {b}) => {bv}")
                    r[i][j] = bv
        return BMat(r)

    def matadd(self, other: BMat[T]) -> BMat[T]:
        return self.mat_bin_op(other, operator.add)

    def mat_un_op(self, un_op: UnOp) -> BMat[T]:
        m = self.shape[0]
        n = self.shape[1]
        r = cast(list[list[T]], [[None] * n for _ in range(m)])

        for i in range(n):
            for j in range(m):
                v = self[i, j]
                uv = BMat.normalize_scalar(un_op(v))
                print(f"un un_op({v}) => {uv}")
                r[i][j] = uv
        return BMat(r)

    def __getitem__(self, idx: int | tuple[int, int] | slice) -> T | list[T]:
        if isinstance(idx, slice):
            raise NotImplementedError("slice getitem")
        elif isinstance(idx, tuple):
            assert len(idx) == 2
            i, j = idx
            return self.v[i][j]
        else:
            return self.v[idx]

    def __setitem__(self, idx: int | tuple[int, int] | slice, value: T | list[T]) -> None:
        print(f"idx: {idx}")
        if isinstance(idx, slice):
            raise NotImplementedError("slice setitem")
        elif isinstance(idx, tuple):
            assert not isinstance(value, list)
            assert len(idx) == 2
            i, j = idx
            self.v[i][j] = BMat.normalize_scalar(value)
        else:
            assert isinstance(value, list)
            self.v[idx] = [BMat.normalize_scalar(v) for v in value]

    def __matmul__(self, other: BMat[T]):
        return self.matmul(other)


_ttmb = BMat(ttm)
print(f"_ttmb:\n{_ttmb}")

_ttmb2 = _ttmb @ _ttmb
print(f"ttmb2:\n{_ttmb2}")

ttmb = BMat(ttm)
ttdb = BMat(ttd)

t_maj3 = (1, 1, 1, 0)
t_maj2a = (1, 0, 0, 1)
t_no_maj2b = (0, 1, 0, 1)
t_no_maj1_0 = (1, 0, 0, 0)
t_no_maj1_1 = (0, 1, 0, 0)


# def mat_bin_op(
#     m_a: list[list[int]],
#     m_b: list[list[int]],
#     bin_op: Callable[[int, int], int],
#     red_op=Callable[[int, int], int],
# ) -> list[list[int]]:
#     return [
#         [reduce(red_op, [bin_op(x, y) for (x, y) in zip(r, c)]) for c in zip(*m_b)] for r in m_a
#     ]


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


# def dot_prod_1d_bit(m_a: list[int], m_b: list[int]) -> int:
#     return reduce(operator.__or__, [x & y for x, y in zip(m_a, m_b)])


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


# n_maj3 = np.array(t_maj3)
# n_maj2a = np.array(t_maj2a)
# n_no_maj2b = np.array(t_no_maj2b)
# n_no_maj1_0 = np.array(t_no_maj1_0)
# n_no_maj1_1 = np.array(t_no_maj1_1)

# syms_str = [f"v_{i}_{j}" for i in range(4) for j in range(4)]
# print(f"syms_str: {syms_str}")
# syms_list = sp.symbols(" ".join(syms_str), integer=True)
# print(f"syms_list: {syms_list}")
# syms = sp.Matrix(list(chunked(syms_list, 4)))
# print(f"syms: {syms}")

# isyms_list = sp.symbols("a b c d", integer=True)
# print(f"isyms_list: {isyms_list}")
# t_isyms = tuple(isyms_list)
# print(f"t_isyms: {t_isyms}")
# isyms = np.array(t_isyms)
# print(f"isyms: {isyms}")

isyms_bit_list = sp.symbols("Ba Bb Bc Bd", integer=True)
print(f"isyms_bit_list: {isyms_bit_list}")
t_isyms_bit = tuple(isyms_bit_list)
print(f"t_isyms_bit: {t_isyms_bit}")
isyms_bit = np.array(t_isyms_bit)
print(f"isyms_bit: {isyms_bit}")

print(f"ttm:\n{ttm}")
print()
print(f"ttd:\n{ttd}")
print()
print(f"ttmb:\n{ttmb}")
print()
print(f"ttdb:\n{ttdb}")
print()

# eval_lut_np(t_maj3)
# eval_lut_np(t_maj2a)
# eval_lut_np(t_no_maj2b)
# eval_lut_np(t_no_maj1_0)
# eval_lut_np(t_no_maj1_1)
# eval_lut_np(t_isyms)

# print("\n\nbin:\n\n")

# eval_lut_np_bit(t_maj3)
# eval_lut_np_bit(t_maj2a)
# eval_lut_np_bit(t_no_maj2b)
# eval_lut_np_bit(t_no_maj1_0)
# eval_lut_np_bit(t_no_maj1_1)

# s_ttm = sp.Matrix(ttm)
# s_ttd = sp.Matrix(ttd)
# s_ttmb = sp.Matrix(ttmb)
# s_ttdb = sp.Matrix(ttdb)

# print(f"s_ttm: {s_ttm}")
# print(f"s_ttd: {s_ttd}")
# print(f"s_ttmb: {s_ttmb}")
# print(f"s_ttdb: {s_ttdb}")

# SPVal = sp.Symbol | sp.Integer


# def mat_bin_sym(
#     m_a: np.ndarray,
#     m_b: np.ndarray,
#     prod_op: Callable[[SPVal, SPVal], SPVal],
#     sum_op=Callable[[SPVal, SPVal], SPVal],
#     ident: SPVal = sp.Integer(0),
# ) -> np.ndarray:
#     m = m_a.shape[0]
#     n1 = m_a.shape[1]
#     n2 = m_b.shape[0]
#     p = m_b.shape[1]
#     # m = len(m_a)
#     # n1 = len(m_a[0])
#     # n2 = len(m_b)
#     # assert n1 == n2
#     # n = n1
#     # p = len(m_b[0])
#     assert n1 == n2
#     n = n1
#     print(f"m: {m} n: {n} p: {p}")
#     r = np.array([[ident] * p for _ in range(m)])

#     print(f"ty m_a: {type(m_a)} dt: {m_b} ty m_b: {type(m_b)}")
#     print(f"m_a: {m_a} m_b: {m_b}")

#     for i in range(m):
#         for j in range(p):
#             for k in range(n):
#                 v = r[i, j]
#                 a = m_a[i, k]
#                 b = m_b[k, j]
#                 # print(f"a: {a} b: {b}")
#                 bv = prod_op(a, b)
#                 rv = sum_op(v, bv)
#                 rvi = unbool_sym_scalar(rv)
#                 print(f"rv: {rv} rvi: {rvi} ty: {type(rvi)}")
#                 r[i, j] = rvi
#     # return cast(sp.Matrix, r)
#     return r
#     # return mat_unbool_sym(r)


# def mat_sum_sym(
#     m_a: np.ndarray,
#     m_b: np.ndarray,
# ) -> np.ndarray:
#     m = m_a.shape[0]
#     n1 = m_a.shape[1]
#     n2 = m_b.shape[0]
#     p = m_b.shape[1]
#     assert n1 == n2
#     n = n1
#     print(f"m: {m} n: {n} p: {p}")
#     r = np.array([[sp.Integer(0)] * p for _ in range(m)])

#     print(f"ty m_a: {type(m_a)} dt: {m_b} ty m_b: {type(m_b)}")
#     print(f"m_a: {m_a} m_b: {m_b}")

#     for i in range(m):
#         for j in range(p):
#             for k in range(n):
#                 v = r[i, j]
#                 a = m_a[i, k]
#                 b = m_b[k, j]
#                 rv = sp.Or(v, sp.Or(a, b))
#                 # print(f"shapes: r: {r.shape}")
#                 rvi = unbool_sym_scalar(rv)
#                 r[i, j] = rvi
#     # return cast(sp.Matrix, r)
#     return r


def eval_lut_np_bit_sym(ibm: tuple[sp.Symbol, sp.Symbol, sp.Symbol, sp.Symbol]) -> None:
    print(f"bs ibm: {ibm}")
    lutl = [list(ibm), list(ibm), list(ibm), list(ibm)]
    lut = BMat(lutl)
    print(f"bs lut:\n{lut}")
    print(f"bs ttmb:\n{ttmb}")
    prods = lut.matmul(ttmb, sp.And, sp.Or)
    print(f"bs prods:\n{prods}")
    prods_w_dc = prods.mat_bin_op(ttdb, sp.Or)
    print(f"bs prods_w_dc:\n{prods_w_dc}")

    reduce_prods_raw = [[reduce(sp.And, row) for row in prods_w_dc.rows]]
    print(f"bs reduce_prods_raw: {reduce_prods_raw}")
    reduce_prods = BMat.normalize_raw(reduce_prods_raw)
    print(f"bs reduce_prods:\n{reduce_prods}")
    sum = reduce(sp.Or, reduce_prods[0])
    print(f"bs sum: {sum}")
    print()


eval_lut_np_bit_sym(t_isyms_bit)
