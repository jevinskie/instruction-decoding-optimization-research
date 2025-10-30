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
# sp.init_printing(use_unicode=True)
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

t_maj3 = (1, 1, 1, 0)
t_maj2a = (1, 0, 0, 1)
t_no_maj2b = (0, 1, 0, 1)
t_no_maj1_0 = (1, 0, 0, 0)
t_no_maj1_1 = (0, 1, 0, 0)


T = TypeVar("T")

UnOp = Callable[[T], T]
BinOp = Callable[[T, T], T]


@define(auto_attribs=True, init=False)
class BMat(Generic[T]):
    v: list[list[T]]
    shape: tuple[int, int]

    def __init__(self, mat: list[list[T]]) -> None:
        m = len(mat)
        n = len(mat[0])
        assert all([len(row) == n for row in mat])
        self.shape = m, n
        self.v = BMat.normalize_raw(mat)

    @property
    def value(self) -> BMat:
        return BMat(self.v)

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
        # print(f"NR: m: {m} n: {n} mat: {mat}")
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
                    # print(f"mm prod_op({a}, {b}) => {bv}")
                    rv = BMat.normalize_scalar(sum_op(v, bv))
                    # print(f"mm sum_op({v}, {bv}) => {rv}")
                    r[i][j] = rv
        return BMat(r)

    def mat_bin_op(self, other: BMat[T], bin_op: BinOp) -> BMat[T]:
        m, n = self.shape
        assert self.shape == other.shape
        r = cast(list[list[T]], [[None] * n for _ in range(m)])

        for i in range(n):
            for j in range(m):
                a = self[i, j]
                b = other[i, j]
                bv = BMat.normalize_scalar(bin_op(a, b))
                # print(f"bo bin_op({a}, {b}) => {bv}")
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
                # print(f"un un_op({v}) => {uv}")
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


ttmb = BMat(ttm)
ttdb = BMat(ttd)

print(f"ttm:\n{ttm}")
print()
print(f"ttd:\n{ttd}")
print()
print(f"ttmb:\n{ttmb}")
print()
print(f"ttdb:\n{ttdb}")
print()

isyms_bit_list = sp.symbols("Ba Bb Bc Bd", integer=True)
print(f"isyms_bit_list: {isyms_bit_list}")
t_isyms_bit = tuple(isyms_bit_list)
print(f"t_isyms_bit: {t_isyms_bit}")
isyms_bit = np.array(t_isyms_bit)
print(f"isyms_bit: {isyms_bit}")


def eval_lut_np(ibm: tuple[int, int, int, int]) -> None:
    lut = np.array(ibm)
    print(f"lut: {lut}")
    lutm = np.array([list(ibm), list(ibm), list(ibm), list(ibm)])
    print(f"lutm:\n{lutm}")

    prods = np.matmul(lutm, ttm)
    print(f"prods:\n{prods}")
    prods_w_dc = prods + ttd
    print(f"prods_w_dc:\n{prods_w_dc}")

    sums = np.add.reduce(prods_w_dc, 1)
    print(f"sums:\n{sums}")
    sum = np.add.reduce(sums)
    print(f"sum: {sum}")
    print()


def eval_lut_np_bit(ibm: tuple[int, int, int, int]) -> None:
    print(f"bit lut: {ibm}")
    prods = np.bitwise_and([list(ibm)], ttm)
    print(f"bit prods:\n{prods}")
    prods_w_dc = np.bitwise_or(prods, ttd)
    print(f"prods_w_dc:\n{prods_w_dc}")

    sums = np.bitwise_and.reduce(prods_w_dc, 1)
    print(f"bit sums:\n{sums}")
    sum = np.bitwise_or.reduce(sums)
    print(f"bit sum: {sum}")
    print()


eval_lut_np(t_isyms_bit)


def eval_lut_np_bit_sym(ibm: tuple[T, T, T, T]) -> None:
    print(f"bs ibm: {ibm}")
    lutl = [list(ibm), list(ibm), list(ibm), list(ibm)]
    lut = BMat(lutl)
    print(f"bs lut:\n{lut}")
    print(f"bs ttmb:\n{ttmb}")
    # prods = lut.matmul(ttmb, sp.And, sp.Or)
    prods = lut.mat_bin_op(ttmb, sp.And)
    print(f"bs prods:\n{prods}")
    prods_w_dc = prods.mat_bin_op(ttdb, sp.Or)
    print(f"bs prods_w_dc:\n{prods_w_dc}")

    reduce_prods_raw = [[reduce(sp.And, row) for row in prods_w_dc.rows]]
    print(f"bs reduce_prods_raw: {reduce_prods_raw}")
    reduce_prods = BMat.normalize_raw(reduce_prods_raw)
    print(f"bs reduce_prods:\n{reduce_prods}")
    sum_raw = reduce(sp.Or, reduce_prods[0])
    sum_norm = BMat.normalize_scalar(sum_raw)
    print(f"bs sum: {sum_norm} sum_raw: {sum_raw}")
    print()


eval_lut_np_bit_sym(t_isyms_bit)


def eval_lut_np_bit_sym_npnpnp(ibm: tuple[T, T, T, T]) -> None:
    print(f"ns ibm: {ibm}")
    lutl = [list(ibm), list(ibm), list(ibm), list(ibm)]
    lut = BMat(lutl)
    print(f"ns lut:\n{lut}")
    print(f"ns ttmb:\n{ttmb}")
    # prods = lut.matmul(ttmb, sp.And, sp.Or)
    prods = lut.mat_bin_op(ttmb, operator.mul)
    print(f"ns prods:\n{prods}")
    prods_w_dc = prods.mat_bin_op(ttdb, operator.add)
    print(f"ns prods_w_dc:\n{prods_w_dc}")

    reduce_prods_raw = [[reduce(operator.mul, row) for row in prods_w_dc.rows]]
    print(f"ns reduce_prods_raw: {reduce_prods_raw}")
    reduce_prods = BMat.normalize_raw(reduce_prods_raw)
    print(f"ns reduce_prods:\n{reduce_prods}")
    sum_raw = reduce(operator.add, reduce_prods[0])
    sum_norm = BMat.normalize_scalar(sum_raw)
    print(f"ns sum: {sum_norm} sum_raw: {sum_raw}")
    print()


eval_lut_np_bit_sym(t_isyms_bit)
eval_lut_np_bit_sym(t_maj3)

eval_lut_np_bit_sym_npnpnp(t_isyms_bit)
eval_lut_np_bit_sym_npnpnp(t_maj3)
