#!/usr/bin/env python3

# from rich import print
from z3 import (
    And,
    BitVec,
    BitVecVal,
    BoolRef,
    Implies,
    Not,
    Or,
    Xor,
    ZeroExt,
    simplify,
)

# useful non default operator definitions for z3 bools
BoolRef.__and__ = lambda self, other: And(self, other)
BoolRef.__or__ = lambda self, other: Or(self, other)
BoolRef.__xor__ = lambda self, other: Xor(self, other)
BoolRef.__invert__ = lambda self: Not(self)
BoolRef.__rshift__ = lambda self, other: Implies(self, other)  # type: ignore

nt_127 = BitVecVal(127, 8)
print(nt_127)
v = BitVec("v", 8)
v16 = ZeroExt(8, v)
m = BitVec("m", 16)

p = v16 * m
print(p)
ps = simplify(p)
print(ps)

bvv = BitVec("bvv", 8)
for i in range(8):
    bvv &= ~BitVecVal(1 << i, 8)
    bvv |= ZeroExt(7, BitVec(f"v{i}", 1)) << i
print("bvv:")
print(bvv)
bvv16 = ZeroExt(8, bvv)

bvm = BitVec("bvm", 16)
for i in range(16):
    bvm &= ~BitVecVal(1 << i, 16)
    bvm |= ZeroExt(15, BitVec(f"m{i}", 1)) << i
print("bvm:")
print(bvm)

bvp = bvv16 * bvm
print("bvp:")
print(bvp)
bvps = simplify(bvp)
print("bvps:")
print(bvps)
