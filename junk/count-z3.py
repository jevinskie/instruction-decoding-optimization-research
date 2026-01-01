#!/usr/bin/env python3

from rich import print
from z3 import (
    Z3_OP_BMUL,
    And,
    BitVec,
    BitVecVal,
    BoolRef,
    Implies,
    Not,
    Or,
    Xor,
    ZeroExt,
    is_bv,
    is_bv_value,
    is_expr,
    simplify,
)

# useful non default operator definitions for z3 bools
BoolRef.__and__ = lambda self, other: And(self, other)
BoolRef.__or__ = lambda self, other: Or(self, other)
BoolRef.__xor__ = lambda self, other: Xor(self, other)
BoolRef.__invert__ = lambda self: Not(self)
BoolRef.__rshift__ = lambda self, other: Implies(self, other)  # type: ignore


# LLM slop
def eliminate_bvmul(expr):
    """Recursively eliminate bvmul by expanding into shifts and adds"""
    if not is_expr(expr):
        return expr

    # Recursively process children first
    if expr.num_args() > 0:
        new_args = [eliminate_bvmul(arg) for arg in expr.children()]
        expr = expr.decl()(new_args) if new_args else expr

    # Check if this is a bvmul
    if is_bv(expr) and expr.decl().kind() == Z3_OP_BMUL:
        left, right = expr.children()

        # Try to expand if one operand is a constant
        if is_bv_value(right):
            return expand_mul_by_const(left, right.as_long(), expr.size())
        elif is_bv_value(left):
            return expand_mul_by_const(right, left.as_long(), expr.size())

    return expr


# LLM slop
def expand_mul_by_const(var, const, width):
    """Expand x * const into shifts and additions"""
    if const == 0:
        return BitVecVal(0, width)
    if const == 1:
        return var

    result = BitVecVal(0, width)
    shift = 0

    while const > 0:
        if const & 1:
            result = result + (var << shift)
        const >>= 1
        shift += 1

    return result


iw = 4
w = 32

bvv = BitVec("bvv", iw)
for i in range(iw):
    bvv &= ~BitVecVal(1 << i, iw)
    bvv |= ZeroExt(iw - 1, BitVec(f"v{i}", 1)) << i
print("bvv:")
print(bvv)
bvv_dw = ZeroExt(w - bvv.size(), bvv)

bvm = BitVec("bvm", w)
for i in range(w):
    bvm &= ~BitVecVal(1 << i, w)
    bvm |= ZeroExt(w - 1, BitVec(f"m{i}", 1)) << i
bvm = BitVecVal(0x077C_B531, w)
print("bvm:")
print(bvm)

bvp = bvv_dw * bvm
print("bvp:")
print(bvp)
bvps = simplify(bvp)
print("bvps:")
print(bvps)
bvpsnm = eliminate_bvmul(bvps)
print("bvpsnm:")
print(bvpsnm)
bvpsnms = simplify(bvpsnm)
print("bvpsnms:")
print(bvpsnms)
