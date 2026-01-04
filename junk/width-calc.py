#!/usr/bin/env python3

from sympy import symbols

# 1 - i64x2
# 2 - i32x4
# 3 - i16x8
# 4 - i8x16
log2_n_1_to_4 = symbols("log2_n_1_to_4", positive=True, integer=True)
w_pad = symbols("w_pad", negative=False, integer=True)
w_vbar = 1


# 1: 16
# 2: 8
# 3: 4
# 4: 2
def num_nibbles_per_elem(log2_n):
    # constant 5 - meh not generic
    return 2 ** (5 - log2_n)


def num_elem(log2_n):
    return 2**log2_n


def width_vec(log2_n, w_p):
    w_outer_vbar = 2 * w_vbar
    n_el = num_elem(log2_n)
    n_nibpelm = num_nibbles_per_elem(log2_n)
    n_dnib = n_el * n_nibpelm
    w_dnib = n_dnib + 2 * (n_el * w_p)
    n_inner_vbar = max(n_el - 1, 0)
    w_inner_vbar = n_inner_vbar * w_vbar
    return w_outer_vbar + w_dnib + w_inner_vbar


wv_eqn = width_vec(log2_n_1_to_4, w_pad)
print(wv_eqn)
for i in (1, 2, 3, 4):
    print(f"width(num_elem = {num_elem(i)}) = {width_vec(i, w_pad)}")
