#!/usr/bin/env python3

from rich import print

TT = [
    [1, 0, 2, 2],
    [1, 2, 1, 2],
    [1, 2, 2, 1],
    [2, 1, 1, 1],
]

TT_ON = [[1 if b != 2 else 0 for b in ttr] for ttr in TT]
TT_DC = [[1 if b == 2 else 0 for b in ttr] for ttr in TT]

SZ = len(TT)

vars = []

for i in range(SZ):
    for j in range(SZ):
        print(f"(declare-fun tt_{i}_{j} () Int)")
        print()
        vars.append(f"tt_{i}_{j}")

for i in range(SZ):
    for j in range(SZ):
        print(f"(assert (= tt_{i}_{j} {TT[i][j]}))")
print()

print("(check-sat)")
print()

print("(get-value (" + " ".join(vars) + "))")
print()

print("(exit)")
print()
