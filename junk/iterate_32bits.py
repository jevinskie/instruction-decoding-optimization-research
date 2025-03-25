#!/usr/bin/env python3

import time


def test_func():
    st = time.process_time()

    i = 0
    while i != 2**32:
        i += 1

    et = time.process_time()

    tt = et - st

    print("done")
    print(f"total time: {tt:.04}")

    sec_per_op = tt / 2**32

    print(f"sec_per_op: {sec_per_op}")


test_func()
