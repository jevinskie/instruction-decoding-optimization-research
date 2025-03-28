#!/usr/bin/env python3

import argparse
import json
import operator
from functools import reduce

import rich.traceback

# from rich import print
import z3
from path import Path

rich.traceback.install()


def subterms(t):
    seen = {}

    def subterms_rec(t):
        if z3.is_app(t):
            for ch in t.children():
                if ch in seen:
                    continue
                seen[ch] = True
                yield ch
                yield from subterms_rec(ch)

    return {s for s in subterms_rec(t)}


def are_equal(s, t1, t2):
    s.push()
    s.add(t1 != t2)
    r = s.check()
    s.pop()
    return r == z3.unsat


def simplify(slv, mdl, t):
    subs = subterms(t)
    values = {s: mdl.eval(s) for s in subs}
    values[t] = mdl.eval(t)

    def simplify_rec(t):
        subs = subterms(t)
        for s in subs:
            if s.sort().eq(t.sort()) and values[s].eq(values[t]) and are_equal(slv, s, t):
                return simplify_rec(s)
        chs = [simplify_rec(ch) for ch in t.children()]
        return t.decl()(chs)

    return simplify_rec(t)


def check_encoding(einf: dict[str, tuple[int, int]]) -> None:
    slv = z3.Solver()
    slv
    ival = z3.BitVec("i", 32)
    vvals: dict[str, z3.BoolRef] = {}
    for iname, binf in einf.items():
        bm = z3.BitVecVal(binf[0], 32)
        bp = z3.BitVecVal(binf[1], 32)
        valid = (ival & bm) == bp
        if valid is False:
            valid = z3.BoolVal(False)
        vvals[iname] = valid
    undef = ~reduce(operator.or_, vvals.values())
    # print(vvals)
    print(undef)
    ud2 = z3.simplify(undef)
    print(ud2)
    ud3 = simplify(ud2)
    print(ud3)
    ud4 = z3.simplify(ud3)
    print(ud4)


def get_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="instdec-py-util")
    parser.add_argument(
        "-e",
        "--enc-json",
        dest="enc_json",
        type=Path,
        required=True,
        help="Prebased encoding bitmask/bitpattern JSON path",
    )
    return parser


def real_main(args: argparse.Namespace):
    raw_json_dict = dict(json.load(open(args.enc_json)))

    enc_info: dict[str, tuple[int, int]] = {}
    for iname, einfo_str in raw_json_dict.items():
        enc_info[iname] = (int(einfo_str[0], 2), int(einfo_str[1], 2))

    # print(enc_info)
    check_encoding(enc_info)


def main():
    parser = get_arg_parser()
    args = parser.parse_args()
    real_main(args)


if __name__ == "__main__":
    main()
