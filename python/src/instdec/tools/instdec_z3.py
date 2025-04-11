#!/usr/bin/env python3

import argparse
import json
import operator
from functools import reduce

import rich.traceback
import z3
from path import Path
from rich import print

from instdec.espresso import generate_espresso, parse_espresso
from instdec.logic import generate_dnf
from instdec.search import generate_search_tree
from instdec.verilog import generate_verilog

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
    ival = z3.BitVec("i", 32)
    vvals: dict[str, z3.BoolRef] = {}
    for iname, binf in einf.items():
        bm = z3.BitVecVal(binf[0], 32)
        bp = z3.BitVecVal(binf[1], 32)
        valid = (ival & bm) == bp
        if valid is False:
            valid = z3.BoolVal(False)
        vvals[iname] = valid
    inst_is_defined = reduce(operator.or_, vvals.values())
    inst_is_undef = ~inst_is_defined
    slv.check(inst_is_undef)
    model = slv.model()
    print(model)
    print("endmodel\n\n!!!!!!!!!!!\n\n\n")
    # print(vvals)
    print(inst_is_undef)
    id2 = z3.simplify(inst_is_defined)
    print(id2)
    # id3 = id2
    id3 = simplify(id2, model, [])
    # print(id3)
    id4 = z3.simplify(id3)
    print(id4)


def get_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="instdec-py-z3")
    in_group = parser.add_mutually_exclusive_group(required=True)
    in_group.add_argument(
        "-i",
        "--enc-json",
        dest="enc_json",
        type=Path,
        required=False,
        help="Prebased encoding bitmask/bitpattern JSON path",
    )
    in_group.add_argument(
        "-E",
        "--espresso-in",
        dest="espresso_in",
        type=Path,
        required=False,
        help="Input Espresso file",
    )
    parser.add_argument(
        "-e",
        "--espresso-out",
        dest="espresso_out",
        type=Path,
        required=False,
        help="Output file for Espresso optimization",
    )
    parser.add_argument(
        "-v",
        "--verilog",
        dest="verilog",
        type=Path,
        required=False,
        help="Output Verilog path",
    )
    parser.add_argument("-p", "--print", action="store_true", help="Print encoding")
    parser.add_argument("-c", "--check", action="store_true", help="Check encoding?")
    parser.add_argument("-s", "--cpsat", action="store_true", help="CP SAT")
    parser.add_argument("-S", "--search", action="store_true", help="Search tree")
    parser.add_argument("--dnf", action="store_true", help="Disjuntive normal form")
    return parser


def real_main(args: argparse.Namespace) -> None:
    enc_info: dict[str, tuple[int, int]] = {}

    if args.enc_json is not None:
        raw_json_dict = dict(json.load(open(args.enc_json)))
        for iname, einfo_str in raw_json_dict.items():
            enc_info[iname] = (int(einfo_str[0], 2), int(einfo_str[1], 2))
    elif args.espresso_in is not None:
        enc_info = parse_espresso(open(args.espresso_in).read())
    else:
        raise ValueError("need input json or espresso")

    if args.print:
        print(enc_info)
    if args.check:
        check_encoding(enc_info)
    if args.cpsat:
        from instdec.cpsat import cpsat_check_encoding

        cpsat_check_encoding(enc_info)
    if args.search:
        generate_search_tree(enc_info)
    if args.dnf:
        generate_dnf(enc_info)

    if args.verilog is not None:
        vl = generate_verilog(enc_info)
        with open(args.verilog, "w") as f:
            f.write(vl)

    if args.espresso_out is not None:
        espr = generate_espresso(enc_info)
        with open(args.espresso_out, "w") as f:
            f.write(espr)


def main():
    parser = get_arg_parser()
    args = parser.parse_args()
    real_main(args)


if __name__ == "__main__":
    main()
