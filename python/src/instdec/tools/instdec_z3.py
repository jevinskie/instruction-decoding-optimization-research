#!/usr/bin/env python3

import argparse
import json
import operator
from functools import reduce

import rich.traceback
import z3
from path import Path
from rich import print

from instdec.util import StringList

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
    ud3 = ud2
    # ud3 = simplify(ud2)
    print(ud3)
    ud4 = z3.simplify(ud3)
    print(ud4)


def generate_verilog(einf: dict[str, tuple[int, int]]) -> str:
    # TODO: Generate "number of valid decodes"
    vl = StringList()
    vl @= "module a64dec(input [31:0]i, output v);"
    vl @= f"    wire [{len(einf) - 1}:0]vtmp;"
    for i, kv in enumerate(einf.items()):
        vl @= (
            f"    assign vtmp[{i:4}] = (i & 32'b{kv[1][0]:032b}) == 32'b{kv[1][1]:032b}; // {kv[0]}"
        )
    vl @= "    assign v = |vtmp;"
    vl @= "endmodule"
    vl @= ""
    return str(vl)


def generate_espresso(einf: dict[str, tuple[int, int]]) -> str:
    el = StringList()
    el @= ".i 32"
    el @= ".o 1"
    el @= ".ilb " + " ".join([f"I{i}" for i in reversed(range(32))])
    el @= ".olb V"
    for i, kv in enumerate(einf.items()):
        bmi = kv[1][0]
        bpi = kv[1][1]
        bits = ""
        for j in reversed(range(32)):
            sb = 1 << j
            if bmi & sb:
                if bpi & sb:
                    bits += "1"
                else:
                    bits += "0"
            else:
                bits += "-"
        bits += " 1"
        el @= bits
    el @= ".e"
    el @= ""
    return str(el)


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
    return parser


def real_main(args: argparse.Namespace) -> None:
    enc_info: dict[str, tuple[int, int]] = {}

    if args.enc_json is not None:
        raw_json_dict = dict(json.load(open(args.enc_json)))
        for iname, einfo_str in raw_json_dict.items():
            enc_info[iname] = (int(einfo_str[0], 2), int(einfo_str[1], 2))
        # print(enc_info)
        # check_encoding(enc_info)
    elif args.espresso_in is not None:
        elines = open(args.espresso_in).readlines()
        elines = list(filter(lambda s: s and not s.startswith("."), elines))
        for i, el in enumerate(elines):
            bs, vs = el.split()
            if vs != "1":
                raise ValueError(f"vs not '1' got '{vs}'")
            bmi = int(bs.replace("1", "N").replace("0", "N").replace("-", "0").replace("N", "1"), 2)
            bpi = int(bs.replace("-", "0"), 2)
            enc_info[f"esp_{i}"] = (bmi, bpi)
    else:
        raise ValueError("need input json or espresso")

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
