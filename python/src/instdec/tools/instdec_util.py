#!/usr/bin/env python3

import argparse

import simplejson as json
from rich import print

from instdec import arm_json
from instdec.trits import TritRange, TritRanges, Trits

Trits
TritRange
TritRanges


def get_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="instdec-py-util")
    parser.add_argument(
        "-i", "--instr-json", dest="instr_json", required=True, help="Instructions.json path"
    )
    return parser


def real_main(args: argparse.Namespace):
    print(f"args: {args}")
    j = dict(json.load(open(args.instr_json)))
    # r = arm_json.find_encodings(j)
    r = arm_json.find_leafs(j)
    for inst in r:
        enc = inst["encoding"]
        if "width" in enc and enc["width"] != 32:
            raise ValueError(f"inst enc width isn't 32 it is {enc['width']}")
        assert enc["_type"] == "Instruction.Encodeset.Encodeset"
        nbits = 0
        trit_ranges = TritRanges()
        for v in enc["values"]:
            assert v["_type"] in ("Instruction.Encodeset.Bits", "Instruction.Encodeset.Field")
            rng = v["range"]
            assert rng["_type"] == "Range"
            sbm = v["should_be_mask"]
            assert sbm["_type"] == "Values.Value"
            val = v["value"]
            assert val["_type"] == "Values.Value"
            start = rng["start"]
            width = rng["width"]
            end = start + width
            assert 0 <= start <= 31
            assert 1 <= end <= 32
            assert width > 0
            nbits += width
            valval = val["value"].replace("'", "")
            sbmt = TritRange(start, width, valval)
            trit_ranges.add_range(sbmt)

        # assert nbits == 32
        if nbits != 32:
            pass
            # raise ValueError(f"got nbits {nbits} - inst:\n{pretty.pretty_repr(inst)}")

        mtrits = trit_ranges.merge()
        mts = str(mtrits)
        n0 = mts.count("0")
        n1 = mts.count("1")
        nX = mts.count("X")
        print(f"inst: {inst['name']:32} mtrits: {mtrits} #0: {n0:2} #1: {n1:2} #X: {nX:2}")

    json.dump(r, open("inst-enc.json", "w"))
    # print(r)


def main():
    parser = get_arg_parser()
    args = parser.parse_args()
    real_main(args)


if __name__ == "__main__":
    main()
