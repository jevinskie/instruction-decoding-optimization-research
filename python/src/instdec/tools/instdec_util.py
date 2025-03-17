#!/usr/bin/env python3

import argparse

import jsonyx as json
from rich import pretty, print

from instdec import arm_json


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

        # assert nbits == 32
        if nbits != 32:
            raise ValueError(f"got nbits {nbits} - inst:\n{pretty.pretty_repr(inst)}")

    json.dump(r, open("inst-enc.json", "w"))
    # print(r)


def main():
    parser = get_arg_parser()
    args = parser.parse_args()
    real_main(args)


if __name__ == "__main__":
    main()
