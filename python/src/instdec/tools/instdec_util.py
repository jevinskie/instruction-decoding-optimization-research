#!/usr/bin/env python3

import argparse
import sys

import simplejson as json
from rich import print

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
    instructions = arm_json.find_leafs(j)

    for inst in instructions:
        name, mtrits, n0, n1, nX = arm_json.parse_instruction_encoding(inst)
        print(f"inst: {name:32} mtrits: {mtrits} #0: {n0:2} #1: {n1:2} #X: {nX:2}")
        if name == "stnt1w_z_p_br_contiguous":
            print(f"stnt1w_z_p_br_contiguous:\n{inst}")
            sys.exit(0)

    json.dump(instructions, open("inst-enc.json", "w"))


def main():
    parser = get_arg_parser()
    args = parser.parse_args()
    real_main(args)


if __name__ == "__main__":
    main()
