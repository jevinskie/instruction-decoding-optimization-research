#!/usr/bin/env python3

import argparse

import jsonyx as json
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
    r = arm_json.find_encodings(j)
    print(r)


def main():
    parser = get_arg_parser()
    args = parser.parse_args()
    real_main(args)


if __name__ == "__main__":
    main()
