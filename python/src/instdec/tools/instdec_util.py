#!/usr/bin/env python3

import argparse
import json

import rich.traceback
from path import Path
from rich import print

from instdec import arm_json, arm_json_schema
from instdec.arm_json_schema import deserialize_instructions_json

rich.traceback.install()


def dump_instructions(raw_json_dict: dict) -> arm_json.ParseContext:
    instructions = deserialize_instructions_json(raw_json_dict)
    if arm_json.has_instructions_w_children(instructions):
        raise ValueError("have instructions w/ children")
    else:
        print("good, no Instruction.Instruction w/ children")

    # print(instructions)
    ctx = arm_json.dump_info(instructions)
    return ctx


def get_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="instdec-py-util")
    parser.add_argument(
        "-i",
        "--instr-json",
        dest="instr_json",
        type=Path,
        required=True,
        help="Instructions.json path",
    )
    parser.add_argument(
        "-e",
        "--enc-json",
        dest="enc_json",
        type=Path,
        required=False,
        help="Output encoding info path",
    )
    return parser


def real_main(args: argparse.Namespace):
    print(f"args: {args}")
    raw_json_dict = dict(json.load(open(args.instr_json)))

    ctx = dump_instructions(raw_json_dict)
    if args.enc_json is not None:
        with open(args.enc_json, "w") as f:
            f.write(ctx.encoding_info_json)

    print(f"seen_identifiers: {sorted(arm_json_schema.seen_identifiers)}")
    print(f"seen_function_names: {sorted(arm_json_schema.seen_function_names)}")
    print(f"seen_value_meanings: {sorted(arm_json_schema.seen_value_meanings)}")
    print(f"seen_value_values: {sorted(arm_json_schema.seen_value_values)}")


def main():
    parser = get_arg_parser()
    args = parser.parse_args()
    real_main(args)


if __name__ == "__main__":
    main()
