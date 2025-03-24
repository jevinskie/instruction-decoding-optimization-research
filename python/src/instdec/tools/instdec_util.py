#!/usr/bin/env python3

import argparse

import simplejson as json
from rich import print

# import rich
from instdec import arm_json, arm_json_schema
from instdec.arm_json_schema import Instructions, JSONSchemaObject


def dump_instructions(raw_json_dict: dict) -> None:
    instructions: JSONSchemaObject = arm_json_schema.converter.structure(
        raw_json_dict, JSONSchemaObject
    )
    if instructions is None:
        raise ValueError("got None instructions")
    if not isinstance(instructions, Instructions):
        raise TypeError("didn't deserialize an Instructions object")
    if arm_json.has_instructions_w_children(instructions):
        raise ValueError("have instructions with children")
    else:
        print("good, no Instruction.Instruction w/ children")

    arm_json.dump_idents(instructions)


def get_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="instdec-py-util")
    parser.add_argument(
        "-i", "--instr-json", dest="instr_json", required=True, help="Instructions.json path"
    )
    return parser


def real_main(args: argparse.Namespace):
    print(f"args: {args}")
    raw_json_dict = dict(json.load(open(args.instr_json)))

    dump_instructions(raw_json_dict)

    print(f"seen_identifiers: {arm_json_schema.seen_identifiers}")
    print(f"seen_function_names: {arm_json_schema.seen_function_names}")
    print(f"seen_value_meanings: {arm_json_schema.seen_value_meanings}")
    print(f"seen_value_values: {arm_json_schema.seen_value_values}")


def main():
    parser = get_arg_parser()
    args = parser.parse_args()
    real_main(args)


if __name__ == "__main__":
    main()
