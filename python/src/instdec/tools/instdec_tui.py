from __future__ import annotations

import argparse
import json
from typing import TYPE_CHECKING

from path import Path

from instdec import arm_json, arm_json_schema
from instdec.arm_json_schema import deserialize_instructions_json

if not TYPE_CHECKING:
    from rich import print


def dump_instructions(raw_json_dict: dict) -> arm_json.ParseContext:
    instructions = deserialize_instructions_json(raw_json_dict)
    if arm_json.has_instructions_w_children(instructions):
        raise ValueError("have instructions w/ children")
    else:
        print("good, no Instruction.Instruction w/ children")

    # print(instructions)
    ctx = arm_json.dump_info(instructions)
    return ctx


def real_main(args: argparse.Namespace):
    raw_json_dict = dict(json.load(open(args.instr_json)))
    raw_json_dict["instructions"] = [i for i in raw_json_dict["instructions"] if i["name"] == "A64"]
    ctx = dump_instructions(raw_json_dict)
    if not args.dump:
        # app = InstrExploreApp(git_repo_path=args.repo)
        # app.run()
        pass
    else:
        print(ctx)
        print(f"seen_identifiers: {sorted(arm_json_schema.seen_identifiers)}")
        print(f"seen_function_names: {sorted(arm_json_schema.seen_function_names)}")
        print(f"seen_value_meanings: {sorted(arm_json_schema.seen_value_meanings)}")
        print(f"seen_value_values: {sorted(arm_json_schema.seen_value_values)}")


def get_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="instdec-py-tui")
    parser.add_argument(
        "-i",
        "--instr-json",
        dest="instr_json",
        type=Path,
        required=True,
        help="Instructions.json path",
    )
    parser.add_argument("-d", "--dump", action="store_true", help="Dump Instructions.json raw info")
    return parser


def main():
    real_main(get_arg_parser().parse_args())


if __name__ == "__main__":
    main()
