#!/usr/bin/env python3

import argparse

import simplejson as json
from rich import print

# import rich
from instdec import arm_json


def dump_instructions_old(raw_json: dict | list) -> None:
    instructions = arm_json.find_leafs(raw_json)
    for inst in instructions:
        name, mtrits, n0, n1, nX = arm_json.parse_instruction_encoding(inst)
        print(f"inst: {name:32} mtrits: {mtrits} #0: {n0:2} #1: {n1:2} #X: {nX:2}")
        inst_dec = arm_json.converter.structure(inst, arm_json.JSONSchemaObject)
        print(f"inst_dec: {inst_dec}")
        cond = inst_dec.condition
        interp = arm_json.Interpteter(cond)
        interp_res = interp.evaluate()
        print(f"interp_res: {interp_res}")
        # if name == "stnt1w_z_p_br_contiguous":
        #     print(f"stnt1w_z_p_br_contiguous:\n{inst}")
        #     condition = arm_json.converter.structure(inst, arm_json.Condition)
        #     print("condition:")
        #     print(condition)
        #     sys.exit(0)
    json.dump(instructions, open("inst-enc-old.json", "w"))


def dump_instructions(raw_json: dict | list) -> None:
    instructions = arm_json.converter.structure(raw_json, arm_json.JSONSchemaObject)
    if instructions is None:
        raise ValueError("got None instructions")

    arm_json.parse_instructions(instructions)


def get_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="instdec-py-util")
    parser.add_argument(
        "-i", "--instr-json", dest="instr_json", required=True, help="Instructions.json path"
    )
    return parser


def real_main(args: argparse.Namespace):
    print(f"args: {args}")
    raw_json = dict(json.load(open(args.instr_json)))

    # dump_instructions_old(raw_json)
    dump_instructions(raw_json)

    print(f"seen_identifiers: {arm_json.seen_identifiers}")
    print(f"seen_function_names: {arm_json.seen_function_names}")
    print(f"seen_value_meanings: {arm_json.seen_value_meanings}")
    print(f"seen_value_values: {arm_json.seen_value_values}")


def main():
    parser = get_arg_parser()
    args = parser.parse_args()
    real_main(args)


if __name__ == "__main__":
    main()
