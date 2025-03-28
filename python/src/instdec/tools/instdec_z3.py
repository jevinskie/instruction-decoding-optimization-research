#!/usr/bin/env python3

import argparse
import json

import rich.traceback
from path import Path
from rich import print

rich.traceback.install()


def get_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="instdec-py-util")
    parser.add_argument(
        "-e",
        "--enc-json",
        dest="enc_json",
        type=Path,
        required=True,
        help="Prebased encoding bitmask/bitpattern JSON path",
    )
    return parser


def real_main(args: argparse.Namespace):
    raw_json_dict = dict(json.load(open(args.enc_json)))

    enc_info: dict[str, tuple[int, int]] = {}
    for iname, einfo_str in raw_json_dict.items():
        enc_info[iname] = (int(einfo_str[0], 2), int(einfo_str[1], 2))

    print(enc_info)


def main():
    parser = get_arg_parser()
    args = parser.parse_args()
    real_main(args)


if __name__ == "__main__":
    main()
