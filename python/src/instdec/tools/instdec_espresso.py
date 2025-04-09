#!/usr/bin/env python3

import argparse
import subprocess

import rich.traceback
from path import Path

from instdec.espresso import espresso_subcmds, generate_espresso, parse_espresso

rich.traceback.install()


def espresso_gauntlet(enc_info: dict[str, tuple[int, int]], ein_path: Path) -> None:
    for subcmd in espresso_subcmds:
        if subcmd in (
            "pairall",
            "verify",
            "PLAverify",
            "dsharp",
            "intersect",
            "sharp",
            "xor",
            "union",
        ):
            continue
        cmd = ["espresso", "-d", "-t", "-v", "", f"-D{subcmd}", str(ein_path)]
        cmd_str = " ".join(cmd)
        print(f"cmd: {cmd_str}", flush=True)
        spres = subprocess.run(cmd, capture_output=True)
        with open(f"eo-{subcmd}.txt", "wb") as f:
            f.write(spres.stdout)


def get_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="instdec-py-espresso")
    parser.add_argument(
        "-i",
        "--in",
        dest="espresso_in",
        type=Path,
        required=True,
        help="Input Espresso file",
    )
    parser.add_argument(
        "-o",
        "--out",
        dest="espresso_out",
        type=Path,
        required=False,
        help="Output Espresso file",
    )
    return parser


def real_main(args: argparse.Namespace) -> None:
    enc_info = parse_espresso(open(args.espresso_in).read())

    # print(enc_info)
    espresso_gauntlet(enc_info, args.espresso_in)

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
