from __future__ import annotations

import re

import attrs


@attrs.define(auto_attribs=True, frozen=True)
class Term:
    ins: str
    outs: str


_term_pattern = re.compile(r"([01-]+)\s+([01-]+)")


@attrs.define(auto_attribs=True)
class PLA:
    terms: list[Term]
    num_in: int
    num_out: int
    labels_in: list[str] | None = None
    labels_out: list[str] | None = None
    name: str | None = None

    @staticmethod
    def from_str(pla_str: str) -> PLA:
        t: list[Term] = []
        ni: int | None = None
        no: int | None = None
        lin: list[str] | None = None
        lout: list[str] | None = None
        n: str | None = None
        expected_p: int | None = None
        for ln in pla_str.splitlines():
            if len(ln) == 0:
                continue
            if ln.startswith("#"):
                continue
            if ln.startswith("."):
                cmd = ln.removeprefix(".")
                match cmd:
                    case "i":
                        ni = int(cmd.removeprefix("i"))
                    case "o":
                        no = int(cmd.removeprefix("o"))
                    case "ilb":
                        lin = list(cmd.removeprefix("ilb").split())
                    case "olb":
                        lout = list(cmd.removeprefix("olb").split())
                    case "p":
                        expected_p = int(cmd.removeprefix("p"))
                    case "e":
                        break
            term_matches = _term_pattern.match(ln)
            if term_matches:
                in_terms_str, out_terms_str = term_matches.groups()
                t.append(Term(in_terms_str, out_terms_str))
            else:
                raise ValueError(f"unhandled line: {ln}")
        if expected_p is not None and len(t) != expected_p:
            raise ValueError(f"Got {len(t)} terms not {expected_p} as specified by '.p N'")
        if len(t) == 0:
            return PLA([], ni if ni is not None else 0, no if no is not None else 0, lin, lout, n)
        return PLA(0, 0)

    def to_str(self) -> str:
        return ""
