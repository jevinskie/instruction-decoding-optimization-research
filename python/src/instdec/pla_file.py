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
    # https://people.eecs.berkeley.edu/~alanmi/research/espresso/espresso_5.html
    terms: list[Term]
    num_in: int
    num_out: int
    labels_in: list[str] | None = None
    labels_out: list[str] | None = None

    @staticmethod
    def from_str(pla_str: str) -> PLA:
        # this is non-compliant in many ways (e.g. treats whitespace as significant)
        t: list[Term] = []
        ni: int | None = None
        no: int | None = None
        lin: list[str] | None = None
        lout: list[str] | None = None
        expected_p: int | None = None
        for line_no, ln in enumerate(pla_str.splitlines()):
            if len(ln) == 0:
                continue
            if ln.startswith("#"):
                continue
            if ln.startswith("."):
                cmd = ln.removeprefix(".")
                if cmd.startswith("ilb "):
                    if lin is not None:
                        raise ValueError(".ilb already processed")
                    lin = list(cmd.removeprefix("ilb ").split())
                    continue
                elif cmd.startswith("ob "):
                    if lout is not None:
                        raise ValueError(".ob already processed")
                    lout = list(cmd.removeprefix("ob ").split())
                    continue
                elif cmd.startswith("i "):
                    if ni is not None:
                        raise ValueError(".i already processed")
                    ni = int(cmd.removeprefix("i "))
                    continue
                elif cmd.startswith("o "):
                    if no is not None:
                        raise ValueError(".o already processed")
                    no = int(cmd.removeprefix("o "))
                    continue
                elif cmd.startswith("p "):
                    if expected_p is not None:
                        raise ValueError(".p already processed")
                    expected_p = int(cmd.removeprefix("p "))
                    continue
                elif cmd == "e":
                    break
                else:
                    raise ValueError(f"unhandled line: line_no:{line_no:2} '{ln}'")
            term_matches = _term_pattern.match(ln)
            if term_matches:
                in_terms_str, out_terms_str = term_matches.groups()
                t.append(Term(in_terms_str, out_terms_str))
            else:
                raise ValueError(f"unhandled line: {ln}")
        if expected_p is not None and len(t) != expected_p:
            raise ValueError(f"Got {len(t)} terms not {expected_p} as specified by '.p N'")
        if len(t) == 0:
            return PLA([], ni if ni is not None else 0, no if no is not None else 0, lin, lout)
        calc_ni, calc_no = len(t[0].ins), len(t[0].outs)
        if ni is None or calc_ni != ni:
            raise ValueError(".i bad")
        if no is None or calc_no != no:
            raise ValueError(".o bad")
        return PLA(t, ni, no, lin, lout)

    def to_str(self) -> str:
        return ""
