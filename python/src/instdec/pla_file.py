from __future__ import annotations

import attrs


@attrs.define(auto_attribs=True, frozen=True)
class Term:
    ins: str
    outs: str


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
        lin: list[str] | None = None
        lout: list[str] | None = None
        t: list[Term] = []
        n: str | None = None
        for ln in pla_str.splitlines():
            # match ln in
            str(ln)
            pass
        map(str, (lin, lout, t, n))
        return PLA(0, 0)

    def to_str(self) -> str:
        return ""
