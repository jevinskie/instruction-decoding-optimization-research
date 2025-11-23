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
        t: list[Term] = []
        ni: int | None = None
        no: int | None = None
        lin: list[str] | None = None
        lout: list[str] | None = None
        n: str | None = None
        for ln in pla_str.splitlines():
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
                        pass
                    case "e":
                        pass

            str(ln)
            pass
        map(str, (lin, lout, t, n, no, ni))
        return PLA(0, 0)

    def to_str(self) -> str:
        return ""
