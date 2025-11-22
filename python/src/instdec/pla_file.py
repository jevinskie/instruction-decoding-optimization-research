from __future__ import annotations

import attrs


@attrs.define(auto_attribs=True)
class PLA:
    num_in: int
    num_out: int
    labels_in: list[str] | None = None
    labels_out: list[str] | None = None
    name: str | None = None

    @staticmethod
    def from_str(pla_str: str) -> PLA:
        return PLA(0, 0)

    def to_str(self) -> str:
        return ""
