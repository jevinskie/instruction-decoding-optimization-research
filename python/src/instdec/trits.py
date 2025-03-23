from typing import Literal, Self

import attrs

from .util import TagBase, defauto, tag


@tag("Trits")
@defauto
class Trits(TagBase):
    """
    A class to represent and manipulate trit strings (0, 1, X).
    """

    _tiep: Literal["Trits"]

    @staticmethod
    def normalize_trit_str(sval: str) -> str:
        sval = sval.strip("'")
        sval = sval.upper()
        return sval

    trits: str = attrs.field(converter=normalize_trit_str)

    @trits.validator
    def _check_trits(self, _, value):
        if not all(c in "01X" for c in value):
            raise ValueError(f"trit string must only contain '0', '1', or 'X' got '{value}'")

    def and_(self, other: Self) -> Self:
        nbit = len(self)
        onbit = len(other)
        minbit = min(nbit, onbit)
        maxbit = max(nbit, onbit)
        diff = maxbit - minbit
        nvs = [" "] * maxbit
        st = self.trits
        ot = other.trits
        if nbit < maxbit:
            eb = "0" if st[-1] != "X" else "X"
            st += eb * diff
        if onbit < maxbit:
            eb = "0" if ot[-1] != "X" else "X"
            ot += eb * diff
        for i in range(maxbit):
            if st[i] == "0" and ot[i] != "X":
                nvs[i] = "0"
            elif st[i] != "X" and ot[i] == "0":
                nvs[i] = "0"
            elif st[i] == "1" and ot[i] == "1":
                nvs[i] = "1"
            else:
                nvs[i] = "X"
        return type(self)("".join(nvs))

    def or_(self, other: Self) -> Self:
        nbit = len(self)
        onbit = len(other)
        minbit = min(nbit, onbit)
        maxbit = max(nbit, onbit)
        diff = maxbit - minbit
        nvs = [" "] * maxbit
        st = self.trits
        ot = other.trits
        if nbit < maxbit:
            eb = "0" if st[-1] != "X" else "X"
            st += eb * diff
        if onbit < maxbit:
            eb = "0" if ot[-1] != "X" else "X"
            ot += eb * diff
        for i in range(maxbit):
            if st[i] == "1" or ot[i] == "1":
                nvs[i] = "1"
            elif st[i] == "0" and ot[i] == "0":
                nvs[i] = "0"
            elif st[i] == "X" or ot[i] == "X":
                nvs[i] = "X"
            else:
                raise ValueError(f"Trit.or_ unhandled case: self: {self} other: {other}")
        return type(self)("".join(nvs))

    def not_(self) -> Self:
        nbit = len(self)
        nvs = [" "] * nbit
        st = self.trits
        for i in range(nbit):
            if st[i] == "1":
                nvs[i] = "0"
            elif st[i] == "0":
                nvs[i] = "1"
            elif st[i] == "X":
                nvs[i] = "X"
            else:
                raise ValueError(f"Trit.not_ unhandled case: self: {self}")
        return type(self)("".join(nvs))

    def eq_(self, other: Self, dont_care_ok: bool = False) -> Self:
        nbit = len(self)
        onbit = len(other)
        minbit = min(nbit, onbit)
        maxbit = max(nbit, onbit)
        diff = maxbit - minbit
        st = self.trits
        ot = other.trits
        if nbit < maxbit:
            eb = "0" if st[-1] != "X" else "X"
            st += eb * diff
        if onbit < maxbit:
            eb = "0" if ot[-1] != "X" else "X"
            ot += eb * diff
        are_equal = True
        for i in range(maxbit):
            if st[i] == "1" and ot[i] == "0":
                are_equal = False
                break
            elif st[i] == "0" and ot[i] == "1":
                are_equal = False
                break
            elif st[i] == "X" and ot[i] != "X":
                if not dont_care_ok:
                    are_equal = False
                    break
            elif st[i] != "X" or ot[i] == "X":
                if not dont_care_ok:
                    are_equal = False
                    break
            elif st[i] == "X" and ot[i] == "X":
                if not dont_care_ok:
                    are_equal = False
                    break
            else:
                raise ValueError(f"Trit.or_ unhandled case: self: {self} other: {other}")
        return type(self)("1" if are_equal else "0")

    def ne_(self, other: Self) -> Self:
        return self.eq_(other).not_()

    def __len__(self) -> int:
        return len(self.trits)

    def __repr__(self) -> str:
        return f"Trits({len(self.trits)}:'{self.trits}')"


@defauto
class TritRange:
    """
    Represents a range of trits within a 32-bit instruction word.
    """

    start: int = attrs.field()
    width: int = attrs.field()
    trits: Trits = attrs.field()

    @start.validator
    def _check_start(self, _, value):
        if not (0 <= value < 32):
            raise ValueError(f"start must be in [0, 32) got {value}")
        if not (value + self.width <= 33):
            raise ValueError(f"start + width must be  <= 32 got {value + self.width}")

    @width.validator
    def _check_width(self, _, value):
        if not (1 <= value <= 32):
            raise ValueError(f"width must be in [1, 32] got {value}")
        if not (value + self.start <= 33):
            raise ValueError(f"start + width must be  <= 32 got {value + self.start}")
        if value != len(self.trits):
            raise ValueError(
                f"width != len(trits) width: {value} len(trits): {len(self.trits)} trits: {self.trits}"
            )

    @trits.validator
    def _check_trits(self, _, value):
        if len(value) != self.width:
            raise ValueError(
                f"width != len(trits) width: {self.width} len(trits): {len(value)} trits: {value}"
            )

    def __str__(self) -> str:
        return self.trits.trits


class TritRanges:
    """
    Manages a collection of TritRange objects and merges them into a 32-bit trit string.
    """

    def __init__(self, ranges: list[TritRange] | None = None) -> None:
        """
        Initialize a TritRanges object with a list of TritRange objects.

        Args:
            ranges: List of TritRange objects.
        """
        if ranges is None:
            ranges = []
        self.ranges = ranges[:]

    def add_range(self, rng: TritRange) -> None:
        """
        Add a TritRange to the collection.

        Args:
            rng: A TritRange object to add.
        """
        self.ranges.append(rng)

    # FIXME: add mask!
    # look up stnt1w_z_p_br_contiguous (stnt1w_z_p_br.html) for Rm != 1111 negative mask
    def merge(self) -> Trits:
        """
        Merge all trit ranges into a single 32-bit Trits object.

        Returns:
            A Trits object representing the merged 32-bit trit string.

        Raises:
            ValueError: If there is a conflict in overlapping trit ranges.
        """
        # Initialize a 32-bit trit string with 'X' (don't care)
        merged = ["X"] * 32
        for rng in self.ranges:
            for i in range(rng.width):
                pos = rng.start + i
                current = merged[pos]
                new_trit = rng.trits.trits[i]
                if current == "X":
                    # If current position is unspecified, take the new trit
                    merged[pos] = new_trit
                elif new_trit == "X":
                    # If new trit is 'X', keep the current value
                    pass
                elif current == new_trit:
                    # If both are the same specific value, keep it
                    pass
                else:
                    # Conflict between '0' and '1'
                    raise ValueError(f"Conflict at position {pos}: {current} and {new_trit}")
        return Trits("".join(merged))

    def __repr__(self) -> str:
        return f"TritRanges(ranges={self.ranges})"
