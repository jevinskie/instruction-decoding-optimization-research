from typing import Self

import attrs


@attrs.define(eq=False)
class Trits:
    """
    A class to represent and manipulate trit strings (0, 1, X).
    """

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
        return Trits("".join(nvs))

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
        return Trits("".join(nvs))

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
        return Trits("".join(nvs))

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
        return Trits("1" if are_equal else "0")

    def ne_(self, other: Self) -> Self:
        return self.eq_(other).not_()

    def __len__(self) -> int:
        return len(self.trits)

    def __repr__(self) -> str:
        return f"Trits('{self.trits}')"


class TritRange:
    """
    Represents a range of trits within a 32-bit instruction word.
    """

    def __init__(self, start: int, width: int, trits: str):
        """
        Initialize a TritRange object.

        Args:
            start: Starting index (0-31).
            width: Width of the range (0-32).
            trits: String of trits ('0', '1', 'X') of length `width`.

        Raises:
            ValueError: If start, width, or trits are invalid.
        """
        # Validate start index
        if not (0 <= start < 32):
            raise ValueError("start must be between 0 and 31")
        # Validate width, ensuring start + width <= 32
        if not (0 <= width <= 32 - start):
            raise ValueError(f"width must be between 0 and {32 - start}")
        # Validate trit string length
        if len(trits) != width:
            raise ValueError(f"trits must have length {width}")
        self.start = start
        self.width = width
        self.trits = trits.upper()
        # Validate trit characters
        if not all(c in "01X" for c in self.trits):
            raise ValueError("trits must only contain '0', '1', or 'X'")

    def __repr__(self) -> str:
        return f"TritRange(start={self.start}, width={self.width}, trits='{self.trits}')"

    def __str__(self) -> str:
        return self.trits


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
                new_trit = rng.trits[i]
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
