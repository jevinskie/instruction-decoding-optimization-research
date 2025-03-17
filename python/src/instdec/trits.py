class Trits:
    """
    A class to represent and manipulate trit strings (0, 1, X).
    """

    def __init__(self, value: str):
        """
        Initialize a Trits object from a string of trits.

        Args:
            value: A string of '0', '1', 'X' (case-insensitive).

        Raises:
            ValueError: If the string contains invalid characters.
        """
        self.trits = value.upper()
        if not all(c in "01X" for c in self.trits):
            raise ValueError(f"trit string must only contain '0', '1', or 'X' got '{self.trits}")

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
