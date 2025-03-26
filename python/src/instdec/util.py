import inspect
import itertools
import math
from collections.abc import Callable, Iterable, Mapping, Sequence
from typing import Any, Final, Self, TypeVar, dataclass_transform, overload

import attr
import attrs

# from intervaltree import Interval, IntervalTree
import portion as P
import rich.markup
import rich.repr
from rich import print

T = TypeVar("T")
C = TypeVar("C", bound=type)


@overload
@dataclass_transform(field_specifiers=(attr.attrib, attrs.field))
def defauto(maybe_cls: C, *args, **kwargs) -> C: ...


@overload
@dataclass_transform(field_specifiers=(attr.attrib, attrs.field))
def defauto(maybe_cls: None, *args, **kwargs) -> Callable[[C], C]: ...


# from attrs:
# maybe_cls's type depends on the usage of the decorator.  It's a class
# if it's used as `@attrs` but `None` if used as `@attrs()`.
def defauto(maybe_cls: C | None, *args, **kwargs) -> C | Callable[[C], C]:
    kwargs["auto_attribs"] = True
    kwargs["on_setattr"] = None
    kwargs["frozen"] = True
    return attrs.define(maybe_cls, *args, **kwargs)


def num_b10_digits(n: int) -> int:
    return int(math.ceil(math.log10(n + 1)))


def bitfield_indices(width: int) -> list[str]:
    if width <= 0:
        raise ValueError(f"width must be > 0 not {width}")
    ndigits = num_b10_digits(width)
    chars = [["x"] * width] * ndigits
    for i in range(width):
        itmp = i
        inumdig = max(1, num_b10_digits(i))
        for j in range(inumdig):
            dval = itmp % 10
            itmp -= dval
            itmp //= 10
            old_dval = chars[j][width - 1 - i]
            print(
                rich.markup.escape(
                    f'old_dval chars(j)(width - 1 - i): r0: {j} r1: {width - 1 - i} val: "{old_dval}"'
                )
            )
            chars[j][width - 1 - i] = str(dval)
            # potential_digit = i % 10 ** (j + 1)
            # tst = dval >= 10**j
            print(
                rich.markup.escape(
                    f"width - 1 - i: {width - 1 - i} j: {j} dval: {dval} itmp: {itmp} i: {i} inumdig: {inumdig}"
                )
            )
            # if i >= limit:
            #     if tst:
            #         chars[j][width - 1 - i] = " "
            #     else:
            #         chars[j][width - 1 - i] = str(potential_digit)
    print(chars)
    for line_chars in chars:
        print(f"line_chars: {line_chars!r}")
    return ["".join(line_chars) for line_chars in chars]


@attrs.define(auto_attribs=True, on_setattr=None, frozen=True, order=True)
class Span:
    start: int
    width: int
    name: str | None = attrs.field(default=None, eq=False, hash=False)

    @property
    def end(self) -> int:
        """End bit index (one past last real index)"""
        return self.start + self.width

    def encompases(self, other: Self) -> bool:
        return self.start <= other.start and self.end >= other.end

    def equal_w_name(self, other: Self) -> bool:
        return self.start == other.start and self.width == other.width and self.name == other.name

    def ascii_art(self, max_width) -> str:
        if self.end > max_width:
            raise ValueError(f"Span: {self} ascii_art() max_width: {max_width} > end: {self.end}")
        rl = [" "] * max_width
        idx_end = max_width - self.start
        idx_start = max_width - self.end
        if self.width == 1:
            rl[idx_start] = "#"
        else:
            rl[idx_start] = "<"
            rl[idx_end - 1] = ">"
            for i in range(idx_start + 1, idx_end - 1):
                rl[i] = "="
        rs = "[" + "".join(rl) + "]"
        rs = rich.markup.escape(rs)
        return "[" + "".join(rl) + "]"

    # def __repr__(self) -> str:
    #     return f"Span({self.ascii_art(32)})"

    def __rich_repr__(self) -> rich.repr.Result:
        yield "name", self.name, None
        yield "s", self.start
        yield "w", self.width
        yield "e", self.end


@defauto
class Pigeonholes:
    width: Final[int] = attrs.field()
    _spans: set[Span] = attrs.Factory(set)
    # _intervals: P.Interval = attrs.Factory(P.Interval)

    @property
    def spans(self) -> set[Span]:
        return self._spans

    # @property
    # def intervals(self) -> P.Interval:
    #     return self._intervals

    def add_span(self, spn: Span) -> None:
        if spn in self._spans:
            for ispn in self._spans:
                if spn == ispn:
                    if not spn.equal_w_name(ispn):
                        spstrs: list[str] = []
                        for espn in self._spans:
                            spstrs.append(espn.ascii_art(32))
                        spstrs.sort()
                        for s in spstrs:
                            print(s)
                        print("", flush=True)
                        raise ValueError(f"Adding span {spn} thats already in Pigeonholes: {self}")
        self._spans.add(spn)
        # self._intervals |= P.closedopen(spn.start, spn.end, spn)

    def has_overlaps(self) -> bool:
        for a, b in itertools.combinations(self._spans, 2):
            ai = P.closedopen(a.start, a.end)
            bi = P.closedopen(b.start, b.end)
            if ai.overlaps(bi):
                return True
        return False
        # return self._intervals.overlaps(0, self.width)


def traverse_nested(
    data: Any,
    callback: Callable[[Any, str], T | None],
    path: str = "$",
    max_depth: int = -1,
    include_private: bool = False,
    skip_callables: bool = True,
    visited: set[int] | None = None,
) -> T | None:
    """
    Traverse deeply nested data structures and call a callback for each object found.

    Args:
        data: The nested data structure to traverse
        callback: Function that takes (object, path) and returns optional result
                 If callback returns non-None, traversal stops for that branch
        path: The current path in XPath-style notation (default: "$")
        max_depth: Maximum recursion depth (-1 means no limit)
        include_private: Whether to include private attributes (starting with _)
        skip_callables: Whether to skip callable attributes
        visited: Set of object ids already visited (for cycle detection)
    """
    # Initialize visited set for cycle detection
    if visited is None:
        visited = set()

    # Skip None values and already visited objects
    if data is None or id(data) in visited:
        return None

    # Call the callback on the current object
    result: T | None = callback(data, path)
    visited.add(id(data))

    # Stop recursion if max_depth is reached or callback returns non-None
    if max_depth == 0 or result is not None:
        if result is not None:
            return result
        return None

    next_depth = max_depth - 1 if max_depth > 0 else -1

    downcall_res: T | None = None

    # Handle mapping types (dict-like)
    if isinstance(data, Mapping):
        for key, value in data.items():
            if key is None or value is None:
                continue

            # Format path based on key type
            key_path = (
                f"{path}['{key}']"
                if isinstance(key, str) and not key.isidentifier()
                else f"{path}.{key}"
                if isinstance(key, str)
                else f"{path}[{key}]"
            )

            downcall_res = traverse_nested(
                value, callback, key_path, next_depth, include_private, skip_callables, visited
            )
            if downcall_res is not None:
                return downcall_res

    # Handle sequence types (list-like, but not strings)
    elif isinstance(data, Sequence) and not isinstance(data, (str, bytes, bytearray)):
        for i, item in enumerate(data):
            downcall_res = traverse_nested(
                item, callback, f"{path}[{i}]", next_depth, include_private, skip_callables, visited
            )
            if downcall_res is not None:
                return downcall_res

    # Handle other iterables
    elif isinstance(data, Iterable) and not isinstance(data, (str, bytes, bytearray)):
        for i, item in enumerate(data):
            downcall_res = traverse_nested(
                item, callback, f"{path}[{i}]", next_depth, include_private, skip_callables, visited
            )
            if downcall_res is not None:
                return downcall_res

    # Handle objects with attributes
    elif (
        hasattr(data, "__slots")
        or hasattr(data, "__dict__")
        or inspect.isclass(data)
        or inspect.ismodule(data)
    ):
        # Get attributes, either from __dict__ or using dir()
        attributes = (
            vars(data)
            if hasattr(data, "__dict__") and not hasattr(data, "__slots__")
            else {
                attr: getattr(data, attr)
                for attr in dir(data)
                if not (skip_callables and callable(getattr(data, attr)))
            }
        )

        for attr_name, attr_value in attributes.items():
            # Skip private attributes if requested
            if not include_private and attr_name.startswith("_"):
                continue

            # Skip callable attributes if requested
            if skip_callables and callable(attr_value):
                continue

            downcall_res = traverse_nested(
                attr_value,
                callback,
                f"{path}.{attr_name}",
                next_depth,
                include_private,
                skip_callables,
                visited,
            )
            if downcall_res is not None:
                return downcall_res
    return None
