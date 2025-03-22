import inspect
from collections.abc import Callable, Iterable, Mapping, Sequence
from typing import Any, Final, ParamSpec, TypeVar, overload

import attrs
from intervaltree import Interval, IntervalTree

T = TypeVar("T")
C = TypeVar("C", bound=type)
P = ParamSpec("P")


@overload
def defauto(maybe_cls: C) -> C: ...


@overload
def defauto(maybe_cls: None, *args: P.args, **kwargs: P.kwargs) -> Callable[P, C]: ...


# from attrs:
# maybe_cls's type depends on the usage of the decorator.  It's a class
# if it's used as `@attrs` but `None` if used as `@attrs()`.
def defauto(maybe_cls: C | None, *args, **kwargs) -> C | Callable[[P], C]:
    kwargs["auto_attribs"] = True
    kwargs["on_setattr"] = None
    kwargs["frozen"] = True
    if maybe_cls is None:
        return attrs.define(*args, **kwargs)
    else:
        return attrs.define(maybe_cls, *args, **kwargs)


def tag(tag_val: str) -> Callable[[C], C]:
    def wrap(cls: C) -> C:
        if not isinstance(cls, type):
            raise ValueError(f"cls should be a type not '{type(cls)}' cls: {cls}")
        setattr(cls, "_type", tag_val)
        return cls

    return wrap


@defauto
class Span:
    start: Final[int] = attrs.field()
    width: Final[int] = attrs.field()
    name: Final[str | None] = attrs.field(default=None)

    @property
    def end(self) -> int:
        """End bit index (one past last real index)"""
        return self.start + self.end

    def __eq__(self, value) -> bool:
        if not isinstance(value, Span):
            return False
        return self.start == value.start and self.width == value.width


@defauto
class Pigeonholes:
    width: Final[int] = attrs.field()
    _spans: set[Span] = attrs.Factory(set)
    _intervals: IntervalTree = attrs.Factory(IntervalTree)

    @property
    def spans(self) -> set[Span]:
        return self._spans

    @property
    def intervals(self) -> IntervalTree:
        return self._intervals

    def add_span(self, span: Span) -> None:
        if span in self._spans:
            raise ValueError(f"Adding span {span} thats already in Pigeonholes: {self}")
        self._spans.add(span)
        self._intervals.add(Interval(span.start, span.end, span))

    def get_overlaps(self) -> list[Span] | None:
        return None


def traverse_nested(
    data: Any,
    callback: Callable[[Any, str], T | None],
    path: str = "$",
    max_depth: int = -1,
    include_private: bool = False,
    skip_callables: bool = True,
    visited: set[int] | None = None,
) -> None:
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
    result = callback(data, path)
    visited.add(id(data))

    # Stop recursion if max_depth is reached or callback returns non-None
    if max_depth == 0 or result is not None:
        return result

    next_depth = max_depth - 1 if max_depth > 0 else -1

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

            traverse_nested(
                value, callback, key_path, next_depth, include_private, skip_callables, visited
            )

    # Handle sequence types (list-like, but not strings)
    elif isinstance(data, Sequence) and not isinstance(data, (str, bytes, bytearray)):
        for i, item in enumerate(data):
            traverse_nested(
                item, callback, f"{path}[{i}]", next_depth, include_private, skip_callables, visited
            )

    # Handle other iterables
    elif isinstance(data, Iterable) and not isinstance(data, (str, bytes, bytearray)):
        for i, item in enumerate(data):
            traverse_nested(
                item, callback, f"{path}[{i}]", next_depth, include_private, skip_callables, visited
            )

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

            return traverse_nested(
                attr_value,
                callback,
                f"{path}.{attr_name}",
                next_depth,
                include_private,
                skip_callables,
                visited,
            )
