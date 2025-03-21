from collections.abc import Callable

import attrs
from typing_extensions import TypeVar

T = TypeVar("T")


def defauto(*args, **kwargs) -> Callable[[type[T]], type[T]]:
    kwargs["auto_attribs"] = True
    kwargs["on_setattr"] = None
    kwargs["frozen"] = True
    return attrs.define(*args, **kwargs)


def tag(value: str):
    def decorator(cls: type[T]) -> type[T]:
        class Wrapped(cls):
            _type: str = value

        # Preserve the original class name
        Wrapped.__name__ = cls.__name__
        Wrapped.__qualname__ = cls.__qualname__
        return Wrapped

    return decorator
