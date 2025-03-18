from collections.abc import Callable
from typing import TypeVar

import attrs

T = TypeVar("T")


def defauto(*args, **kwargs) -> Callable[[type[T]], type[T]]:
    kwargs["auto_attribs"] = True
    kwargs["on_setattr"] = None
    kwargs["frozen"] = True
    return attrs.define(*args, **kwargs)
