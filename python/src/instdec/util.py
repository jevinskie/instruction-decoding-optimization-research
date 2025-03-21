from collections.abc import Callable

import attrs
from typing_extensions import TypeVar

T = TypeVar("T")


def defauto(*args, **kwargs) -> Callable[[type[T]], type[T]]:
    kwargs["auto_attribs"] = True
    kwargs["on_setattr"] = None
    kwargs["frozen"] = True
    return attrs.define(*args, **kwargs)
