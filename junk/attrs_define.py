# https://github.com/python-attrs/attrs/blob/main/src/attr/_next_gen.py
import attr


def define(
    maybe_cls=None,
    *,
    auto_attribs=None,
):
    def do_it(cls, auto_attribs):
        return attr.attrs(
            maybe_cls=cls,
            auto_attribs=auto_attribs,
        )

    def wrap(cls):
        return do_it(cls, auto_attribs)

    # maybe_cls's type depends on the usage of the decorator.  It's a class
    # if it's used as `@attrs` but `None` if used as `@attrs()`.
    if maybe_cls is None:
        return wrap

    return wrap(maybe_cls)
