import functools
from typing import Self

import anytree
import attrs
from rich import print


def auto_clear_cache_on_false(cache_clearing_methods, attribute_name, trigger_value=False):
    def class_decorator(cls):
        new_attribute = attrs.field(
            default=trigger_value,
            init=True,
            on_setattr=[
                clear_cache_if_false(cache_clearing_methods, attribute_name, trigger_value)
            ],
            repr=False,
        )
        setattr(cls, attribute_name, new_attribute)
        return cls

    def clear_cache_if_false(cache_clearing_methods, attribute_name, trigger_value):
        def setter(inst, attribute, value):
            if value == trigger_value:
                for method in cache_clearing_methods:
                    if hasattr(inst, method) and hasattr(getattr(inst, method), "clear_cache"):
                        getattr(getattr(inst, method), "clear_cache")(
                            inst
                        )  # Pass instance to clear_cache
            return value

        return setter

    return class_decorator


def conditional_method_cache(condition_attr):
    def decorator(func):
        cached_attr_name = f"_{func.__name__}_cache"

        @functools.wraps(func)
        def wrapper(self, *args, **kwargs):
            if not hasattr(self, cached_attr_name):
                setattr(self, cached_attr_name, {})  # Set attribute dynamically if it doesn't exist

            cache = getattr(self, cached_attr_name)

            if getattr(self, condition_attr, False):
                if args in cache:
                    return cache[args]
                else:
                    result = func(self, *args, **kwargs)
                    cache[args] = result
                    return result
            else:
                return func(self, *args, **kwargs)

        def clear_cache(self):
            if hasattr(self, cached_attr_name):
                getattr(self, cached_attr_name).clear()

        wrapper.clear_cache = clear_cache  # type: ignore
        return wrapper

    return decorator


@attrs.define(slots=False)
@functools.total_ordering
@auto_clear_cache_on_false(["__hash__"], "finalized")
class Node(anytree.NodeMixin):
    name: str
    _finalized: bool = attrs.field(default=False, repr=False)

    @property
    def left_child(self) -> Self | None:
        clen = len(self.children)
        if clen == 0:
            return None
        if clen != 2:
            raise ValueError(f"self.children len != 2: {self.children}")
        return self.children[0]

    @property
    def right_child(self) -> Self | None:
        clen = len(self.children)
        if clen == 0:
            return None
        if clen != 2:
            raise ValueError(f"self.children len != 2: {self.children}")
        return self.children[1]

    @property
    def left_and_right_child(self) -> tuple[Self, Self] | None:
        clen = len(self.children)
        if clen == 0:
            return None
        if clen != 2:
            raise ValueError(f"self.children len != 2: {self.children}")
        return (self.children[0], self.children[1])

    @left_and_right_child.setter
    def left_and_right_child(self, left_and_right: tuple[Self, Self] | None) -> None:
        if left_and_right is None:
            self.children: tuple[Self, Self] | tuple = tuple()
            return
        self.children = left_and_right

    def __lt__(self, other) -> bool:
        if not isinstance(other, type(self)):
            raise NotImplementedError
        else:
            raise NotImplementedError

    def __eq__(self, other) -> bool:
        if not isinstance(other, type(self)):
            raise NotImplementedError
        else:
            return False

    @conditional_method_cache("finalized")
    def __hash__(self) -> int:
        hash_list = [self.name]
        if not self.is_leaf:
            if self.left_child is None:
                raise ValueError(f"left child None: {self}")
            if self.right_child is None:
                raise ValueError(f"right child None: {self}")
            hash_list += [self.left_child, self.right_child]
        return hash(tuple(hash_list))


def generate_search_tree(einf: dict[str, tuple[int, int]]) -> None:
    tree = {}
    for iname, bvs in einf.items():
        bm, bp = bvs
    print("tree:")
    print(tree)
