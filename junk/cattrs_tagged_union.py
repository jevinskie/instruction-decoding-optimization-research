#!/usr/bin/env python3
from typing import Literal

from attrs import define
from cattrs import Converter
from rich import inspect, print


@define
class ClassA:
    field_one: Literal["one"]


@define
class ClassB:
    field_one: Literal["two"] = "two"


Classes = ClassA | ClassB

print("ClassA:")
inspect(ClassA, all=True)
inspect(ClassA("one"), all=True)
# inspect(ClassA("onez"), all=True)

print("ClassB:")
inspect(ClassB, all=True)
# inspect(ClassB("two"), all=True)
# inspect(ClassB("twoz"), all=True)

conv = Converter()

cao = conv.structure({"field_one": "one"}, Classes)

inspect(cao, all=True)

cbo = conv.structure({"field_one": "two"}, Classes)

inspect(cbo, all=True)

ceo = conv.structure({"field_one": "twoz"}, Classes)

inspect(ceo, all=True)
