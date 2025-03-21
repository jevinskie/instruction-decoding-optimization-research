#!/usr/bin/env python3

import sys
import typing
from collections.abc import Callable

import attrs
import cattrs
import cattrs.strategies
import rich
from rich import print

# prevent ruff removal of imports
sys
typing
attrs
cattrs
rich
print

T = typing.TypeVar("T")


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


@tag("Instruction.Operation")
@defauto
class Operation:
    operation: str
    title: str


@tag("Instruction.OperationAlias")
@defauto
class OperationAlias:
    operation_id: str
    description: str


Operationish = Operation | OperationAlias


class Operations(dict[str, Operationish]):
    pass


@tag("Instruction.Instruction")
@defauto
class Instruction:
    name: str
    opc: int


@tag("Instruction.Instructions")
@defauto
class Instructions:
    instructions: list[Instruction]
    operations: Operations


DaTypes = Operation | OperationAlias | Instruction | Instructions


attrs.resolve_types(Operation, globals(), locals())
attrs.resolve_types(OperationAlias, globals(), locals())
attrs.resolve_types(Instruction, globals(), locals())
attrs.resolve_types(Instructions, globals(), locals())

converter = cattrs.Converter()
converter.detailed_validation = True


def structure_operations(obj: dict[str, Operation], _: type) -> Operations:
    result = {}
    for key, value in obj.items():
        # Determine the type based on the _type field and structure accordingly
        if value.get("_type") == "Instruction.Operation":
            result[key] = converter.structure(value, Operation)
        elif value.get("_type") == "Instruction.OperationAlias":
            result[key] = converter.structure(value, OperationAlias)
        else:
            raise ValueError(f"Unknown operation type: {value.get('_type')}")
    return result


def my_tag_generator(cl: type) -> str:
    print(f"cl._type: {cl._type} type(cl): {type(cl)}")
    return cl._type


# converter.register_structure_hook(JSONSchemaObject, structure_json_schema)
cattrs.strategies.configure_tagged_union(DaTypes, converter, tag_generator=my_tag_generator)


# Register a custom structure hook for Operations
converter.register_structure_hook(Operations, structure_operations)


dumb_isa = {
    "_type": "Instruction.Instructions",
    "instructions": [
        {"_type": "Instruction.Instruction", "name": "add", "opc": 7},
        {"_type": "Instruction.Instruction", "name": "xor", "opc": 42},
    ],
    "operations": {
        "add_op": {
            "_type": "Instruction.Operation",
            "operation": "add_op_op",
            "title": "add_op_title",
        },
        "add_op_alias": {
            "_type": "Instruction.OperationAlias",
            "operation_id": "add_op_alias_op_id",
            "description": "add_op_alias_descr",
        },
    },
}

instrs = converter.structure(dumb_isa, DaTypes)
print("instrs:")
print(instrs)
