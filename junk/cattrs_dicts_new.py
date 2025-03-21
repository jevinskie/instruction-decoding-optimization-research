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


class JSONObject:
    _type: typing.LiteralString


@defauto
class Operation(JSONObject):
    operation: str
    title: str
    _type: typing.Final[typing.Literal["Instruction.Operation"]] = "Instruction.Operation"


@defauto
class OperationAlias(JSONObject):
    operation_id: str
    description: str
    _type: typing.Final[typing.Literal["Instruction.OperationAlias"]] = "Instruction.OperationAlias"


Operationish = Operation | OperationAlias


# @tag("Instructions.Operations")  # fake
class Operations(dict[str, Operationish]):
    pass


@defauto
class Instruction(JSONObject):
    name: str
    opc: int
    _type: typing.Final[typing.Literal["Instruction.Instruction"]] = "Instruction.Instruction"


@defauto
class Instructions(JSONObject):
    instructions: list[Instruction]
    operations: Operations
    _type: typing.Final[typing.Literal["Instruction.Instructions"]] = "Instruction.Instructions"


DaTypes = Operation | OperationAlias | Instruction | Instructions | Operations


attrs.resolve_types(Operation, globals(), locals())
attrs.resolve_types(OperationAlias, globals(), locals())
attrs.resolve_types(Instruction, globals(), locals())
attrs.resolve_types(Instructions, globals(), locals())

converter = cattrs.Converter()
converter.detailed_validation = True


def structure_operations(obj: Operations, _: type) -> Operations:
    result = {}
    print(f"structure_operations: obj: {obj}")
    for key, value in obj.items():
        # Determine the type based on the _type field and structure accordingly
        if value.get("_type") == "Instruction.Operation":
            print("structure: Operation")
            result[key] = converter.structure(value, Operation)
        elif value.get("_type") == "Instruction.OperationAlias":
            print("structure: OperationAlias")
            result[key] = converter.structure(value, OperationAlias)
        else:
            raise ValueError(f"Unknown operation type: {value.get('_type')}")
    print(f"structure_operations: result: {result}")
    return result


# Register a custom structure hook for Operations
converter.register_structure_hook(Operations, structure_operations)


def my_tag_generator(cl: type) -> str:
    if hasattr(cl, "_type"):
        print(f"cl._type: {cl._type} cl: {cl} cl.__name__: {cl.__name__}")
        return str(cl._type)
    else:
        print(f"cl._type: N/A cl: {cl} cl.__name__: {cl.__name__}")
        return type(cl).__name__
        # return "Instructions.Operations"


# converter.register_structure_hook(JSONSchemaObject, structure_json_schema)
cattrs.strategies.configure_tagged_union(DaTypes, converter, tag_generator=my_tag_generator)


dumb_isa = {
    "_type": "Instruction.Instructions",
    "instructions": [
        {"_type": "Instruction.Instruction", "name": "add", "opc": 7},
        {"_type": "Instruction.Instruction", "name": "xor", "opc": 42},
    ],
    "operations": {
        # "_type": "Instruction.Operations",
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
