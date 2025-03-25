from __future__ import annotations

import enum
import typing
from typing import Literal

import attrs
from cattrs import Converter

from .trits import Trits
from .util import Span, defauto


class BinOp(enum.StrEnum):
    AND = "&&"
    NE = "!="
    EQ = "=="
    OR = "||"
    IN = "IN"


class UnOp(enum.StrEnum):
    NOT = "!"


class ConsOp(enum.StrEnum):
    IMPLIES = "-->"
    IFF = "<->"


seen_value_meanings: set[str] = set()
seen_value_values: set[Trits] = set()


@defauto
class Value:
    value: Trits
    meaning: str | None = attrs.field(repr=False)  # always observed as null
    _type: Literal["Values.Value"] = attrs.field(default="Values.Value", repr=False)

    def __attrs_post_init__(self):
        seen_value_meanings.add(self.meaning)
        seen_value_values.add(self.value)
        if self.meaning is not None:
            raise NotImplementedError(f"finally a release with non-null `meaning`? Value: {self}")


seen_identifiers: set[str] = set()


@defauto
class Identifier:
    value: str
    _type: Literal["AST.Identifier"] = attrs.field(default="AST.Identifier", repr=False)

    def __attrs_post_init__(self):
        seen_identifiers.add(self.value)


@defauto
class Bool:
    value: bool
    _type: Literal["AST.Bool"] = attrs.field(default="AST.Bool", repr=False)


@defauto
class Set:
    values: tuple[Value, ...]
    _type: Literal["AST.Set"] = attrs.field(default="AST.Set", repr=False)

    @property
    def values_set(self) -> set[Value]:
        rs: set[Value] = set(self.values)
        if len(self.values) != len(rs):
            raise ValueError(f"duplicate detected in AST.Set: {self}")
        return rs


@defauto
class BinaryOp:
    left: Expression
    op: BinOp
    right: Expression
    _type: Literal["AST.BinaryOp"] = attrs.field(default="AST.BinaryOp", repr=False)


@defauto
class UnaryOp:
    expr: Expression
    op: UnOp
    _type: Literal["AST.UnaryOp"] = attrs.field(default="AST.UnaryOp", repr=False)


seen_function_names: set[str] = set()


@defauto
class Function:
    name: str
    arguments: tuple[Expression, ...]
    _type: Literal["AST.Function"] = attrs.field(default="AST.Function", repr=False)

    def __attrs_post_init__(self):
        seen_function_names.add(self.name)


# Define Expression as a union of all possible AST node types
Expression = Bool | BinaryOp | Function | Identifier | Set | UnaryOp | Value
Valueish = Value | Set


@defauto
class Range:
    start: int
    width: int
    _type: Literal["Range"] = attrs.field(default="Range", repr=False)

    @property
    def end(self) -> int:
        return self.start + self.width

    @property
    def span(self) -> Span:
        return Span(self.start, self.width)


@defauto
class EncodesetBase:
    value: Value
    range: Range
    should_be_mask: Value


@defauto
class EncodesetBits(EncodesetBase):
    _type: Literal["Instruction.Encodeset.Bits"] = attrs.field(
        default="Instruction.Encodeset.Bits", repr=False
    )


@defauto
class EncodesetField(EncodesetBase):
    name: str
    _type: Literal["Instruction.Encodeset.Field"] = attrs.field(
        default="Instruction.Encodeset.Field", repr=False
    )


@defauto
class EncodsetShouldBeBits:
    value: Value
    range: Range
    _type: Literal["Instruction.Encodeset.ShouldBeBits"] = attrs.field(
        default="Instruction.Encodeset.ShouldBeBits", repr=False
    )

    def __attrs_post_init__(self):
        raise NotImplementedError("deprecated object")


EncodesetValues = EncodesetBits | EncodesetField | EncodsetShouldBeBits


@defauto
class Encodeset:
    values: tuple[EncodesetValues, ...]
    width: int
    _type: Literal["Instruction.Encodeset.Encodeset"] = attrs.field(
        default="Instruction.Encodeset.Encodeset", repr=False
    )

    def get_fields(self) -> list[EncodesetField]:
        fields: list[EncodesetField] = []
        for v in self.values:
            if isinstance(v, EncodesetField):
                fields.append(v)
        names = [lambda f: f.value for f in fields]
        if len(names) != len(set(names)):
            raise ValueError("duplicates in Encodeset EncodesetField names")
        ranges = [lambda f: f.range for f in fields]
        if len(ranges) != len(set(ranges)):
            raise ValueError("duplicates in Encodeset EncodesetField ranges")
        return fields

    def get_field(self, name: str) -> EncodesetField | None:
        fields = self.get_fields()
        for f in fields:
            if f.name == name:
                return f
        return None

    def has_field(self, name: str) -> bool:
        return self.get_field(name) is not None

    def get_bits(self) -> list[EncodesetBits]:
        bits: list[EncodesetBits] = []
        for v in self.values:
            if isinstance(v, EncodesetBits):
                bits.append(v)
        ranges = [lambda b: b.range for b in bits]
        if len(ranges) != len(set(ranges)):
            raise ValueError("duplicates in Encodeset EncodesetBits ranges")
        return bits


@defauto
class InstructionInstance:
    name: str
    condition: Expression | None = attrs.field(default=None)
    children: tuple[InstructionInstance, ...] | None = attrs.field(default=None)
    _type: Literal["Instruction.InstructionInstance"] = attrs.field(
        default="Instruction.InstructionInstance", repr=False
    )


@defauto
class InstructionAlias:
    name: str
    operation_id: str
    condition: Expression | None = attrs.field(default=None)
    # assembly: ?
    _type: Literal["Instruction.InstructionAlias"] = attrs.field(
        default="Instruction.InstructionAlias", repr=False
    )


Instructionish = (
    typing.ForwardRef("Instruction", is_argument=False) | InstructionInstance | InstructionAlias
)


@defauto
class Instruction:
    name: str
    operation_id: str
    encoding: Encodeset
    condition: Expression | None = attrs.field(default=None)
    children: tuple[Instructionish, ...] | None = attrs.field(default=None)
    title: str | None = attrs.field(default=None)
    preferred: Expression | None = attrs.field(default=None)
    _type: Literal["Instruction.Instruction"] = attrs.field(
        default="Instruction.Instruction", repr=False
    )


InstructionOrInstructionGroup = Instruction | typing.ForwardRef(
    "InstructionGroup", is_argument=False
)


@defauto
class InstructionGroup:
    name: str
    encoding: Encodeset
    title: str | None = attrs.field(default=None)
    condition: Expression | None = attrs.field(default=None)
    children: tuple[InstructionOrInstructionGroup, ...] | None = attrs.field(default=None)
    operation_id: str | None = attrs.field(default=None)
    _type: Literal["Instruction.InstructionGroup"] = attrs.field(
        default="Instruction.InstructionGroup", repr=False
    )


@defauto
class InstructionSet:
    name: str
    encoding: Encodeset
    read_width: int
    condition: Expression | None = attrs.field(default=None)
    children: tuple[InstructionOrInstructionGroup, ...] | None = attrs.field(default=None)
    operation_id: str | None = attrs.field(default=None)
    _type: Literal["Instruction.InstructionSet"] = attrs.field(
        default="Instruction.InstructionSet", repr=False
    )


@defauto
class Operation:
    operation: str
    description: str
    brief: str
    title: str
    decode: str | None = attrs.field(default=None)
    _type: Literal["Instruction.Operation"] = attrs.field(
        default="Instruction.Operation", repr=False
    )


@defauto
class OperationAlias:
    operation_id: str
    description: str
    brief: str
    title: str
    _type: Literal["Instruction.OperationAlias"] = attrs.field(
        default="Instruction.OperationAlias", repr=False
    )


Operationish = Operation | OperationAlias


class Operations(dict[str, Operationish]):
    pass


@defauto
class Instructions:
    instructions: tuple[InstructionSet, ...]
    operations: Operations
    _type: Literal["Instruction.Instructions"] = attrs.field(
        default="Instruction.Instructions", repr=False
    )


JSONSchemaObject = (
    Encodeset
    | EncodesetBits
    | EncodesetField
    | EncodsetShouldBeBits
    | Expression
    | Identifier
    | Instruction
    | InstructionAlias
    | InstructionGroup
    | InstructionInstance
    | Instructions
    | InstructionSet
    | Operation
    | OperationAlias
    | Range
    | Trits
)

JSONSchemaObjectClasses = (
    BinaryOp,
    Bool,
    Encodeset,
    EncodesetBits,
    EncodesetField,
    EncodsetShouldBeBits,
    Function,
    Identifier,
    Instruction,
    InstructionAlias,
    InstructionGroup,
    InstructionInstance,
    Instructions,
    InstructionSet,
    Operation,
    OperationAlias,
    Range,
    Set,
    Trits,
    UnaryOp,
    Value,
)


def _resolve_json_schema_obj_cls_types():
    for cls in JSONSchemaObjectClasses:
        ct = typing.cast(type, cls)
        attrs.resolve_types(ct)


_resolve_json_schema_obj_cls_types()

converter = Converter()
converter.detailed_validation = True


def structure_trit(trit_str: str, cls: type[Trits]) -> Trits:
    if not issubclass(cls, Trits):
        raise TypeError(f"got cls {cls} not Trits")
    return Trits(trit_str)


converter.register_structure_hook(Trits, structure_trit)
