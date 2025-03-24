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
    meaning: str | None
    _type: Literal["Values.Value"] = "Values.Value"

    def __attrs_post_init__(self):
        seen_value_meanings.add(self.meaning)
        seen_value_values.add(self.value)


seen_identifiers: set[str] = set()


@defauto
class Identifier:
    value: str
    _type: Literal["AST.Identifier"] = "AST.Identifier"

    def __attrs_post_init__(self):
        seen_identifiers.add(self.value)


@defauto
class Bool:
    value: bool
    _type: Literal["AST.Bool"] = "AST.Bool"


@defauto
class Set:
    values: tuple[Value, ...]
    _type: Literal["AST.Set"] = "AST.Set"

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
    _type: Literal["AST.BinaryOp"] = "AST.BinaryOp"


@defauto
class UnaryOp:
    expr: Expression
    op: UnOp
    _type: Literal["AST.UnaryOp"] = "AST.UnaryOp"


seen_function_names: set[str] = set()


@defauto
class Function:
    name: str
    arguments: tuple[Expression, ...]
    _type: Literal["AST.Function"] = "AST.Function"

    def __attrs_post_init__(self):
        seen_function_names.add(self.name)


# Define Expression as a union of all possible AST node types
Expression = Bool | BinaryOp | Function | Identifier | Set | UnaryOp | Value
Valueish = Value | Set


@defauto
class Range:
    start: int
    width: int
    _type: Literal["Range"] = "Range"

    @property
    def end(self) -> int:
        return self.start + self.width

    @property
    def span(self) -> Span:
        return Span(self.start, self.width)


@defauto
class EncodesetBits:
    value: Value
    range: Range
    should_be_mask: Value
    _type: Literal["Instruction.Encodeset.Bits"] = "Instruction.Encodeset.Bits"


@defauto
class EncodesetField:
    name: str
    range: Range
    value: Value
    should_be_mask: Value
    _type: Literal["Instruction.Encodeset.Field"] = "Instruction.Encodeset.Field"


@defauto
class EncodsetShouldBeBits:
    value: Value
    range: Range
    _type: Literal["Instruction.Encodeset.ShouldBeBits"] = "Instruction.Encodeset.ShouldBeBits"

    def __attrs_post_init__(self):
        raise NotImplementedError("deprecated object")


EncodesetValues = EncodesetBits | EncodesetField | EncodsetShouldBeBits


@defauto
class Encodeset:
    values: tuple[EncodesetValues, ...]
    width: int
    _type: Literal["Instruction.Encodeset.Encodeset"] = "Instruction.Encodeset.Encodeset"

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
    _type: Literal["Instruction.InstructionInstance"] = "Instruction.InstructionInstance"


@defauto
class InstructionAlias:
    name: str
    operation_id: str
    condition: Expression | None = attrs.field(default=None)
    # assembly: ?
    _type: Literal["Instruction.InstructionAlias"] = "Instruction.InstructionAlias"


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
    _type: Literal["Instruction.Instruction"] = "Instruction.Instruction"


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
    _type: Literal["Instruction.InstructionGroup"] = "Instruction.InstructionGroup"


@defauto
class InstructionSet:
    name: str
    encoding: Encodeset
    read_width: int
    condition: Expression | None = attrs.field(default=None)
    children: tuple[InstructionOrInstructionGroup, ...] | None = attrs.field(default=None)
    operation_id: str | None = attrs.field(default=None)
    _type: Literal["Instruction.InstructionSet"] = "Instruction.InstructionSet"


@defauto
class Operation:
    operation: str
    description: str
    brief: str
    title: str
    decode: str | None = attrs.field(default=None)
    _type: Literal["Instruction.Operation"] = "Instruction.Operation"


@defauto
class OperationAlias:
    operation_id: str
    description: str
    brief: str
    title: str
    _type: Literal["Instruction.OperationAlias"] = "Instruction.OperationAlias"


Operationish = Operation | OperationAlias


class Operations(dict[str, Operationish]):
    pass


@defauto
class Instructions:
    instructions: tuple[InstructionSet, ...]
    operations: Operations
    _type: Literal["Instruction.Instructions"] = "Instruction.Instructions"


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
    InstructionInstance,
    InstructionAlias,
    InstructionGroup,
    Instructions,
    InstructionSet,
    Range,
    Set,
    Trits,
    UnaryOp,
    Value,
    Operation,
    OperationAlias,
)

for cls in JSONSchemaObjectClasses:
    ct = typing.cast(type, cls)
    attrs.resolve_types(ct, globals(), locals())

converter = Converter()
converter.detailed_validation = True


def structure_trit(trit_str: str, cls: type[Trits]) -> Trits:
    if not issubclass(cls, Trits):
        raise TypeError(f"got cls {cls} not Trits")
    return Trits(trit_str)


converter.register_structure_hook(Trits, structure_trit)
