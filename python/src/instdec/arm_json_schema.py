from __future__ import annotations

import enum
import typing
from typing import Literal

import attrs
import rich.repr
from cattrs import Converter

from .trits import Trits
from .util import Span, defauto


class BinOp(enum.StrEnum):
    AND = "&&"
    NE = "!="
    EQ = "=="
    OR = "||"
    IN = "IN"
    IMPLIES = "-->"
    IFF = "<->"

    def __repr__(self) -> str:
        return f"<{self.__class__.__name__}.{self._name_}>"


class UnOp(enum.StrEnum):
    NOT = "!"

    def __repr__(self) -> str:
        return f"<{self.__class__.__name__}.{self._name_}>"


seen_value_meanings: set[str] = set()
seen_value_values: set[Trits] = set()


@attrs.define(auto_attribs=True, on_setattr=None, frozen=True)
class Value:
    value: Trits  # = attrs.field(repr=lambda v: v.trits)
    meaning: str | None = attrs.field(repr=False)  # always observed as null
    _type: Literal["Values.Value"] = attrs.field(default="Values.Value", repr=False)

    def __attrs_post_init__(self):
        seen_value_meanings.add(self.meaning)
        seen_value_values.add(self.value)
        if self.meaning is not None:
            raise NotImplementedError(f"finally a release with non-null `meaning`? Value: {self}")

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.value.trits
        yield len(self.value)

    def __repr__(self) -> str:
        return f"Value({len(self.value)}:'{self.value.trits}')"


seen_identifiers: set[str] = set()


@defauto
class Identifier:
    value: str
    _type: Literal["AST.Identifier"] = attrs.field(default="AST.Identifier", repr=False)

    def __attrs_post_init__(self):
        seen_identifiers.add(self.value)

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.value


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

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.name
        yield None, self.arguments


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

    def __rich_repr__(self) -> rich.repr.Result:
        yield "s", self.start
        yield "w", self.width
        yield "e", self.end


@defauto
class EncodesetBase:
    value: Value
    range: Range
    should_be_mask: Value

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.value
        yield self.range
        yield "sbm", self.should_be_mask


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

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.name
        yield from super().__rich_repr__()


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
    width: int = attrs.field(repr=False)
    parent: str
    _type: Literal["Instruction.Encodeset.Encodeset"] = attrs.field(
        default="Instruction.Encodeset.Encodeset", repr=False
    )

    def __rich_repr__(self) -> rich.repr.Result:
        yield "parent", self.parent
        yield from self.values

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
    condition: Expression | None = None
    children: tuple[InstructionInstance, ...] | None = None
    _type: Literal["Instruction.InstructionInstance"] = attrs.field(
        default="Instruction.InstructionInstance", repr=False
    )


@defauto
class InstructionAlias:
    name: str
    operation_id: str
    condition: Expression | None = None
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
    parent: str
    operation_id: str
    encoding: Encodeset
    condition: Expression | None = None
    children: tuple[Instructionish, ...] | None = None
    title: str | None = None
    preferred: Expression | None = None
    _type: Literal["Instruction.Instruction"] = attrs.field(
        default="Instruction.Instruction", repr=False
    )

    @property
    def path(self) -> str:
        return self.parent + "." + self.name

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.name
        yield (
            "op_id",
            self.operation_id,
        )
        yield "parent", self.parent
        yield self.encoding
        yield "cond", self.condition
        if self.children and len(self.children):
            yield "children", self.children
        yield "title", self.title, None
        yield "pref", self.preferred, None


InstructionOrInstructionGroup = Instruction | typing.ForwardRef(
    "InstructionGroup", is_argument=False
)


@defauto
class InstructionGroup:
    name: str
    parent: str
    encoding: Encodeset
    title: str | None = None
    condition: Expression | None = None
    children: tuple[InstructionOrInstructionGroup, ...] | None = None
    operation_id: str | None = None
    _type: Literal["Instruction.InstructionGroup"] = attrs.field(
        default="Instruction.InstructionGroup", repr=False
    )

    @property
    def path(self) -> str:
        return self.parent + "." + self.name


@defauto
class InstructionSet:
    name: str
    encoding: Encodeset
    read_width: int
    condition: Expression | None = None
    children: tuple[InstructionOrInstructionGroup, ...] | None = None
    operation_id: str | None = None
    _type: Literal["Instruction.InstructionSet"] = attrs.field(
        default="Instruction.InstructionSet", repr=False
    )

    @property
    def path(self) -> str:
        return self.name


@defauto
class Operation:
    operation: str
    description: str
    brief: str
    title: str
    decode: str | None = None
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


def structure_instructionset(iset_dict: dict, cls: type[InstructionSet]) -> InstructionSet:
    if not issubclass(cls, InstructionSet):
        raise TypeError(f"got cls {cls} not InstructionSet")
    eset_kwargs = iset_dict["encoding"]
    eset_kwargs["type"] = eset_kwargs["_type"]
    del eset_kwargs["_type"]
    eset_kwargs["parent"] = iset_dict["name"]
    iset_dict["encoding"] = Encodeset(**iset_dict["encoding"])
    iset_dict["type"] = iset_dict["_type"]
    del iset_dict["_type"]
    return InstructionSet(**iset_dict)


converter.register_structure_hook(InstructionSet, structure_instructionset)


def structure_trit(trit_str: str, cls: type[Trits]) -> Trits:
    if not issubclass(cls, Trits):
        raise TypeError(f"got cls {cls} not Trits")
    return Trits(trit_str)


converter.register_structure_hook(Trits, structure_trit)
