from __future__ import annotations

import enum
import typing
from typing import Literal

import attrs
import rich.repr
from cattrs import Converter
from rich import print

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
    _type: Literal["Values.Value"] = attrs.field(default="Values.Value", repr=False, alias="_type")

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
    _type: Literal["AST.Identifier"] = attrs.field(
        default="AST.Identifier", repr=False, alias="_type"
    )

    def __attrs_post_init__(self):
        seen_identifiers.add(self.value)

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.value


@defauto
class Bool:
    value: bool
    _type: Literal["AST.Bool"] = attrs.field(default="AST.Bool", repr=False, alias="_type")

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.value


@defauto
class Set:
    values: tuple[Value, ...]
    _type: Literal["AST.Set"] = attrs.field(default="AST.Set", repr=False, alias="_type")

    @property
    def values_set(self) -> set[Value]:
        rs: set[Value] = set(self.values)
        if len(self.values) != len(rs):
            raise ValueError(f"duplicate detected in AST.Set: {self}")
        return rs

    def __rich_repr__(self) -> rich.repr.Result:
        yield from self.values


@defauto
class BinaryOp:
    left: Expression
    op: BinOp
    right: Expression
    _type: Literal["AST.BinaryOp"] = attrs.field(default="AST.BinaryOp", repr=False, alias="_type")


@defauto
class UnaryOp:
    expr: Expression
    op: UnOp
    _type: Literal["AST.UnaryOp"] = attrs.field(default="AST.UnaryOp", repr=False, alias="_type")


seen_function_names: set[str] = set()


@defauto
class Function:
    name: str
    arguments: tuple[Expression, ...]
    _type: Literal["AST.Function"] = attrs.field(default="AST.Function", repr=False, alias="_type")

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
    _type: Literal["Range"] = attrs.field(default="Range", repr=False, alias="_type")

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

    @property
    def span(self) -> Span:
        return self.range.span

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.value
        yield self.range
        yield "sbm", self.should_be_mask


@defauto
class EncodesetBits(EncodesetBase):
    _type: Literal["Instruction.Encodeset.Bits"] = attrs.field(
        default="Instruction.Encodeset.Bits", repr=False, alias="_type"
    )


@defauto
class EncodesetField(EncodesetBase):
    name: str
    _type: Literal["Instruction.Encodeset.Field"] = attrs.field(
        default="Instruction.Encodeset.Field", repr=False, alias="_type"
    )

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.name
        yield from super().__rich_repr__()


@defauto
class EncodsetShouldBeBits:
    value: Value
    range: Range
    _type: Literal["Instruction.Encodeset.ShouldBeBits"] = attrs.field(
        default="Instruction.Encodeset.ShouldBeBits", repr=False, alias="_type"
    )

    @property
    def span(self) -> Span:
        raise NotImplementedError("deprecated object *and* not available")

    def __attrs_post_init__(self):
        raise NotImplementedError("deprecated object")


EncodesetValues = EncodesetBits | EncodesetField | EncodsetShouldBeBits


# If part of an Encodeset is unspecified in both the current instruction node and all of
# its parent nodes, that part is considered to be an
# "any-bit" ('1' or '0', usually denoted as 'x').

# If part of the local Encodeset is unspecified but that same part has a value specified
# in a parent node, the value of that part is inherited in the local Encodeset.


@defauto
class Encodeset:
    values: tuple[EncodesetValues, ...]
    width: int = attrs.field(repr=False)
    parent: str
    _type: Literal["Instruction.Encodeset.Encodeset"] = attrs.field(
        default="Instruction.Encodeset.Encodeset", repr=False, alias="_type"
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

    @property
    def spans(self) -> list[Span]:
        spans = [v.span for v in self.values]
        sorted_spans = sorted(spans, reverse=True)
        if tuple(spans) != tuple(sorted_spans):
            print("spans:")
            print(spans)
            print("sorted_spans:")
            print(sorted_spans)
            raise ValueError(f"got unsorted spans in Encodeset. Is this unexpected? self: {self}")
        return spans

    @property
    def bitmask(self) -> int:
        return 0

    @property
    def bitpattern(self) -> int:
        return 0

    @property
    def ne_bitmask(self) -> int:
        return 0

    @property
    def ne_bitpattern(self) -> int:
        return 0


@defauto
class InstructionInstance:
    name: str
    condition: Expression | None = None
    children: tuple[InstructionInstance, ...] | None = None
    _type: Literal["Instruction.InstructionInstance"] = attrs.field(
        default="Instruction.InstructionInstance", repr=False, alias="_type"
    )

    def __attrs_post_init__(self):
        raise NotImplementedError("They added InstructionInstance?")


@defauto
class InstructionAlias:
    name: str
    operation_id: str
    condition: Expression | None = None
    # assembly: ?
    _type: Literal["Instruction.InstructionAlias"] = attrs.field(
        default="Instruction.InstructionAlias", repr=False, alias="_type"
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
        default="Instruction.Instruction", repr=False, alias="_type"
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
        default="Instruction.InstructionGroup", repr=False, alias="_type"
    )

    @property
    def path(self) -> str:
        return self.parent + "." + self.name

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.name
        yield "parent", self.parent
        yield "operation_id", self.operation_id, None
        yield self.encoding
        yield "cond", self.condition
        if self.children and len(self.children):
            yield "children", self.children
        yield "title", self.title, None


@defauto
class InstructionSet:
    name: str
    encoding: Encodeset
    read_width: int
    condition: Expression | None = None
    children: tuple[InstructionOrInstructionGroup, ...] | None = None
    operation_id: str | None = None
    _type: Literal["Instruction.InstructionSet"] = attrs.field(
        default="Instruction.InstructionSet", repr=False, alias="_type"
    )

    @property
    def path(self) -> str:
        return self.name

    def __rich_repr__(self) -> rich.repr.Result:
        yield self.name
        yield "read_width", self.read_width
        yield "operation_id", self.operation_id, None
        yield self.encoding
        yield "cond", self.condition
        if self.children and len(self.children):
            yield "children", self.children


@defauto
class Operation:
    operation: str
    brief: str
    title: str
    decode: str | None = None
    description: str | None = None
    _type: Literal["Instruction.Operation"] = attrs.field(
        default="Instruction.Operation", repr=False, alias="_type"
    )

    def __rich_repr__(self) -> rich.repr.Result:
        yield "op", self.operation, "// Not specified"
        yield "title", self.title, ""
        yield "brief", self.brief, "."
        yield "desc", self.description, None
        yield "decode", self.decode, None


@defauto
class OperationAlias:
    operation_id: str
    brief: str
    title: str
    description: str | None = None
    _type: Literal["Instruction.OperationAlias"] = attrs.field(
        default="Instruction.OperationAlias", repr=False, alias="_type"
    )

    def __rich_repr__(self) -> rich.repr.Result:
        yield "op_id", self.operation_id
        yield "title", self.title, ""
        yield "brief", self.brief, "."
        yield "desc", self.description, None


Operationish = Operation | OperationAlias


class Operations(dict[str, Operationish]):
    pass


@defauto
class Instructions:
    instructions: tuple[InstructionSet, ...]
    operations: Operations
    _type: Literal["Instruction.Instructions"] = attrs.field(
        default="Instruction.Instructions", repr=False, alias="_type"
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


def _add_cattrs_hooks():
    def structure_operations(ops_dict: dict, cls: type[Operations]) -> Trits:
        if not issubclass(cls, Operations):
            raise TypeError(f"got cls {cls} not Operations")
        for k in ops_dict.keys():
            ops_dict[k] = converter.structure(ops_dict[k], Operationish)
        return Operations(**ops_dict)

    converter.register_structure_hook(Operations, structure_operations)

    def structure_instructionset(iset_dict: dict, cls: type[InstructionSet]) -> InstructionSet:
        if not issubclass(cls, InstructionSet):
            raise TypeError(f"got cls {cls} not InstructionSet")

        my_name = iset_dict["name"]
        iset_dict["encoding"]["parent"] = my_name
        for child_json in iset_dict["children"]:
            child_json["parent"] = my_name

        # Structure each attribute individually
        attrs_dict = {}
        for field in attrs.fields(InstructionSet):
            if field.name in iset_dict:
                # Use converter.structure to handle nested types for this field's value
                attrs_dict[field.name] = converter.structure(iset_dict[field.name], field.type)

        # Create and return the InstructionSet instance
        return InstructionSet(**attrs_dict)

    converter.register_structure_hook(InstructionSet, structure_instructionset)

    def structure_instructiongroup(
        igrp_dict: dict, cls: type[InstructionGroup]
    ) -> InstructionGroup:
        if not issubclass(cls, InstructionGroup):
            raise TypeError(f"got cls {cls} not InstructionGroup")

        my_name = igrp_dict["parent"] + "." + igrp_dict["name"]
        igrp_dict["encoding"]["parent"] = my_name
        for child_json in igrp_dict["children"]:
            child_json["parent"] = my_name

        attrs_dict = {}
        for field in attrs.fields(InstructionGroup):
            if field.name in igrp_dict:
                attrs_dict[field.name] = converter.structure(igrp_dict[field.name], field.type)

        return InstructionGroup(**attrs_dict)

    converter.register_structure_hook(InstructionGroup, structure_instructiongroup)

    def structure_instruction(instr_dict: dict, cls: type[Instruction]) -> Instruction:
        if not issubclass(cls, Instruction):
            raise TypeError(f"got cls {cls} not Instruction")

        my_name = instr_dict["parent"] + "." + instr_dict["name"]
        instr_dict["encoding"]["parent"] = my_name
        for child_json in instr_dict["children"]:
            child_json["parent"] = my_name

        attrs_dict = {}
        for field in attrs.fields(Instruction):
            if field.name in instr_dict:
                attrs_dict[field.name] = converter.structure(instr_dict[field.name], field.type)

        return Instruction(**attrs_dict)

    converter.register_structure_hook(Instruction, structure_instruction)

    def structure_trit(trit_str: str, cls: type[Trits]) -> Trits:
        if not issubclass(cls, Trits):
            raise TypeError(f"got cls {cls} not Trits")
        return Trits(trit_str)

    converter.register_structure_hook(Trits, structure_trit)


_add_cattrs_hooks()


def deserialize_instructions_json(instr_json: dict) -> Instructions:
    deser = converter.structure(instr_json, Instructions)
    if not isinstance(deser, Instructions):
        raise TypeError(f"Didn't get Instructions, got {type(deser)}")
    return deser
