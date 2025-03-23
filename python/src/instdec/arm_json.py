from __future__ import annotations

import enum
import typing
from collections.abc import Callable
from typing import Any, Literal

import attrs
import cattrs
import cattrs.strategies
import rich
from cattrs import Converter

# from rich import print
from .trits import TritRange, TritRanges, Trits
from .util import Span, TagBase, defauto, traverse_nested


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


# @tag("Value.Value")
@defauto
class Value(TagBase):
    _type: Literal["Value.Value"]
    value: Trits
    meaning: str | None

    def __attrs_post_init__(self):
        seen_value_meanings.add(self.meaning)
        seen_value_values.add(self.value)


seen_identifiers: set[str] = set()


# @tag("AST.Identifier")
@defauto
class Identifier(TagBase):
    _type: Literal["AST.Identifier"]
    value: str

    def __attrs_post_init__(self):
        seen_identifiers.add(self.value)


# @tag("AST.Bool")
@defauto
class Bool(TagBase):
    _type: Literal["AST.Bool"]
    value: bool


# @tag("AST.Set")
@defauto
class Set(TagBase):
    _type: Literal["AST.Set"]
    values: set[Value]


# @tag("AST.BinaryOp")
@defauto
class BinaryOp(TagBase):
    _type: Literal["AST.BinaryOp"]
    left: Expression
    op: BinOp
    right: Expression


# @tag("AST.UnaryOp")
@defauto
class UnaryOp(TagBase):
    _type: Literal["AST.UnaryOp"]
    expr: Expression
    op: UnOp


seen_function_names: set[str] = set()


# @tag("AST.Function")
@defauto
class Function(TagBase):
    _type: Literal["AST.Function"]
    name: str
    arguments: list[Expression]

    def __attrs_post_init__(self):
        seen_function_names.add(self.name)


# Define Expression as a union of all possible AST node types
Expression = Bool | BinaryOp | Function | Identifier | Set | UnaryOp | Value
Valueish = Value | Set


def expr_has_ident(expr: Expression | None, ident: str) -> bool:
    if expr is None:
        return False
    if isinstance(expr, BinaryOp):
        return expr_has_ident(expr.left, ident) or expr_has_ident(expr.right, ident)
    elif isinstance(expr, UnaryOp):
        return expr_has_ident(expr.expr, ident)
    elif isinstance(expr, Identifier):
        return expr.value == ident
    else:
        return False


# @tag("Range")
@defauto
class Range(TagBase):
    _type: Literal["Range"]
    start: int
    width: int

    @property
    def end(self) -> int:
        return self.start + self.width

    @property
    def span(self) -> Span:
        return Span(self.start, self.width)


# @tag("Instruction.Encodeset.Bits")
@defauto
class EncodesetBits(TagBase):
    _type: Literal["Instruction.Encodeset.Bits"]
    value: Value
    range: Range
    should_be_mask: Value


# @tag("Instruction.Encodeset.Field")
@defauto
class EncodesetField(TagBase):
    _type: Literal["Instruction.Encodeset.Field"]
    name: str
    range: Range
    value: Value
    should_be_mask: Value


# @tag("Instruction.Encodeset.ShouldBeBits")
@defauto
class EncodsetShouldBeBits(TagBase):
    _type: Literal["Instruction.Encodeset.ShouldBeBits"]
    value: Value
    range: Range


EncodesetValues = EncodesetBits | EncodesetField | EncodsetShouldBeBits


# @tag("Instruction.Encodeset.Encodeset")
@defauto
class Encodeset(TagBase):
    _type: Literal["Instruction.Encodeset.Encodeset"]
    values: list[EncodesetValues]
    width: int

    def get_field(self, name: str) -> EncodesetField | None:
        matches: list[EncodesetField] = []
        for v in self.values:
            if isinstance(v, EncodesetField):
                if v.name == name:
                    matches.append(v)
        if len(matches) > 1:
            raise ValueError(
                f"have multiple results for Encodeset.Field '{name}' results: {matches}"
            )
        if len(matches) == 0:
            return None
        return matches[0]

    def has_field(self, name: str) -> bool:
        return self.get_field(name) is not None


# @tag("Instruction.InstructionInstance")
@defauto
class InstructionInstance(TagBase):
    _type: Literal["Instruction.InstructionInstance"]
    name: str
    condition: Expression | None = attrs.field(default=None)
    children: list[InstructionInstance] | None = attrs.field(default=None)


# @tag("Instruction.InstructionAlias")
@defauto
class InstructionAlias(TagBase):
    _type: Literal["Instruction.InstructionAlias"]
    name: str
    operation_id: str
    condition: Expression | None = attrs.field(default=None)
    # assembly: ?


Instructionish = (
    typing.ForwardRef("Instruction", is_argument=False) | InstructionInstance | InstructionAlias
)


# @tag("Instruction.Instruction")
@defauto
class Instruction(TagBase):
    _type: Literal["Instruction.Instruction"]
    name: str
    operation_id: str
    encoding: Encodeset
    condition: Expression | None = attrs.field(default=None)
    children: list[Instructionish] | None = attrs.field(default=None)
    title: str | None = attrs.field(default=None)
    preferred: Expression | None = attrs.field(default=None)


InstructionOrInstructionGroup = Instruction | typing.ForwardRef(
    "InstructionGroup", is_argument=False
)


# @tag("Instruction.InstructionGroup")
@defauto
class InstructionGroup(TagBase):
    _type: Literal["Instruction.InstructionGroup"]
    name: str
    encoding: Encodeset
    title: str | None = attrs.field(default=None)
    condition: Expression | None = attrs.field(default=None)
    children: list[InstructionOrInstructionGroup] | None = attrs.field(default=None)
    operation_id: str | None = attrs.field(default=None)


# @tag("Instruction.InstructionSet")
@defauto
class InstructionSet(TagBase):
    _type: Literal["Instruction.InstructionSet"]
    name: str
    encoding: Encodeset
    read_width: int
    condition: Expression | None = attrs.field(default=None)
    children: list[InstructionOrInstructionGroup] | None = attrs.field(default=None)
    operation_id: str | None = attrs.field(default=None)


# @tag("Instruction.Operation")
@defauto
class Operation(TagBase):
    _type: Literal["Instruction.Operation"]
    operation: str
    description: str
    brief: str
    title: str
    decode: str | None = attrs.field(default=None)


# @tag("Instruction.OperationAlias")
@defauto
class OperationAlias(TagBase):
    _type: Literal["Instruction.OperationAlias"]
    operation_id: str
    description: str
    brief: str
    title: str


Operationish = Operation | OperationAlias


# @tag("Operations")
# @defauto
# class Operations(TagBase):
#     _type: Literal["Operations"]
#     ops: dict[str, Operationish]


class Operations(dict[str, Operationish]):
    pass


# @tag("Instruction.Instructions")
@defauto
class Instructions(TagBase):
    _type: Literal["Instruction.Instructions"]
    instructions: list[InstructionSet]
    operations: Operations


JSONSchemaObject = typing.Union[
    Encodeset,
    EncodesetBits,
    EncodesetField,
    EncodsetShouldBeBits,
    Expression,
    Identifier,
    Instruction,
    InstructionInstance,
    InstructionAlias,
    InstructionGroup,
    Instructions,
    InstructionSet,
    Range,
    Trits,
    Operation,
    OperationAlias,
]

TheTypes = (
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
    Valueish,
    InstructionOrInstructionGroup,
    Instructionish,
    Operationish,
    Operation,
    OperationAlias,
)

for i in range(7):
    for t in TheTypes:
        try:
            typing.get_type_hints(t, globalns=globals(), localns=locals())
        except Exception:
            # print(f"did {t} got {e}")
            pass

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

# Set up cattrs converter with a custom structure hook
converter = Converter()
converter.detailed_validation = True


def structure_operations(obj: dict[str, dict], cls: type[Operations]) -> Operations:
    if not issubclass(cls, Operations):
        raise TypeError(f"got cls {cls} not Operations")
    result: dict[str, Operationish] = dict()
    for key, value in obj.items():
        # Determine the type based on the _type field and structure accordingly
        # ty = value.get("_type")
        ty = value.get("_type")
        if ty is None:
            ty = value.get("_type")
            # print(f"structure_operations _type none ty: {ty}")
        if ty == "Instruction.Operation":
            result[key] = converter.structure(value, Operation)
        elif ty == "Instruction.OperationAlias":
            result[key] = converter.structure(value, OperationAlias)
        else:
            raise ValueError(f"Unknown operation type: {ty} val: {value}")
    print(f"structure_operations res: {result}")
    return cls(ops=result)


# Register a custom structure hook for Operations
converter.register_structure_hook(Operations, structure_operations)


def structure_identifier(obj: str, cls: type[Identifier]) -> Identifier:
    if not issubclass(cls, Identifier):
        raise TypeError(f"got cls {cls} not Identifier")
    print(f"structure_identifier obj: '{obj}' cls: {cls}")
    return cls(obj)


# converter.register_structure_hook(Identifier, structure_identifier)


def my_tag_generator(cls: type[TagBase]) -> str:
    if not hasattr(cls, "_type"):
        rich.inspect(cls, all=True)
        print(f"my_tag_generator cls: {cls} type: {type(cls)}")
        raise ValueError(f"cls has no _type attribute. cls: {cls}")
    if not isinstance(cls, type):
        raise TypeError(f"not type got {type(cls)} instead")
    if not issubclass(cls, TagBase):
        raise TypeError(f"cls not TagBase type(cls): {type(cls)} cls: {cls}")
    anno = cls.__annotations__["_type"]
    # anno_trimmed = (
    #     anno.removeprefix("typing.Literal['").removeprefix("Literal['").removesuffix("']")
    # )
    anno_trimmed = anno
    print(f"my_tag_generator cls: {cls} tag: {cls._type} anno: {anno} anno_trimmed: {anno_trimmed}")
    # rich.inspect(cls, all=True)
    # rich.inspect(cls._type, all=True)
    # rich.inspect(cls.__annotations__["_type"], all=True)
    return anno_trimmed


cattrs.strategies.configure_tagged_union(
    Identifier | Value, converter, tag_generator=my_tag_generator
)

cattrs.strategies.configure_tagged_union(
    Instruction | InstructionInstance | InstructionAlias, converter, tag_generator=my_tag_generator
)

cattrs.strategies.configure_tagged_union(
    Instruction | InstructionGroup, converter, tag_generator=my_tag_generator
)

# converter.register_structure_hook(JSONSchemaObject, structure_json_schema)
cattrs.strategies.configure_tagged_union(
    JSONSchemaObject, converter, tag_generator=my_tag_generator
)


def structure_trit(obj: str, cls: type[Trits]) -> Trits:
    if not issubclass(cls, Trits):
        raise TypeError(f"got cls {cls} not Trits")
    # print(f"structure_trit obj: '{obj}' cls: {cls}")
    return Trits(obj, "Trits")


converter.register_structure_hook(Trits, structure_trit)


class ExprRef:
    def __init__(self, node):
        self.node = node

    def __repr__(self):
        # Only display a summary: id and keys of the dict
        return f"<ExprRef id={id(self.node)} keys={list(self.node.keys())}>"


@attrs.define(auto_attribs=True)
class Interpteter:
    ast: Expression

    def evaluate(self) -> Valueish:
        cur_node = self.ast
        try:
            if isinstance(cur_node, Function):
                return self.eval_func(cur_node)
            elif isinstance(cur_node, BinaryOp):
                lv = Interpteter(cur_node.left).evaluate()
                rv = Interpteter(cur_node.right).evaluate()
                if isinstance(lv, Set):
                    raise ValueError("eval BinaryOp lv is Set")
                if isinstance(rv, Set):
                    raise ValueError("eval BinaryOp rv is Set")
                return self.eval_binop(cur_node, lv, rv)
            elif isinstance(cur_node, UnaryOp):
                ov = Interpteter(cur_node.expr).evaluate()
                if isinstance(ov, Set):
                    raise ValueError("eval UnaryOp ov is Set")
                return self.eval_unop(cur_node, ov)
            elif isinstance(cur_node, Bool):
                return self.eval_bool(cur_node)
            elif isinstance(cur_node, Identifier):
                return self.eval_id(cur_node)
            elif isinstance(cur_node, (Value, Set)):
                return cur_node
            else:
                raise NotImplementedError(
                    f"Interpteter.evaluate '{type(cur_node)}' unhandled\nast: {self.ast}"
                )
        except Exception as e:
            print(f"eval got exc: {e}\ncur ast: {cur_node}")
            raise e

    def eval_func(self, cur_node: Function) -> Value:
        n = cur_node.name
        if n == "IsFeatureImplemented":
            return Value(meaning=n, value=Trits("X"))
        else:
            raise NotImplementedError(f"AST.Function eval but '{n}' unhandled")

    def eval_binop(self, cur_node: BinaryOp, left: Value, right: Value) -> Value:
        op = cur_node.op
        if op == BinOp.AND:
            nv = left.value.and_(right.value)
            return Value(meaning="AND", value=nv)
        elif op == BinOp.OR:
            nv = left.value.or_(right.value)
            return Value(meaning="OR", value=nv)
        elif op == BinOp.EQ:
            nv = left.value.eq_(right.value)
            return Value(meaning="EQ", value=nv)
        elif op == BinOp.NE:
            if (
                isinstance(left, Identifier)
                and left.value == "Rm"
                and isinstance(right, Value)
                and right.value == Trits("11111")
            ):
                return Value(meaning="FORCE_RM_NE_1S", value=Trits("1"))
            nv = left.value.ne_(right.value)
            return Value(meaning="NE", value=nv)
        elif op == BinOp.IN:
            if not isinstance(right, Set):
                raise ValueError(
                    f"righthand operator to IN isn't set. cur_node: {cur_node} left: {left}, right: {right}"
                )
            lv = left.value
            tt = Trits("1")
            for rv in right.values:
                if lv.eq_(rv.value) == tt:
                    return Value(meaning="IN-TRUE", value=Trits("1"))
            return Value(meaning="IN-FALSE", value=Trits("0"))
        else:
            raise ValueError(f"eval_binop unhandled op: {op} cur_node: {cur_node}")

    def eval_unop(self, cur_node: UnaryOp, val: Value) -> Value:
        op = cur_node.op
        if op == UnOp.NOT:
            return Value(meaning="NOT", value=val.value.not_())
        else:
            raise ValueError(f"eval_unop unhandled op: '{op}' cur_node: {cur_node} val: {val}")

    def eval_bool(self, cur_node: Bool) -> Value:
        if cur_node.value:
            return Value(meaning="Bool", value=Trits("1"))
        else:
            return Value(meaning="Bool", value=Trits("0"))

    def eval_id(self, cur_node: Identifier) -> Value:
        return Value(meaning=f"ID.{cur_node.value}", value=Trits("X"))


def find_encodings(node, context=None, path=""):
    if context is None:
        context = []

    results = []

    if isinstance(node, dict):
        # Work on a copy of the current context for this branch
        current_context = context.copy()

        if "encoding" in node:
            encoding_entry = {
                "encoding": node["encoding"],
                "context": current_context.copy(),  # Context as accumulated so far
                "path": path + ".encoding",
            }
            results.append(encoding_entry)
            # Append current node to the context, wrapping it with ExprRef to prevent recursive printing
            # current_context.append({"encoding": node["encoding"], "object": ExprRef(node)})
            current_context.append(
                {"encoding": node["encoding"], "object": node.get("name", "no_name")}
            )

        # Process the 'children' field if present.
        children = node.get("children", [])
        if isinstance(children, dict):
            children = [children]
        if isinstance(children, list):
            for idx, child in enumerate(children):
                results.extend(find_encodings(child, current_context, f"{path}.children[{idx}]"))

        # Optionally, process other keys containing dicts or lists.
        for key, value in node.items():
            if key != "children" and isinstance(value, (dict, list)):
                results.extend(find_encodings(value, context, f"{path}.{key}"))

    elif isinstance(node, list):
        for idx, item in enumerate(node):
            results.extend(find_encodings(item, context, f"{path}[{idx}]"))

    return results


def are_encodesets_consistent(a: dict, b: dict) -> bool:
    return False


# def constrain_instr(encset: En)


def find_leafs_helper(instrs: dict | list, encoding_stack: list | None = None) -> list:
    results = []
    if encoding_stack is None:
        encoding_stack = []
    if isinstance(instrs, dict):
        instrs = [instrs]
    assert isinstance(instrs, list)
    for x in instrs:
        if isinstance(x, dict):
            if "encoding" in x and (
                ("children" in x and len(x["children"]) == 0) or ("children" not in x)
            ):
                # we are leaf
                xc = x.copy()
                for band in ("assembly", "assemble"):
                    if band in xc:
                        del xc[band]
                xc["parent_encodings"] = encoding_stack.copy()
                results.append(xc)
                continue
            if "encoding" in x:
                assert x["encoding"]["_type"] == "Instruction.Encodeset.Encodeset"
                encoding_stack.append((x["name"], x["encoding"]))
            for k in x:
                if k == "children":
                    # future extension point
                    results += find_leafs_helper(x["children"], encoding_stack=encoding_stack)
                else:
                    v = x[k]
                    if isinstance(v, (list, dict)):
                        results += find_leafs_helper(v, encoding_stack=encoding_stack)
            if "encoding" in x:
                encoding_stack.pop()
        elif isinstance(x, list):
            results += find_leafs_helper(x, encoding_stack=encoding_stack)
    return results


def find_leafs(ijson: dict) -> list:
    instrsl = ijson["instructions"]
    if len(instrsl) != 1:
        raise ValueError("instructions list isn't size 1")
    instrs_root = instrsl[0]
    leafs = find_leafs_helper(instrs_root)
    return leafs


def parse_instruction_encoding(inst: dict) -> tuple[str, Trits, int, int, int]:
    """Parse instruction encoding into trits and counts.

    Args:
        inst: Instruction dictionary from JSON

    Returns:
        tuple of (name, Trits object, count_0, count_1, count_X)
    """
    enc = inst["encoding"]
    if "width" in enc and enc["width"] != 32:
        raise ValueError(f"inst enc width isn't 32 it is {enc['width']}")
    assert enc["_type"] == "Instruction.Encodeset.Encodeset"

    trit_ranges = TritRanges()
    for v in enc["values"]:
        assert v["_type"] in ("Instruction.Encodeset.Bits", "Instruction.Encodeset.Field")
        rng = v["range"]
        assert rng["_type"] == "Range"
        val = v["value"]
        assert val["_type"] == "Values.Value"

        start = rng["start"]
        width = rng["width"]
        end = start + width
        assert 0 <= start <= 31
        assert 1 <= end <= 32
        assert width > 0

        valval = val["value"].replace("'", "")
        sbmt = TritRange(start, width, Trits(valval))
        trit_ranges.add_range(sbmt)

    mtrits = trit_ranges.merge()
    mts = str(mtrits)
    return (inst["name"], mtrits, mts.count("0"), mts.count("1"), mts.count("X"))


def has_instructions_w_children(instrs: Instructions) -> bool:
    for iset in instrs.instructions:

        def check(o: Any, path: str) -> Any | None:
            if isinstance(o, Instruction):
                if (
                    hasattr(o, "children")
                    and o.children is not None
                    and len(o.children) != 0
                    and not all([isinstance(c, InstructionAlias) for c in o.children])
                ):
                    raise ValueError(f"found instr w/ children: {o}")
                    return o
            return None

        res = traverse_nested(iset.children, check)
        if res is not None:
            # raise ValueError(f"found instr w/ children:\n{res}")
            return True
    return False


@defauto
class ParseContext:
    set_encoding_stack: list[Encodeset] = attrs.Factory(list)
    set_condition_stack: list[Expression | None] = attrs.Factory(list)
    group_encoding_stack: list[Encodeset] = attrs.Factory(list)
    group_condition_stack: list[Expression | None] = attrs.Factory(list)
    group_name_stack: list[str] = attrs.Factory(list)
    obj_stack: list[JSONSchemaObject] = attrs.Factory(list)


InstrCB = Callable[[Instruction, ParseContext], None]


def recurse_instr_or_instr_group(
    il: list[InstructionOrInstructionGroup],
    ctx: ParseContext,
    cb: InstrCB,
    seen: set[int] | None = None,
) -> None:
    if seen is None:
        seen = set()
    for ioig in il:
        ctx.obj_stack.append(ioig)
        if id(ioig) in seen:
            if isinstance(ioig, list):
                raise TypeError("skipping from seen id list")
            elif isinstance(ioig, TagBase):
                raise TypeError(f"skipping from seen id type: {ioig._type}")
            else:
                raise TypeError("skipping from seen id OTHER")
            continue  # TODO: see if assertions are ever raisec
        if isinstance(ioig, Instruction):
            cb(ioig, ctx)
        else:
            if not isinstance(ioig, InstructionGroup):
                raise ValueError(f"ioig: {ioig}")
            ctx.group_encoding_stack.append(ioig.encoding)
            ctx.group_condition_stack.append(ioig.condition)
            ctx.group_name_stack.append(ioig.name)
            recurse_instr_or_instr_group(ioig.children, ctx, cb)
            ctx.group_name_stack.pop()
            ctx.group_condition_stack.pop()
            ctx.group_encoding_stack.pop()
        seen.add(id(ioig))
        ctx.obj_stack.pop()
    return


def instr_cb(i: Instruction, ctx: ParseContext) -> None:
    # print(f"i name stack: {'.'.join(ctx.group_name_stack)} ctx: {ctx}")
    s = f"os[-2].type: {ctx.obj_stack[-2]._type}"
    print(f"i name stack: {'.'.join(ctx.group_name_stack)} s: {s}")


def parse_instructions(instrs: Instructions, cb: InstrCB = instr_cb) -> None:
    ctx = ParseContext()
    ctx.obj_stack.append(instrs)

    for iset in instrs.instructions:
        ctx.obj_stack.append(iset)
        ctx.set_encoding_stack.append(iset.encoding)
        ctx.set_condition_stack.append(iset.condition)

        if iset.children is None:
            raise ValueError(f"iset name: {iset.name} children is None")

        recurse_instr_or_instr_group(iset.children, ctx, cb)

        ctx.set_condition_stack.pop()
        ctx.set_encoding_stack.pop()
        ctx.obj_stack.pop()

    ctx.obj_stack.pop()

    return


def dump_idents(instrs: Instructions) -> None:
    def dump_idents_instr_cb(i: Instruction, ctx: ParseContext) -> None:
        if expr_has_ident(i.condition, "Rm"):
            smth = i.encoding.get_field("Rm")
            print(f"smth: {smth}")
        return

    parse_instructions(instrs, dump_idents_instr_cb)
