from __future__ import annotations

import enum
import typing

import attrs
import cattrs
import cattrs.dispatch
import cattrs.strategies
from cattrs import Converter

from .trits import TritRange, TritRanges, Trits
from .util import defauto, tag


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


seen_identifiers: set[str] = set()


@tag("AST.Identifier")
@defauto
class Identifier:
    # valuex: str = attrs.field(alias="value")
    value: str
    _sentinel: str  # FIXME: this has to go, right? or a converter?

    def __attrs_post_init__(self):
        seen_identifiers.add(self.value)

    # @property
    # def value(self) -> str:
    #     return self.valuex


seen_value_meanings: set[str] = set()
seen_value_values: set[Trits] = set()


def str_none_nil_xfrm(v: str | None) -> str:
    return v if v is not None else "(nil)"


@tag("Value.Value")
@defauto
class Value:
    meaning: str = attrs.field(converter=str_none_nil_xfrm)
    value: Trits

    def __attrs_post_init__(self):
        seen_value_meanings.add(self.meaning)
        seen_value_values.add(self.value)


@tag("AST.Bool")
@defauto
class Bool:
    value: bool


@tag("AST.Set")
@defauto
class Set:
    values: set[Value]


@tag("AST.BinaryOp")
@defauto
class BinaryOp:
    left: Expression
    op: BinOp
    right: Expression


@tag("AST.UnaryOp")
@defauto
class UnaryOp:
    expr: Expression
    op: UnOp


seen_function_names: set[str] = set()


@tag("AST.Function")
@defauto
class Function:
    name: str
    arguments: list[Expression]

    def __attrs_post_init__(self):
        seen_function_names.add(self.name)


# Define Expression as a union of all possible AST node types
Expression = Bool | BinaryOp | Function | Identifier | Set | UnaryOp | Value
Valueish = Value | Set


@tag("Range")
@defauto
class Range:
    start: int
    width: int

    @property
    def end(self) -> int:
        return self.start + self.width


@tag("Instruction.Encodeset.Bits")
@defauto
class EncodesetBits:
    value: Value
    range: Range
    should_be_mask: Value


@tag("Instruction.Encodeset.Field")
@defauto
class EncodesetField:
    name: str
    range: Range
    value: Value
    should_be_mask: Value


@tag("Instruction.Encodeset.ShouldBeBits")
@defauto
class EncodsetShouldBeBits:
    value: Value
    range: Range


EncodesetValues = EncodesetBits | EncodesetField | EncodsetShouldBeBits


@tag("Instruction.Encodeset.Encodeset")
@defauto
class Encodeset:
    values: list[EncodesetValues]
    width: int


@tag("Instruction.InstructionInstance")
@defauto
class InstructionInstance:
    name: str
    condition: Expression
    children: list[InstructionInstance]


@tag("Instruction.InstructionAlias")
@defauto
class InstructionAlias:
    name: str
    operation_id: str
    condition: Expression


Instructionish = (
    typing.ForwardRef("Instruction", is_argument=False) | InstructionInstance | InstructionAlias
)

InstructionChildren = list[Instructionish]


@tag("Instruction.Instruction")
@defauto
class Instruction:
    name: str
    operation_id: str
    encoding: Encodeset
    condition: Expression | None = attrs.field(default=None)
    children: InstructionChildren | None = attrs.field(default=None)
    title: str | None = attrs.field(default=None)
    preferred: Expression | None = attrs.field(default=None)


InstructionGroupish = Instruction | typing.ForwardRef("InstructionGroup", is_argument=False)

InstructionGroupSetChildren = list[InstructionGroupish]


@tag("Instruction.InstructionGroup")
@defauto
class InstructionGroup:
    name: str
    encoding: Encodeset
    title: str | None = attrs.field(default=None)
    condition: Expression | None = attrs.field(default=None)
    children: InstructionGroupSetChildren | None = attrs.field(default=None)
    operation_id: str | None = attrs.field(default=None)


@tag("Instruction.InstructionSet")
@defauto
class InstructionSet:
    name: str
    encoding: Encodeset
    read_width: int
    condition: Expression | None = attrs.field(default=None)
    children: InstructionGroupSetChildren | None = attrs.field(default=None)
    operation_id: str | None = attrs.field(default=None)


@tag("Instruction.Operation")
@defauto
class Operation:
    operation: str
    description: str
    brief: str
    title: str
    decode: str | None = attrs.field(default=None)


@tag("Instruction.OperationAlias")
@defauto
class OperationAlias:
    operation_id: str
    description: str
    brief: str
    title: str


Operationish = Operation | OperationAlias


class Operations(dict[str, Operationish]):
    pass


@tag("Instruction.Instructions")
@defauto
class Instructions:
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
    InstructionChildren,
    InstructionGroupish,
    InstructionGroupSetChildren,
    Instructionish,
    Operationish,
    Operations,
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
    attrs.resolve_types(cls, globals(), locals())

# Set up cattrs converter with a custom structure hook
converter = Converter()
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


# Register a custom structure hook for Operations
converter.register_structure_hook(Operations, structure_operations)


def my_tag_generator(cl: type) -> str:
    return cl._type


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


def structure_trit(obj: str, cls: type):
    # print(f"structure_trit obj: '{obj}' cls: {cls}")
    return cls(obj)


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
                return self.eval_binop(cur_node, lv, rv)
            elif isinstance(cur_node, UnaryOp):
                ov = Interpteter(cur_node.expr).evaluate()
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
