from __future__ import annotations

import enum
import sys
from typing import Any, Union

import attrs
import cattrs
import cattrs.dispatch
from cattrs import Converter

from instdec.trits import TritRange, TritRanges, Trits


def defauto(*args, **kwargs):
    kwargs["auto_attribs"] = True
    kwargs["on_setattr"] = None
    kwargs["frozen"] = True
    return attrs.define(*args, **kwargs)


class BinOp(enum.StrEnum):
    AND = "&&"
    NE = "!="
    EQ = "=="
    OR = "||"
    IN = "IN"


class UnOp(enum.StrEnum):
    NOT = "!"


@defauto
class Identifier:
    value: str


@defauto
class Value:
    meaning: str | None
    value: str


@defauto
class Bool:
    value: bool


@defauto
class Set:
    values: set[Value]


@defauto
class BinaryOp:
    left: Node
    op: BinOp
    right: Node


@defauto
class UnaryOp:
    expr: Node
    op: UnOp


@defauto
class Function:
    name: str
    arguments: list[Node]


# Define Node as a union of all possible node types
Node = Union[Bool, BinaryOp, Function, Identifier, UnaryOp, Set, Value]


@attrs.define(auto_attribs=True)
class Interpteter:
    ast: Node

    def evaluate(self) -> Any:
        cur_node: Node = self.ast
        if isinstance(cur_node, Function):
            self.eval_func(cur_node)
        return "TODO"

    def eval_func(self, cur_node: Function) -> Node:
        print(f"evaluating AST.Function '{cur_node.name}")
        return Bool(value=True)


# Set up cattrs converter with a custom structure hook
converter = Converter()


def structure_node(
    obj: cattrs.dispatch.UnstructuredValue, _: cattrs.dispatch.TargetType
) -> cattrs.dispatch.StructuredValue:
    type_to_class = {
        "AST.BinaryOp": BinaryOp,
        "AST.Bool": Bool,
        "AST.Function": Function,
        "AST.Identifier": Identifier,
        "AST.Set": Set,
        "AST.UnaryOp": UnaryOp,
        "Values.Value": Value,
    }
    cls = type_to_class.get(obj["_type"])
    if cls is None:
        raise ValueError(f"Unknown _type: {obj['_type']}")
    return converter.structure(obj, cls)


converter.register_structure_hook(Node, structure_node)


# Top-level class to match the JSON structure
@defauto
class Condition:
    condition: Node


class NodeRef:
    def __init__(self, node):
        self.node = node

    def __repr__(self):
        # Only display a summary: id and keys of the dict
        return f"<NodeRef id={id(self.node)} keys={list(self.node.keys())}>"


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
            # Append current node to the context, wrapping it with NodeRef to prevent recursive printing
            # current_context.append({"encoding": node["encoding"], "object": NodeRef(node)})
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


def find_leafs_helper(instrs: dict | list, encoding_stack: list | None = None) -> list:
    results = []
    if encoding_stack is None:
        encoding_stack = []
    if isinstance(instrs, dict):
        instrs = [instrs]
    elif not isinstance(instrs, list):
        print(f"type missing: {type(instrs)}", file=sys.stderr)
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
        sbmt = TritRange(start, width, valval)
        trit_ranges.add_range(sbmt)

    mtrits = trit_ranges.merge()
    mts = str(mtrits)
    return (inst["name"], mtrits, mts.count("0"), mts.count("1"), mts.count("X"))
