from __future__ import annotations

from collections import defaultdict
from collections.abc import Callable
from typing import Any, DefaultDict

import attrs
from rich import print

from .arm_json_schema import (
    BinaryOp,
    BinOp,
    Bool,
    Encodeset,
    Expression,
    Function,
    Identifier,
    Instruction,
    InstructionAlias,
    InstructionGroup,
    InstructionOrInstructionGroup,
    Instructions,
    JSONSchemaObject,
    JSONSchemaObjectClasses,
    Set,
    UnaryOp,
    UnOp,
    Value,
    Valueish,
)
from .trits import Trits
from .util import Pigeonholes, defauto, traverse_nested


def expr_get_objs(expr: Expression) -> list[JSONSchemaObject]:
    res: list[JSONSchemaObject] = []
    rset: set[JSONSchemaObject] = set()

    def helper(e: Expression):
        if e in rset:
            raise ValueError(f"should e be in rset? e: {e} expr: {expr} rset: {rset}")
        if isinstance(e, JSONSchemaObjectClasses):
            res.append(e)
        if isinstance(e, BinaryOp):
            helper(e.left)
            helper(e.right)
        elif isinstance(e, UnaryOp):
            helper(e.expr)
        elif isinstance(e, Set):
            for v in e.values:
                helper(v)

    helper(expr)
    return res


def expr_idents(expr: Expression) -> list[str]:
    idents: list[str] = []

    def helper(e: Expression):
        if isinstance(e, BinaryOp):
            helper(e.left)
            helper(e.right)
        elif isinstance(e, UnaryOp):
            helper(e.expr)
        elif isinstance(e, Identifier):
            idents.append(e.value)

    helper(expr)
    if len(idents) != len(set(idents)):
        raise ValueError("got duplicate AST.Identifiers")
    return idents


def expr_has_ident(expr: Expression, ident: str) -> bool:
    return ident in expr_idents(expr)


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


def are_encodesets_consistent(a: dict, b: dict) -> bool:
    return False


# def constrain_instr(encset: En)


def merge_constraints(constraints: list[Expression | None]) -> list[Expression]:
    consdef: list[Expression] = [c for c in constraints if c is not None]
    res: list[Expression] = []
    rset: set[Expression] = set()
    for cons in consdef:
        if cons in rset:
            if cons == Bool(True):
                continue
            raise ValueError(
                f"merge_constraints: got duplicate constraint. Is this bad? cons: {cons}"
            )
        rset.add(cons)
        res.append(cons)
    return res


def has_instructions_w_children(instrs: Instructions) -> bool:
    for iset in instrs.instructions:

        def check(o: Any, _: str) -> None:
            if isinstance(o, Instruction):
                if (
                    hasattr(o, "children")
                    and o.children is not None
                    and len(o.children) != 0
                    and not all([isinstance(c, InstructionAlias) for c in o.children])
                ):
                    raise ValueError(f"found instr w/ children: {o}")
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


def get_encoding_list(ctx: ParseContext, instr_enc: Encodeset) -> list[Encodeset]:
    return [instr_enc] + ctx.group_encoding_stack[::-1] + ctx.set_encoding_stack[::-1]


def get_condition_list(ctx: ParseContext, instr_cond: Expression | None) -> list[Expression | None]:
    return [instr_cond] + ctx.group_condition_stack[::-1] + ctx.set_condition_stack[::-1]


def get_conditon_list_defined(ctx: ParseContext, instr_cond: Expression | None) -> list[Expression]:
    return list(filter(lambda x: x is not None, get_condition_list(ctx, instr_cond)))


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
            else:
                raise TypeError("skipping from seen id OTHER")
            continue  # TODO: see if assertions are ever raisec
        if isinstance(ioig, Instruction):
            cb(ioig, ctx)
        else:
            if not isinstance(ioig, InstructionGroup):
                raise ValueError(f"ioig type: {type(ioig)}")
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


def dump_idents_instr_cb(i: Instruction, ctx: ParseContext) -> None:
    if i.condition is not None and expr_has_ident(i.condition, "Rm"):
        rs: list[str] = []
        instr_field = i.encoding.get_field("Rm")
        if instr_field:
            rs.append("Rm in instr encoding")
        for n, instr_group_enc in enumerate(ctx.group_encoding_stack[::-1]):
            instr_group_field = instr_group_enc.get_field("Rm")
            if instr_group_field is not None:
                rs.append(f"Rm in instr group stack[{n}]")
        iset_field = ctx.set_encoding_stack[-1].get_field("Rm")
        if iset_field is not None:
            rs.append("Rm in instr set")
        smth = ", ".join(rs)
        print(f"smth: {smth}")


num_cons: DefaultDict[int, int] = defaultdict(int)
num_expr_objs: DefaultDict[int, int] = defaultdict(int)


def inspect_constraints_instr_cb(instr: Instruction, ctx: ParseContext) -> None:
    cons = merge_constraints(get_condition_list(ctx, instr.condition))
    num_cons[len(cons)] += 1
    for e in cons:
        num_expr_objs[len(expr_get_objs(e))] += 1


def encodeset_overlap_check_instr_cb(instr: Instruction, ctx: ParseContext) -> None:
    for eset in get_encoding_list(ctx, instr.encoding):
        pholes = Pigeonholes(32)
        for eset_bit in eset.get_bits():
            pholes.add_span(eset_bit.range.span)
        for eset_field in eset.get_fields():
            pholes.add_span(eset_field.range.span)
        if pholes.has_overlaps():
            raise ValueError(
                f"encodeset_overlap_check_instr_cb pholes has overlaps: {pholes.spans}"
            )


def encodeset_overlap_overall_check_instr_cb(instr: Instruction, ctx: ParseContext) -> None:
    pholes = Pigeonholes(32)
    esetlist = get_encoding_list(ctx, instr.encoding)
    for eset in esetlist:
        for eset_bit in eset.get_bits():
            pholes.add_span(eset_bit.range.span)
        for eset_field in eset.get_fields():
            pholes.add_span(eset_field.range.span)
    if pholes.has_overlaps():
        print("\n\n\n")
        spstrs: list[str] = []
        for espn in pholes.spans:
            spstrs.append(espn.ascii_art(32))
        spstrs.sort(reverse=True)
        for s in spstrs:
            print(f"    {s}")
        print("\n\n\n", flush=True)
        print("instr:")
        print(instr)
        print("esetlist:")
        print(esetlist)
        raise ValueError(
            f"encodeset_overlap_overall_check_instr_cb pholes has overlaps: {pholes.spans}"
        )


def instr_cb(i: Instruction, ctx: ParseContext) -> None:
    dump_idents_instr_cb(i, ctx)
    inspect_constraints_instr_cb(i, ctx)
    encodeset_overlap_check_instr_cb(i, ctx)
    encodeset_overlap_overall_check_instr_cb(i, ctx)


def parse_instructions(instrs: Instructions, cb: InstrCB) -> None:
    ctx = ParseContext()
    ctx.obj_stack.append(instrs)

    for iset in instrs.instructions:
        ctx.obj_stack.append(iset)
        ctx.set_encoding_stack.append(iset.encoding)
        ctx.set_condition_stack.append(iset.condition)

        if iset.children is None:
            raise ValueError(f"iset name: {iset.name} children is None")

        recurse_instr_or_instr_group(list(iset.children), ctx, cb)

        ctx.set_condition_stack.pop()
        ctx.set_encoding_stack.pop()
        ctx.obj_stack.pop()

    ctx.obj_stack.pop()

    return


def dump_idents(instrs: Instructions) -> None:
    parse_instructions(instrs, instr_cb)
    nc = dict(sorted(num_cons.items()))
    print(f"num_cons: {nc}")
    no = dict(sorted(num_expr_objs.items()))
    print(f"num_expr_objs: {no}")
