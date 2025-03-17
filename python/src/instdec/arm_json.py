import sys


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
            if "encoding" in x:
                assert x["encoding"]["_type"] == "Instruction.Encodeset.Encodeset"
                encoding_stack.append(x["encoding"])
            if "encoding" in x and (
                ("children" in x and len(x["children"]) == 0) or ("children" not in x)
            ):
                # we are leaf
                xc = x.copy()
                for band in ("assembly", "assemble", "condition"):
                    if band in xc:
                        del xc[band]
                xc["parent_encodings"] = encoding_stack.copy()
                results.append(xc)
                continue
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
