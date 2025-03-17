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
            current_context.append({"encoding": node["encoding"], "object": path})

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
