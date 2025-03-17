def find_encodings(node, context=None, results=None):
    if context is None:
        context = []
    if results is None:
        results = []

    if isinstance(node, dict):
        current_encoding = node.get("encoding")
        # Update current context if encoding exists
        new_context = context + [current_encoding] if current_encoding is not None else context
        if current_encoding is not None:
            results.append({"encoding": current_encoding, "context": context.copy()})

        scan_objs = []
        children = node.get("children", [])
        if isinstance(children, dict):
            children = [children]
        scan_objs += children
        for k in node.keys():
            if k == "children":
                continue
            # if k == "encoding":
            #     continue
            scan_objs.append(node[k])
        for scan_obj in scan_objs:
            find_encodings(scan_obj, new_context, results)

    elif isinstance(node, list):
        for item in node:
            # print("in list")
            find_encodings(item, context, results)

    return results
