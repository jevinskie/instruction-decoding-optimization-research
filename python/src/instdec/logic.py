import sympy
import sympy.logic.boolalg as balg
from rich import print


def generate_dnf(einf: dict[str, tuple[int, int]]) -> balg.Boolean:
    ib = sympy.symbols([f"i{n}" for n in range(32)])
    terms = {}
    for i, kv in enumerate(einf.items()):
        name, bvs = kv
        bm, bp = bvs
        bpbs = {}
        for j in list(range(32)):
            if bm & (1 << j):
                bpb = bool(bp & (1 << j))
                if bpb:
                    bpbs[j] = ib[j]
                else:
                    bpbs[j] = balg.Not(ib[j])
        terms[name] = balg.And(*bpbs.values())
    terms_summed = balg.Or(*terms.values())
    print(terms_summed)
    # anf = terms_summed.to_anf()
    # print(f"type(anf): {type(anf)}")
    # print("anf:")
    # print(anf)
    return terms_summed
