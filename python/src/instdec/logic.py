import sympy
import sympy.logic.boolalg as balg
from rich import print


def generate_dnf(einf: dict[str, tuple[int, int]]) -> None:
    ib = sympy.symbols([f"i{n}" for n in range(32)])
    terms = {}
    # out = sympy.symbols("out")
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
        terms[name] = balg.And(*list(bpbs.values()))
    terms_summed = balg.Or(*list(terms.values()))
    print(terms_summed)
