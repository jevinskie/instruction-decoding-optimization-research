import pandas as pd
from ortools.sat.python import cp_model
from rich import print


def cpsat_check_encoding(einf: dict[str, tuple[int, int]]) -> None:
    model = cp_model.CpModel()
    pidx = pd.Index(range(32), name="idx")
    ib = model.new_bool_var_series("i", pidx)
    # ib = [model.new_bool_var(f"i{i}") for i in reversed(range(32))]
    ivs = {}
    for iname, ei in einf.items():
        bm, bp = ei
        iv = model.new_bool_var(f"v_{iname}")
        ivs[iname] = iv
        lits = []
        for x in range(32):
            lits.append(ib[int(x)] == True)  # noqa: E712

        for i in list(range(32)):
            if bm & (1 << i):
                bpb = bool(bp & (1 << i))
                lit = model.new_bool_var(f"v_{iname}_{int(bpb)}")
                model.AddBoolAnd(lit).OnlyEnforceIf(iv)
                # lits.append(lit)
    model.add_at_least_one(ivs.values())
    print(model)
