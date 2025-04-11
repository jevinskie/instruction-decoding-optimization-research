import pandas as pd
from ortools.sat.python import cp_model
from rich import print


def cpsat_check_encoding(einf: dict[str, tuple[int, int]]) -> None:
    all_vars = []
    model = cp_model.CpModel()
    pidx = pd.Index(range(32), name="idx")
    ib = model.new_bool_var_series("i", pidx)
    all_vars.append(ib)
    # ib = [model.new_bool_var(f"i{i}") for i in reversed(range(32))]
    ivs = {}
    for iname, ei in einf.items():
        bm, bp = ei
        iv = model.new_bool_var(f"v_{iname}")
        all_vars.append(iv)
        ivs[iname] = iv
        for i in list(range(32)):
            if bm & (1 << i):
                bpb = bool(bp & (1 << i))
                lit = model.new_bool_var(f"v_{iname}_{i}_{int(bpb)}")
                all_vars.append(lit)
                model.AddBoolAnd(lit).OnlyEnforceIf(iv)
                model.AddImplication(lit, ib[i])
    model.AddAtLeastOne(ivs.values())
    print(model)
    solver = cp_model.CpSolver()
    solve_status = solver.solve(model)
    print(f"solve status: {solve_status}")
    ibv = solver.boolean_values(ib)
    print(f"ibv: {ibv}")
