from ortools.sat.python import cp_model
from rich import print


def cpsat_check_encoding(einf: dict[str, tuple[int, int]]) -> None:
    model = cp_model.CpModel()
    ib = [model.new_bool_var(f"i{i}") for i in reversed(range(32))]
    for iname, ei in einf.items():
        bm, bp = ei
        iv = model.new_bool_var(f"v_{iname}")
        model.add_bool_and(
            [ib[i] == int(bool(bp & (1 << i))) for i in reversed(range(32)) if bm & (1 << i)]
        ).only_enforce_if(iv)
    print(model)
