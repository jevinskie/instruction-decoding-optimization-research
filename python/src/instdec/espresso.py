from instdec.util import StringList

# fmt: off
espresso_subcmds: tuple[str, ...] = (
    "ESPRESSO", "many", "exact", "qm", "single_output", "so", "so_both",
    "simplify", "echo", "signature", "opo", "opoall", "pair", "pairall",
    "check", "stats", "verify", "PLAverify", "equiv", "map", "mapdc", "fsm",
    "contain", "d1merge", "d1merge_in", "disjoint", "dsharp", "intersect",
    "minterms", "primes", "separate", "sharp", "union", "xor", "essen",
    "expand", "gasp", "irred", "make_sparse", "reduce", "taut", "super_gasp",
    "lexsort", "test"
)
# fmt: on


def generate_espresso(einf: dict[str, tuple[int, int]]) -> str:
    el = StringList()
    el @= ".i 32"
    el @= ".o 1"
    el @= ".ilb " + " ".join([f"I{i}" for i in reversed(range(32))])
    el @= ".olb V"
    for i, kv in enumerate(einf.items()):
        bmi = kv[1][0]
        bpi = kv[1][1]
        bits = ""
        for j in reversed(range(32)):
            sb = 1 << j
            if bmi & sb:
                if bpi & sb:
                    bits += "1"
                else:
                    bits += "0"
            else:
                bits += "-"
        bits += " 1"
        el @= bits
    el @= ".e"
    el @= ""
    return str(el)
