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


def parse_term(term: str) -> list[int]:
    """Parse a 32-bit term into a list of literals."""
    literals: list[int] = []
    if len(term) != 32:
        raise ValueError(f"len(term) != 32 term: '{term}'")
    for j, bit in enumerate(term):
        if bit == "1":
            literals.append(j + 1)  # x_j is j+1
        elif bit == "0":
            literals.append(-(j + 1))  # ~x_j is -(j+1)
        # '-' is don't care, so skip
    return literals


def term_from_bit_mask_and_pattern(bm: int, bp: int) -> list[int]:
    """Parse a 32-bit term from bitmask and bitpattern into a list of literals."""
    literals: list[int] = []
    for j in range(32):
        if (1 << j) & bm:
            if (1 << j) & bp:
                literals.append(j + 1)
            else:
                literals.append(-(j + 1))
    return literals


def terms_from_enc_info(einf: dict[str, tuple[int, int]]) -> list[list[int]]:
    return [term_from_bit_mask_and_pattern(bmp[0], bmp[1]) for bmp in einf.values()]


def generate_cnf(terms: list[list[int]]) -> tuple[list[list[int]], int]:
    """Generate CNF clauses using Tseitin transformation."""
    clauses: list[list[int]] = []
    num_terms = len(terms)
    num_vars = 32 + num_terms + 1  # 32 x's, N y's, 1 z
    y_base = 33  # y_0 starts at 33
    z = num_vars - 1

    # Process each product term
    for i, term in enumerate(terms):
        y_i = y_base + i
        literals = term

        # Clauses for y_i <-> p_i
        for lit in literals:
            clauses.append([-y_i, lit])  # ~y_i \/ lit
        # y_i \/ ~lit_1 \/ ~lit_2 \/ ...
        clauses.append([y_i] + [-lit for lit in literals])

    # Clauses for z <-> (y_0 \/ y_1 \/ ... \/ y_792)
    y_vars = list(range(y_base, y_base + num_terms))
    clauses.append([-z] + y_vars)  # ~z \/ y_0 \/ ... \/ y_792
    for y_i in y_vars:
        clauses.append([z, -y_i])  # z \/ ~y_i

    # Enforce f = 1
    clauses.append([z])

    return clauses, num_vars


def geneerate_dimacs(clauses: list, num_vars: int) -> str:
    return f"p cnf {num_vars} {len(clauses)}\n" + "\n".join([f"{c} 0" for c in clauses]) + "\n"
