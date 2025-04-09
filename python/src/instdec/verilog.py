from instdec.util import StringList


def generate_verilog(einf: dict[str, tuple[int, int]]) -> str:
    # TODO: Generate "number of valid decodes"
    vl = StringList()
    vl @= "module a64dec(input [31:0]i, output v);"
    vl @= f"    wire [{len(einf) - 1}:0]vtmp;"
    for i, kv in enumerate(einf.items()):
        vl @= (
            f"    assign vtmp[{i:4}] = (i & 32'b{kv[1][0]:032b}) == 32'b{kv[1][1]:032b}; // {kv[0]}"
        )
    vl @= "    assign v = |vtmp;"
    vl @= "endmodule"
    vl @= ""
    return str(vl)
