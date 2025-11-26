module circt(input [3:0]i, output [0:0]o);
    wire [3:0]minterms_0;
    // reg [3:0]minterms_0 = 0;
    // assign minterms_0 = 3'b000;

    // out_bit: 0
    initial begin
    minterms_0 = 0;
    minterms_0[0] = (i & 4'b0111) == 4'b0111; // ob: 0 tn: 0
    minterms_0[1] = (i & 4'b1100) == 4'b1100; // ob: 0 tn: 1
    minterms_0[2] = (i & 4'b1010) == 4'b1010; // ob: 0 tn: 2
    minterms_0[3] = (i & 4'b1001) == 4'b1000; // ob: 0 tn: 3
    // minterms_0[3] = 1;
    // minterms_0[0] = 0;
    end

   assign o[0] = |minterms_0;
endmodule
