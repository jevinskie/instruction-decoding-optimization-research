module test(input clk, output reg [3:0] y);
    always @(posedge clk)
        y <= (y << 1) | ^y;
endmodule
