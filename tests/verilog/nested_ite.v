// ?: is right-associative and binds weaker than | ^ &
// RUN: %test_synth -u %s.cnf %s | grep -q "verified CORRECT"
module m(input wire x1, input wire x2, input wire x3, output wire x4, x5, x6);
    assign x4 = x1 & x2 ? 1'b0 : x1 ? 1'b1 : x2;
    assign x5 = x1 ? x2 ? 1'b1 : 1'b0 : x3 ^ x3 | x3 & x3;
    assign x6 = ~(x1 ? 1'b1 : x3);
endmodule
