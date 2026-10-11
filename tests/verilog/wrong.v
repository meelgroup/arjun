// a wrong function must be caught: x4 should be x1 ^ x2
// RUN: %test_synth -u %S/ops.v.cnf %s > %t.log; test $? -eq 1
// RUN: grep -q "Sample does not satisfy the CNF" %t.log
module m(input wire x1, input wire x2, input wire x3, output wire x4, output wire x5, output wire x6);
    assign x4 = x1 | x2;
    assign x5 = x1 ? x2 : x3;
    assign x6 = ~x1 & ~x3;
endmodule
