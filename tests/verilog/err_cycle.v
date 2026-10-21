// RUN: %expect_exit 1 %test_synth -u %S/ops.v.cnf %s > %t.log 2>&1
// RUN: grep -q "line 7: wire 'a' depends on itself" %t.log
module m(input wire x1, output wire x4);
    wire a, b;
    assign x4 = a;
    assign a = b & x1;
    assign b = ~a;
endmodule
