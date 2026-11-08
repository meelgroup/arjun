// RUN: %expect_exit 1 %test_synth -u %S/ops.v.cnf %s > %t.log 2>&1
// RUN: grep -q "line 4: 'x2' is not declared" %t.log
module m(input wire x1, output wire x4);
    assign x4 = x1 & x2;
endmodule
