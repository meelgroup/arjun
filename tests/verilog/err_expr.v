// RUN: %expect_exit 1 %test_synth -u %S/ops.v.cnf %s > %t.log 2>&1
// RUN: grep -q "line 4: malformed expression for 'x4'" %t.log
module m(input wire x1, output wire x4);
    assign x4 = (x1 & ) | x1;
endmodule
