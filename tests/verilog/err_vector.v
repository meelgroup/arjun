// RUN: %test_synth -u %S/ops.v.cnf %s > %t.log 2>&1; test $? -eq 1
// RUN: grep -q "line 3: unexpected character '\['" %t.log
module m(input wire [3:0] x1, output wire x4);
    assign x4 = x1;
endmodule
