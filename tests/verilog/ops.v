// every operator, old-style ports, and wires used before they are assigned
// RUN: %test_synth -u %s.cnf %s | grep -q "verified CORRECT"
module ops(x1, x2, x3, x4, x5, x6);
    input x1, x2;
    input x3;
    output x4, x5, x6;
    wire both, either, nor13;
    /* x4 is an xor,
       spelled out */
    assign x4 = either & !both;
    assign x5 = x1 ? x2 & 1'b1 : (x3 | 1'b0);
    assign x6 = nor13 ^ 0, nor13 = ~(x1 | x3);
    assign either = x1 | x2;
    assign both = x1 & x2;
endmodule
