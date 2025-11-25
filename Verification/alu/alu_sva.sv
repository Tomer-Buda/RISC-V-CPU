module alu_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [3:0]  alu_ctrl,
    input logic [31:0] result,
    input logic        zero,
    input logic        clk
);

    // Operation Codes
    localparam ADD  = 4'b0000;
    localparam SUB  = 4'b1000;
    localparam SLL  = 4'b0001;
    localparam SLT  = 4'b0010;
    localparam SLTU = 4'b0011; 
    localparam XOR  = 4'b0100;
    localparam SRL  = 4'b0101; 
    localparam SRA  = 4'b1101;
    localparam OR   = 4'b0110;
    localparam AND  = 4'b0111;

    // ARITHMETIC & LOGIC CHECKS
    property check_add;
        @(posedge clk) (alu_ctrl == ADD) |-> (result == a + b);
    endproperty
    assert_add: assert property (check_add) else $error("BUG: ADD failed!");

    property check_sub;
        @(posedge clk) (alu_ctrl == SUB) |-> (result == a - b);
    endproperty
    assert_sub: assert property (check_sub) else $error("BUG: SUB failed!");

    property check_and;
        @(posedge clk) (alu_ctrl == AND) |-> (result == (a & b));
    endproperty
    assert_and: assert property (check_and) else $error("BUG: AND failed!");

    property check_or;
        @(posedge clk) (alu_ctrl == OR) |-> (result == (a | b));
    endproperty
    assert_or: assert property (check_or) else $error("BUG: OR failed!");

    property check_xor;
        @(posedge clk) (alu_ctrl == XOR) |-> (result == (a ^ b));
    endproperty
    assert_xor: assert property (check_xor) else $error("BUG: XOR failed!");

    // SHIFT CHECKS
    // We wrap the RHS in $unsigned() to force a raw bitwise comparison
    property check_sra;
        @(posedge clk) (alu_ctrl == SRA) |-> (result == $unsigned($signed(a) >>> b[4:0]));
    endproperty
    
    // Error Message to help debug if it fails
    assert_sra: assert property (check_sra) 
        else $error("BUG: SRA failed! Input: %h, Shift: %d, Result: %h, Expected: %h", 
                    a, b[4:0], result, $unsigned($signed(a) >>> b[4:0]));

    property check_sll;
        @(posedge clk) (alu_ctrl == SLL) |-> (result == a << b[4:0]);
    endproperty
    assert_sll: assert property (check_sll) else $error("BUG: SLL failed!");

    property check_srl;
        @(posedge clk) (alu_ctrl == SRL) |-> (result == a >> b[4:0]);
    endproperty
    assert_srl: assert property (check_srl) else $error("BUG: SRL (Logical) failed!");

    // COMPARISON CHECKS
    property check_slt;
        @(posedge clk) (alu_ctrl == SLT) |-> 
            (result == (($signed(a) < $signed(b)) ? 32'd1 : 32'd0));
    endproperty
    assert_slt: assert property (check_slt) else $error("BUG: SLT (Signed) failed!");

    property check_sltu;
        @(posedge clk) (alu_ctrl == SLTU) |-> 
            (result == (a < b ? 32'd1 : 32'd0));
    endproperty
    assert_sltu: assert property (check_sltu) else $error("BUG: SLTU (Unsigned) failed!");

    // ZERO FLAG CHECKS
    // 1. If result is 0, Zero MUST be 1
    property check_zero_high;
        @(posedge clk) (result == 0) |-> (zero == 1);
    endproperty
    assert_zero_high: assert property (check_zero_high) else $error("BUG: Result is 0, but Zero Flag is LOW!");

    // 2. If result is NOT 0, Zero MUST be 0 (Prevents flag getting stuck high)
    property check_zero_low;
        @(posedge clk) (result != 0) |-> (zero == 0);
    endproperty
    assert_zero_low: assert property (check_zero_low) else $error("BUG: Result is NOT 0, but Zero Flag is HIGH!");

endmodule