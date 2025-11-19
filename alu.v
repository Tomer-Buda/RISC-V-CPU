module alu (
    input  [31:0] a,       // Operand A
    input  [31:0] b,       // Operand B
    input  [3:0]  alu_ctrl,// Operation Control Code
    output reg [31:0] result, // Calculation Result
    output zero            // Zero Flag (True if result == 0)
);

    // Operation Codes (Matches standard RISC-V conventions closely)
    localparam ADD  = 4'b0000;
    localparam SUB  = 4'b1000;
    localparam SLL  = 4'b0001;
    localparam SLT  = 4'b0010; // Set Less Than (Signed)
    localparam SLTU = 4'b0011; // Set Less Than (Unsigned)
    localparam XOR  = 4'b0100;
    localparam SRL  = 4'b0101;
    localparam SRA  = 4'b1101;
    localparam OR   = 4'b0110;
    localparam AND  = 4'b0111;

    assign zero = (result == 0);

    always @(*) begin
        case (alu_ctrl)
            ADD:  result = a + b;
            SUB:  result = a - b;
            AND:  result = a & b;
            OR:   result = a | b;
            XOR:  result = a ^ b;
            SLL:  result = a << b[4:0]; // Shift amount is bottom 5 bits
            SRL:  result = a >> b[4:0];
            SRA:  result = $signed(a) >>> b[4:0]; // Arithmetic shift (preserves sign)
            
            // Comparisons: Return 1 if true, 0 if false
            SLT:  result = ($signed(a) < $signed(b)) ? 32'd1 : 32'd0;
            SLTU: result = (a < b) ? 32'd1 : 32'd0;
            
            default: result = 32'b0;
        endcase
    end
endmodule