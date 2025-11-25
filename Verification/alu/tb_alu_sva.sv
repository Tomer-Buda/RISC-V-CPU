`timescale 1ns/1ns

module tb_alu_sva;

    // Signals
    logic [31:0] a, b;
    logic [3:0]  alu_ctrl;
    logic [31:0] result;
    logic        zero;
    logic        clk;

    // Instantiate ALU (Design)
    alu uut (
        .a(a), .b(b), .alu_ctrl(alu_ctrl), .result(result), .zero(zero)
    );

    // Instantiate SVA (Verification)
    alu_sva police_alu (
        .a(a), .b(b), .alu_ctrl(alu_ctrl), .result(result), .zero(zero), .clk(clk)
    );

    // Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Stimulus
    initial begin
        $display("--- STARTING FULL ALU VERIFICATION ---");
        
        a = 0; b = 0; alu_ctrl = 0;
        #10;

        // 1. ADD
        $display("Testing ADD...");
        a = 10; b = 20; alu_ctrl = 4'b0000;
        #10;

        // 2. SUB
        $display("Testing SUB...");
        a = 20; b = 5; alu_ctrl = 4'b1000;
        #10;

        // 3. AND
        $display("Testing AND...");
        a = 32'hF0F0F0F0; b = 32'hFFFF0000; alu_ctrl = 4'b0111;
        #10;

        // 4. OR
        $display("Testing OR...");
        a = 32'hF0F0F0F0; b = 32'h0000FFFF; alu_ctrl = 4'b0110;
        #10;

        // 5. XOR
        $display("Testing XOR...");
        a = 32'hFFFFFFFF; b = 32'hFFFF0000; alu_ctrl = 4'b0100;
        #10;

        // 6. SLL
        $display("Testing SLL...");
        a = 32'd1; b = 32'd4; alu_ctrl = 4'b0001; 
        #10;

        // 7. SRL
        $display("Testing SRL...");
        a = 32'hF0000000; b = 32'd4; alu_ctrl = 4'b0101; 
        #10;

        // 8. SRA
        $display("Testing SRA...");
        a = 32'hF0000000; b = 32'd4; alu_ctrl = 4'b1101; 
        #10;

        // 9. SLT
        $display("Testing SLT...");
        a = -10; b = 10; alu_ctrl = 4'b0010;
        #10;

        // 10. SLTU
        $display("Testing SLTU...");
        a = 32'hFFFFFFFF; b = 10; alu_ctrl = 4'b0011;
        #10;

        // --- 11. ZERO FLAG TEST (NEW) ---
        $display("Testing ZERO FLAG (15 - 15)...");
        a = 15; b = 15; alu_ctrl = 4'b1000; // SUB
        // Expected: Result = 0, Zero = 1
        #10;

        $display("------------------------------------------------");
        $display("ALU VERIFICATION FINISHED. If no red errors above, YOU PASSED!");
        $finish;
    end
endmodule