`timescale 1ns/1ns

module tb_sva;

    // Signals
    logic [6:0] opcode;
    logic [2:0] funct3;
    logic [6:0] funct7;
    logic       clk;
    
    // Outputs
    logic       reg_write;
    logic       mem_write;
    logic       alu_src;
    logic [1:0] alu_src_a;
    logic [1:0] result_src;
    logic       branch;
    logic       jump;
    logic       jalr;
    logic [3:0] alu_ctrl;

    // The Design (DUT)
    control_unit uut (
        .opcode(opcode),
        .funct3(funct3),
        .funct7(funct7),
        .reg_write(reg_write),
        .mem_write(mem_write),
        .alu_src(alu_src),
        .alu_src_a(alu_src_a),
        .result_src(result_src),
        .branch(branch),
        .jump(jump),
        .jalr(jalr),
        .alu_ctrl(alu_ctrl)
    );

    // The Verification Module (SVA)
    control_unit_sva verifier (
        .opcode(opcode),
        .funct3(funct3),
        .funct7(funct7),
        .reg_write(reg_write),
        .mem_write(mem_write),
        .alu_src(alu_src),
        .alu_src_a(alu_src_a),
        .result_src(result_src),
        .branch(branch),
        .jump(jump),
        .jalr(jalr),
        .alu_ctrl(alu_ctrl),
        .clk(clk)
    );

    // Clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Stimulus
    initial begin
        // Init
        opcode = 0; funct3 = 0; funct7 = 0;
        #10;

        // LOAD
        $display("Testing LOAD Instruction...");
        opcode = 7'b0000011; 
        #10;

        // STORE
        $display("Testing STORE Instruction...");
        opcode = 7'b0100011; 
        #10;

        // R-TYPE
        $display("Testing R-TYPE Instruction...");
        opcode = 7'b0110011; funct3 = 3'b000; funct7 = 0;
        #10;

        // BRANCH
        $display("Testing BRANCH Instruction...");
        opcode = 7'b1100011; 
        #10;

        // JAL
        $display("Testing JAL Instruction...");
        opcode = 7'b1101111; 
        #10;

        // JALR
        $display("Testing JALR Instruction...");
        opcode = 7'b1100111; 
        #10;
        
        $display("All tests finished. If no errors appeared above, YOU PASSED!");
        $finish;
    end
endmodule