module datapath (
    input clk,
    input rst,
    output [31:0] alu_result_out // For viewing in simulation
);

    // Wires
    wire [31:0] pc, next_pc, pc_plus_4, pc_target;
    wire [31:0] instr;
    wire [31:0] imm;
    wire [31:0] rd1, rd2;
    wire [31:0] alu_a, alu_b;
    wire [31:0] alu_result;
    wire [31:0] mem_read_data;
    wire [31:0] result; // The final value to write back
    wire zero;
    wire clk, rst;

    // Control Signals
    wire reg_write, mem_write, alu_src, branch, jump, jalr;
    wire [1:0] alu_src_a;
    wire [1:0] result_src;
    wire [3:0] alu_ctrl;
    wire [2:0] funct3 = instr[14:12];
    wire [6:0] funct7 = instr[31:25];
    wire [6:0] opcode = instr[6:0];

    assign alu_result_out = alu_result; // Connect output for testbench

    // FETCH STAGE
    // PC Register
    program_counter pc_reg (
        .clk(clk),
        .rst(rst),
        .next_pc(next_pc),
        .pc(pc)
    );

    // Instruction Memory
    instruction_memory imem (
        .addr(pc),
        .instr(instr)
    );

    // PC Adder
    assign pc_plus_4 = pc + 4;

    // DECODE STAGE
    // Immediate Generator
    imm_gen ext (
        .instr(instr),
        .imm(imm)
    );

    // Control Unit
    control_unit ctrl (
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

    // Register File
    register_file rf (
        .clk(clk),
        .we3(reg_write),
        .a1(instr[19:15]), // rs1
        .a2(instr[24:20]), // rs2
        .a3(instr[11:7]),  // rd
        .wd3(result),      // Data to write
        .rd1(rd1),
        .rd2(rd2)
    );

    // EXECUTE STAGE
    // 00=Reg, 01=PC, 10=Zero (for LUI)
    assign alu_a = (alu_src_a == 2'b01) ? pc : 
               (alu_src_a == 2'b10) ? 32'b0 : rd1;

    // ALU Input B Mux (0=Reg, 1=Imm)
    assign alu_b = (alu_src) ? imm : rd2;

    // ALU
    alu main_alu (
        .a(alu_a),
        .b(alu_b),
        .alu_ctrl(alu_ctrl),
        .result(alu_result),
        .zero(zero)
    );

    // MEMORY STAGE
    data_memory dmem (
        .clk(clk),
        .we(mem_write),
        .funct3(funct3),
        .a(alu_result),
        .wd(rd2),
        .rd(mem_read_data)
    );

    // WRITEBACK STAGE
    // Result Mux (0=ALU, 1=Mem, 2=PC+4)
    assign result = (result_src == 2'b00) ? alu_result :
                    (result_src == 2'b01) ? mem_read_data :
                    (result_src == 2'b10) ? pc_plus_4 : 32'b0;

    // PC LOGIC (Branch & Jump)
    
    // Branch Condition Logic
    reg take_branch;
    always @(*) begin
        case (funct3)
            3'b000: take_branch = (rd1 == rd2);                  // BEQ
            3'b001: take_branch = (rd1 != rd2);                  // BNE
            3'b100: take_branch = ($signed(rd1) < $signed(rd2)); // BLT
            3'b101: take_branch = ($signed(rd1) >= $signed(rd2));// BGE
            3'b110: take_branch = (rd1 < rd2);                   // BLTU
            3'b111: take_branch = (rd1 >= rd2);                  // BGEU
            default: take_branch = 0;
        endcase
    end

    // PC Target Calculation
    // JALR target = (rs1 + imm) & ~1 (LSB must be 0)
    // Branch/JAL target = PC + Imm
    wire [31:0] target_val = (jalr) ? rd1 : pc;
    assign pc_target = (target_val + imm) & ~32'd1; // Mask LSB for JALR spec compliance

    // PC Mux
    // Jump if (JAL/JALR) OR (Branch AND Condition Met)
    wire pcsrac = jump | jalr | (branch & take_branch);
    assign next_pc = (pcsrac) ? pc_target : pc_plus_4;

endmodule
