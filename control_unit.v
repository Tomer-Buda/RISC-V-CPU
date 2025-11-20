module control_unit (
    input  [6:0] opcode,
    input  [2:0] funct3,
    input  [6:0] funct7,
    output reg reg_write,
    output reg mem_write,
    output reg alu_src, // 0 = RegB, 1 = Imm
    output reg [1:0] alu_src_a,  // 0 = RegA, 1 = PC (For AUIPC/JAL)
    output reg [1:0] result_src, // 0 = ALU, 1 = Mem, 2 = PC+4
    output reg branch, // 1 if it's a branch instruction
    output reg jump, // 1 if it's JAL
    output reg jalr, // 1 if it's JALR
    output reg [3:0] alu_ctrl // The ALU Operation Code
);

    // ALU Control Codes
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

    // Main Decoder
    always @(*) begin
        // Defaults
        reg_write = 0; mem_write = 0; alu_src = 0; alu_src_a = 2'b00;
        result_src = 0; branch = 0; jump = 0; jalr = 0;
        alu_ctrl = ADD; // Default to add

        case (opcode)
            // R-Type (ADD, SUB, SLL, etc.)
            7'b0110011: begin
                reg_write = 1;
                // Logic for ALU Ops
                case (funct3)
                    3'b000: alu_ctrl = (funct7[5]) ? SUB : ADD; // Add/Sub
                    3'b001: alu_ctrl = SLL;
                    3'b010: alu_ctrl = SLT;
                    3'b011: alu_ctrl = SLTU;
                    3'b100: alu_ctrl = XOR;
                    3'b101: alu_ctrl = (funct7[5]) ? SRA : SRL; // SRA/SRL
                    3'b110: alu_ctrl = OR;
                    3'b111: alu_ctrl = AND;
                endcase
            end

            // I-Type ALU (ADDI, XORI, etc.)
            7'b0010011: begin
                reg_write = 1;
                alu_src = 1; // Use Immediate
                case (funct3)
                    3'b000: alu_ctrl = ADD;
                    3'b010: alu_ctrl = SLT;
                    3'b011: alu_ctrl = SLTU;
                    3'b100: alu_ctrl = XOR;
                    3'b110: alu_ctrl = OR;
                    3'b111: alu_ctrl = AND;
                    3'b001: alu_ctrl = SLL;
                    3'b101: alu_ctrl = (funct7[5]) ? SRA : SRL;
                endcase
            end

            // Load (LB, LH, LW, etc.)
            7'b0000011: begin
                reg_write = 1;
                alu_src = 1;
                result_src = 2'b01; // Select Memory Result
                alu_ctrl = ADD;     // Calculate Address (Reg + Imm)
            end

            // Store (SB, SH, SW)
            7'b0100011: begin
                mem_write = 1;
                alu_src = 1;
                alu_ctrl = ADD;     // Calculate Address (Reg + Imm)
            end

            // Branch (BEQ, BNE, etc.)
            7'b1100011: begin
                branch = 1;
                alu_src = 0;
                alu_ctrl = SUB; 
            end

            // JAL
            7'b1101111: begin
                jump = 1;
                reg_write = 1;
                result_src = 2'b10; // Write PC+4 to Reg
            end

            // JALR
            7'b1100111: begin
                jalr = 1;
                reg_write = 1;
                alu_src = 1;        // Rs1 + Imm
                result_src = 2'b10; // Write PC+4 to Reg
                alu_ctrl = ADD;     // Calculate Target
            end

            // LUI (Load Upper Immediate)
        7'b0110111: begin
            reg_write = 1;
            alu_src = 1;    // Use Imm
            alu_src_a = 2'b10; // Select Zero
            alu_ctrl = ADD; // Result = 0 + Imm
        end

            // AUIPC (Add Upper Imm to PC)
        7'b0010111: begin
            reg_write = 1;
            alu_src = 1;    // Imm
            alu_src_a = 2'b01; // Select PC
            alu_ctrl = ADD; // PC + Imm
        end

            default: begin
                // NOP or Unsupported Instruction
        end
        endcase
    end
endmodule