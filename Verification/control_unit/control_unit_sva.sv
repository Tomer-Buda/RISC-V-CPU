module control_unit_sva (
    input logic [6:0] opcode,
    input logic [2:0] funct3,
    input logic [6:0] funct7,
    input logic reg_write,
    input logic mem_write,
    input logic alu_src,
    input logic [1:0] alu_src_a,
    input logic [1:0] result_src,
    input logic branch,
    input logic jump,
    input logic jalr,
    input logic [3:0] alu_ctrl,
    input logic clk
);
// SVA Properties for Control Unit
    // Opcode Definitions
    localparam OP_LOAD   = 7'b0000011;
    localparam OP_STORE  = 7'b0100011;
    localparam OP_BRANCH = 7'b1100011;
    localparam OP_R_TYPE = 7'b0110011;
    localparam OP_I_TYPE = 7'b0010011;
    localparam OP_JAL    = 7'b1101111;
    localparam OP_JALR   = 7'b1100111; 

    property check_store_logic;
        @(posedge clk)
        (opcode == OP_STORE) |-> (mem_write == 1 && reg_write == 0);
    endproperty

    property check_load_logic;
        @(posedge clk)
        (opcode == OP_LOAD) |-> (reg_write == 1 && mem_write == 0 && alu_src == 1 && result_src == 2'b01);
    endproperty

    property check_rtype_logic;
        @(posedge clk)
        (opcode == OP_R_TYPE) |-> (reg_write == 1 && alu_src == 0 && result_src == 2'b00);
    endproperty

    property check_itype_logic;
        @(posedge clk)
        (opcode == OP_I_TYPE) |-> (reg_write == 1 && alu_src == 1 && result_src == 2'b00);
    endproperty

    property check_branch_logic;
        @(posedge clk)
        (opcode == OP_BRANCH) |-> (branch == 1 && reg_write == 0 && mem_write == 0);
    endproperty

    property check_jal_logic;
        @(posedge clk)
        (opcode == OP_JAL) |-> (jump == 1 && reg_write == 1 && mem_write == 0 && result_src == 2'b10);
    endproperty

    property check_jalr_logic;
        @(posedge clk)
        (opcode == OP_JALR) |-> (jalr == 1 && reg_write == 1 && mem_write == 0 && alu_src == 1 && result_src == 2'b10);
    endproperty

    // Assert property for R-type instruction
    assert_rtype_check: assert property (check_rtype_logic)
        else $error("Control Unit BUG FOUND: R-type instruction has wrong signals!");

    // Assert property for I-type instruction
    assert_itype_check: assert property (check_itype_logic)
        else $error("Control Unit BUG FOUND: I-type instruction has wrong signals!");

    // Assert property for branch instruction
    assert_branch_check: assert property (check_branch_logic)
        else $error("Control Unit BUG FOUND: Branch instruction has wrong signals!");

    // Assert property for JAL instruction
    assert_jal_check: assert property (check_jal_logic) 
        else $error("Control Unit BUG FOUND: JAL instruction has wrong signals!");
    
    // Assert property for JALR instruction
    assert_jalr_check: assert property (check_jalr_logic)
        else $error("Control Unit BUG FOUND: JALR instruction has wrong signals!");
    
    // Assert property for load instruction
    assert_load_check: assert property (check_load_logic)
        else $error("Control Unit BUG FOUND: Load instruction has wrong signals!");

    // Assert property for store instruction
    assert_store_check: assert property (check_store_logic)
        else $error("Control Unit BUG FOUND: Store instruction has wrong signals!");
endmodule