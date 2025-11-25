module instruction_memory (
    input [31:0] addr,
    output [31:0] instr
);
    reg [31:0] mem [0:255]; // 256 x 32-bit instruction memory
    assign instr = mem[addr >> 2]; // Word-aligned addressing
    initial begin
        $readmemh("program.hex", mem);
    end
endmodule
