module program_counter (
    input clk,
    input rst,
    input [31:0] next_pc, // The Datapath tells us where to go
    output reg [31:0] pc
);
    always @(posedge clk) begin
        if (rst)
            pc <= 32'b0;
        else
            pc <= next_pc; // Just load the value. No calculation here.
    end
endmodule
