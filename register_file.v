module register_file (
    input  clk,
    input  we3,           // Write Enable
    input  [4:0] a1,      // Address Read 1
    input  [4:0] a2,      // Address Read 2
    input  [4:0] a3,      // Address Write
    input  [31:0] wd3,    // Write Data
    output [31:0] rd1,    // Read Data 1
    output [31:0] rd2     // Read Data 2
);

    reg [31:0] rf [31:0]; // 32 registers of 32 bits each

    // 1. Synchronous Write (Clocked)
    always @(posedge clk) begin
        if (we3) begin
            rf[a3] <= wd3;
        end
    end

    // 2. Asynchronous Read (Combinational)
    // If address is 0, output 0. Otherwise read from array.
    assign rd1 = (a1 != 0) ? rf[a1] : 32'b0;
    assign rd2 = (a2 != 0) ? rf[a2] : 32'b0;

endmodule