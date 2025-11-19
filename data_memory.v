module data_memory (
    input clk,
    input we,
    input [2:0] funct3,  // Determines width (Byte, Half, Word)
    input [31:0] a,      // Address
    input [31:0] wd,     // Write Data
    output reg [31:0] rd // Read Data
);

    reg [31:0] mem [0:255]; // 256 words of RAM

    reg [31:0] raw_word;
    reg [7:0]  b_val;
    reg [15:0] h_val;

    // Address Decoding
    wire [31:0] word_addr = a >> 2;
    wire [1:0]  byte_offset = a[1:0]; // Which byte inside the word?

    // READ LOGIC (Combinational)
    always @(*) begin
    
        raw_word = mem[word_addr];

        case (funct3)
            3'b010: rd = raw_word; // LW

            // Bytes (LB, LBU)
            3'b000, 3'b100: begin 
                // Extract the correct byte based on offset
                case (byte_offset)
                    2'b00: b_val = raw_word[7:0];
                    2'b01: b_val = raw_word[15:8];
                    2'b10: b_val = raw_word[23:16];
                    2'b11: b_val = raw_word[31:24];
                endcase
                // Sign Extension vs Zero Extension
                if (funct3 == 3'b000) rd = {{24{b_val[7]}}, b_val}; // LB
                else                  rd = {24'b0, b_val};          // LBU
            end

            // Half-words (LH, LHU)
            3'b001, 3'b101: begin
                // Extract half-word (offset 0 or 2)
                if (byte_offset[1] == 0) h_val = raw_word[15:0];
                else                     h_val = raw_word[31:16];

                if (funct3 == 3'b001) rd = {{16{h_val[15]}}, h_val}; // LH
                else                  rd = {16'b0, h_val};           // LHU
            end

            default: rd = 32'b0;
        endcase
    end

    // WRITE LOGIC (Sequential)
    always @(posedge clk) begin
        if (we) begin
            case (funct3)
                3'b010: mem[word_addr] <= wd; // SW

                3'b000: begin // SB (Store Byte)
                    // Read-Modify-Write: Keep 3 bytes, change 1
                    case (byte_offset)
                        2'b00: mem[word_addr][7:0]   <= wd[7:0];
                        2'b01: mem[word_addr][15:8]  <= wd[7:0];
                        2'b10: mem[word_addr][23:16] <= wd[7:0];
                        2'b11: mem[word_addr][31:24] <= wd[7:0];
                    endcase
                end

                3'b001: begin // SH (Store Half)
                    if (byte_offset[1] == 0) mem[word_addr][15:0]  <= wd[15:0];
                    else                     mem[word_addr][31:16] <= wd[15:0];
                end
            endcase
        end
    end

endmodule