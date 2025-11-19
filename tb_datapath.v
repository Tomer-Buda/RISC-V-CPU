`timescale 1ns/1ps
module tb_datapath;
    reg clk, rst;
    wire [31:0] alu_res;

    datapath uut (.clk(clk), .rst(rst), .alu_result_out(alu_res));

    initial begin
        clk = 1; forever #5 clk = ~clk;
    end

    initial begin
        $dumpfile("cpu_waveforms.vcd");
        $dumpvars(0, tb_datapath);

        // Monitor interesting signals (PC is inside uut)
        $monitor("Time=%0t | PC=%h | Instr=%h | ALU_Res=%h", 
                 $time, uut.pc, uut.instr, alu_res);

        rst = 1; #15; rst = 0;

        #200; 
        $finish;
    end
endmodule