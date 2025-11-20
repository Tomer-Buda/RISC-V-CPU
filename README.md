# Single-Cycle RISC-V Processor (RV32I)

A fully functional, synthesized Single-Cycle RISC-V processor core designed in Verilog. This architecture implements the complete **RV32I Base Integer Instruction Set**, capable of handling arithmetic, logic, memory access, and complex control flow.

## Architecture Features

* **Instruction Set:** Supports R-Type, I-Type, S-Type, B-Type, U-Type, and J-Type instructions.
* **Universal ALU:** Handles 10 operations including signed/unsigned comparisons (`SLT`/`SLTU`) and arithmetic shifts (`SRA`).
* **Smart Data Memory:** byte-addressable memory supporting Word (`LW`/`SW`), Half-Word (`LH`/`SH`), and Byte (`LB`/`SB`) access with correct sign extension logic.
* **Control Flow:** Full support for conditional branching (`BEQ`, `BNE`, `BLT`, `BGE`) and unconditional jumps (`JAL`, `JALR`) using a dedicated 3-way PC Multiplexer.
* **Immediate Generation:** Specialized hardware unit to unscramble and sign-extend 12-bit and 20-bit immediates.

## Design Modules

1.  **Datapath (`datapath.v`):** Top-level integration wiring the PC, ALU, RegFile, and Memory.
2.  **Control Unit (`control_unit.v`):** Main decoder generating control signals based on Opcode/Funct3/Funct7.
3.  **Register File (`register_file.v`):** 32x32-bit dual-read port, single-write port memory.
4.  **Data Memory (`data_memory.v`):** 1KB RAM with read-modify-write logic for sub-word access.
5.  **Immediate Generator (`imm_gen.v`):** Combinational logic for immediate value extraction.

## Verification

The core is verified using a self-checking assembly test suite (`program.hex`) that validates:
* Register Read/Write integrity.
* ALU Arithmetic and Logic correctness.
* Memory Load/Store operations (Byte/Half/Word).
* Branching and Jumping logic (Forward/Backward jumps).

### How to Run

1.  **Install Icarus Verilog:**
    ```bash
    # MacOS
    brew install icarus-verilog
    # Linux
    sudo apt-get install iverilog
    # Windows
    # Download installer from https://bleyer.org/icarus/
    ```

2.  **Compile the Design:**
    ```bash
    iverilog -o cpu_core alu.v register_file.v data_memory.v instruction_memory.v program_counter.v control_unit.v imm_gen.v datapath.v tb_datapath.v
    ```

3.  **Run Simulation:**
    ```bash
    vvp cpu_core

    ```


