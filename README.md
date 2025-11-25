# RISC-V Core Design & Formal Verification

## Project Overview
This repository contains the RTL design and Formal Verification environment for a Single-Cycle RISC-V Processor (RV32I). The project is divided into two modules:
1. **RTL Design:** A synthesizable Verilog implementation of the RISC-V Core.
2. **Formal Verification:** An Assertion-Based Verification (ABV) suite using SystemVerilog Assertions (SVA) to validate protocol compliance and logic correctness.

---

## Module 1: RTL Design (The CPU)
**Location:** [`/rtl`](./rtl)
* **Architecture:** Single-Cycle RV32I (Base Integer Instruction Set).
* **Features:**
  * **ALU:** Supports all arithmetic, logical, and shift operations including separation of Arithmetic (`>>>`) vs Logical (`>>`) shifts.
  * **Control Unit:** Decodes Opcode/Funct3/Funct7 to generate control signals.
  * **Datapath:** Includes PC Multiplexing for Jumps/Branches and Immediate Generation.

---

## Module 2: Formal Verification (The Police)
**Location:** [`/Verification`](./Verification)

I implemented a robust **Assertion-Based Verification (ABV)** environment using **Aldec Riviera-PRO**. Unlike standard simulation, this strictly enforces mathematical properties to prevent illegal states.

### Key Verification Features
* **Control Unit Safety:**
  * Formally proved **Mutual Exclusion** (e.g., `MemRead` and `MemWrite` never active simultaneously).
  * Enforced **State Safety** (e.g., Branch instructions must never trigger `RegWrite`).
* **ALU Data Integrity:**
  * Validated **Signed vs. Unsigned** logic (SLT vs SLTU).
  * Verified **Sign Extension** correctness for Arithmetic Shifts (SRA).
  * Implemented bi-directional **Zero Flag** assertions.

### Verification Evidence
**1. Fault Injection Testing (The "Sabotage" Test)**
To prove the testbench works, I intentionally broke the Arithmetic Shift logic (changed `>>>` to `>>`). The SVA environment immediately caught the bug:
![Fault Injection](Verification/docs/fault_injection_demo.png)

**2. Successful Verification (Golden Model)**
After fixing the logic, the design passed 100% of the assertion coverage properties

---

## 🚀 How to Run
The verification environment is set up for **Aldec Riviera-PRO** (or any simulator supporting SVA).
1. Load the design files from `rtl/`.
2. Load the assertion files from `Verification/assertions/`.
3. Run the testbench from `Verification/testbench/`.
