CPU_Project

A SystemVerilog-based verification environment for the ZhenCPU, including FSM, ALU, register, memory testing, waveform analysis, and functional coverage.

Overview

ZhenCPU is a simplified CPU designed for instruction-level execution and hardware verification learning.
This repository contains:

RTL source code (SystemVerilog) organized per module

Self-checking testbenches for each module (ALU, Mem, Mux, Rig, Controller, Counter)

CPU-level integration testbench

Waveform analysis using Cadence Xcelium + SimVision

Formal property verification (FPV) for FSM, registers, counters, and ALU

Functional coverage reports for each module and CPU-level tests

Instruction program testing environment

CPU Modules

ALU – arithmetic & logic operations

MUX Units – data-path selection

Register / Rig – accumulator & intermediate pipeline registers

Controller – 8-state Moore FSM for instruction sequencing

Memory – 8-bit data memory with 5-bit address

Program Counter – 5-bit counter with enable & reset

All module directories include RTL + testbench + coverage + FPV assertions.

Verification Features

✔ Module-level testbenches (ALU, Mem, Mux, Rig, Control, Counter)
✔ CPU integration testing under CPUwave/
✔ Directed + randomized stimulus
✔ Waveform tracing (VCD/FSDB via SimVision)
✔ Functional coverage (FSM states, ALU opcodes, memory accesses, register operations)
✔ Formal verification (FPV) with bind files
✔ Simulation logs & automated scripts (runme.sh, runcover.sh, clean.sh)

📁 Project Structure
src/                # RTL + per-module verification
  ALU/              # ALU RTL, testbench, FPV, coverage, scripts
  Mem/              # Memory RTL, testbench, FPV, coverage
  Mux/              # Mux RTL + testbench
  Rig/              # 8-bit register RTL + testbench + FPV
  control/          # FSM controller RTL + testbench + FPV
  count/            # 5-bit counter RTL + testbench + FPV
  cpu.sv            # Top-level CPU integration RTL
  typedefs.sv       # Shared enums & type definitions

CPUwave/            # CPU-level waveform simulation environment
  cpu_tb.sv         # Full CPU testbench
  runme.sh          # Launch full CPU simulation + SimVision

programs/           # Instruction-program testing + TCL automation
coverage/           # Consolidated functional coverage reports
tb/                 # Additional standalone testbenches (if any)
waves/              # Waveform screenshots (user-generated)
.gitignore
README.md


  
