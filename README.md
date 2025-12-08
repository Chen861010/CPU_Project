# CPU_Project
A SystemVerilog-based verification environment for the ZhenCPU, including FSM, ALU, register, memory testing, waveform analysis, and functional coverage.

---

## Overview
ZhenCPU is a simplified CPU designed for instruction-level execution and hardware verification learning.  
This repository contains:

- RTL source code (SystemVerilog) organized per module  
- Self-checking testbenches for each module (ALU, Mem, Mux, Rig, Controller, Counter)  
- CPU-level integration testbench  
- Waveform analysis using **Cadence Xcelium + SimVision**  
- Functional coverage and simulation support using **QuestaSim / ModelSim**  
- Formal property verification (FPV) for FSM, registers, counters, and ALU  
- Instruction program testing environment  

---

## CPU Modules

- **ALU** – arithmetic & logic operations  
- **MUX Units** – data-path selection  
- **Register / Rig** – accumulator & intermediate registers  
- **Controller** – 8-state Moore FSM for instruction sequencing  
- **Memory** – 8-bit data memory with 5-bit address  
- **Program Counter** – 5-bit counter with enable & reset  

All module directories include RTL + testbench + coverage + FPV assertions.

---

## Verification Features

- ✔ Module-level testbenches (ALU, Mem, Mux, Rig, Control, Counter)  
- ✔ CPU integration testing under CPUwave/  
- ✔ Directed + randomized stimulus  
- ✔ Waveform tracing (VCD/FSDB via SimVision or Questa GUI)  
- ✔ Functional coverage using **QuestaSim UCDB**  
- ✔ Simulation logs & automated scripts (`runme.sh`, `runcover.sh`, `clean.sh`)  
- ✔ Formal verification (FPV) with bind files  

---

## 📁 Project Structure

```
src/                         # RTL modules + per-module verification environment
  ALU/                       # ALU RTL, ALU testbench, FPV assertions, bind files,
                             # QuestaSim coverage scripts, runme.sh & runcover.sh
  Mem/                       # Memory RTL + memory testbench + FPV + coverage
  Mux/                       # 2-to-1 multiplexer RTL + testbench + coverage
  Rig/                       # 8-bit register RTL + testbench + FPV + coverage
  control/                   # 8-state controller FSM RTL + testbench + FPV + coverage
  count/                     # 5-bit counter / PC RTL + testbench + FPV + coverage
  cpu.sv                     # Top-level CPU module integrating all submodules
  typedefs.sv                # Shared typedefs, enums, opcodes, state definitions

CPUwave/                     # CPU-level waveform simulation environment (Xcelium)
  cpu_tb.sv                  # Full CPU testbench (instruction-level execution)
  runme.sh                   # Launch full CPU simulation + SimVision wave viewer

programs/                    # Instruction program tests + TCL automation scripts
coverage/                    # Consolidated functional coverage reports (UCDB/text)
tb/                          # Additional standalone or experimental testbenches
waves/                       # User-generated waveform screenshots or FSDB exports
.gitignore                   # Files excluded from version control
README.md                    # Project documentation (this file)
```

```

---

## 🖥️ Simulation Tools

---

## **Cadence Xcelium + SimVision (`runme.sh`)**

`runme.sh` is used for **full CPU simulation and waveform debugging**.  
This script compiles the entire design and launches SimVision for FSDB waveform viewing.

### Typical Flow

```bash
./runme.sh       # compile + simulate + open SimVision waveform viewer
```

### Internally, the script performs:

```bash
xrun -64bit -access +rwc \
     cpu_tb.sv cpu.sv ... \
     -gui
```

### Features

- Fast compile/runtime  
- Full SVA/assertion support  
- SimVision waveform debugging  
- FSDB signal tracing  

### Output Files

- `xrun.log` — simulation log  
- `xcelium.d/` — build directory  
- `waves.shm/` or `.fsdb` — waveform database  
- `simvision_history/` — SimVision layout  

---

## **QuestaSim Functional Coverage (`runcover.sh`)**

`runcover.sh` is designed specifically for **functional coverage** using **QuestaSim UCDB**.  
This script compiles modules, runs the testbench, executes `cover.do`, and writes coverage reports.

### Typical Flow

```bash
./runcover.sh    # compile + simulate + generate UCDB coverage
```

### Internally, the script performs:

```bash
vlib work
vlog *.sv
vsim -c top_tb -do "do cover.do; run -all; coverage report -output cov.rpt; quit"
```

### Features

- UCDB functional coverage  
- FSM, opcode, ALU-path coverage  
- Coverage merging and visualization  
- Compatible with all per-module testbenches  

### Output Files

- `cov.rpt` — text-based coverage report  
- `work.ucdb` — full UCDB coverage database  
- `transcript` — QuestaSim command log  

### Viewing Coverage in GUI

```bash
vsim -viewcov work.ucdb
```

---


