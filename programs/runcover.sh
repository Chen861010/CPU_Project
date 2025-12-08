rm -rf work cpu_cov.ucdb vsim.wlf covhtmlreport
vlib work

echo "=== Compile RTL ==="
vlog typedefs.sv
vlog 2to1_mux.sv
vlog 5bit_count.sv
vlog 8bit_rig.sv
vlog 8S_control.sv
vlog ALU.sv
vlog Mem.sv
vlog cpu.sv

echo "=== Compile Assertions ==="
vlog cpu_assertions.sv
vlog cpu_coverage.sv

echo "=== Compile Testbench ==="
vlog -cover sbecft cpu_stb.sv

echo "=== Run Simulation (FULL COVERAGE ENABLED) ==="
vsim -c testbench -coverage -do cover.do


