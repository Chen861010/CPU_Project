//==============================================================
//  mem.sv — 32-word x 8-bit Synchronous Memory
//
//  Design matches cpu_v1 and its testbench assumptions:
//    • Module name: mem
//    • Internal array: memory[0:31]
//    • Address width: 5 bits (PC / IR addressing range)
//    • Separate synchronous read and write operations
//
//  Behavior:
//    • Write occurs on posedge clk when write=1 and read=0
//    • Read  occurs on posedge clk when read=1 and write=0
//    • Simultaneous read/write is intentionally disallowed
//==============================================================

timeunit 1ns;
timeprecision 100ps;

module mem (
    input  logic        clk,        // Clock input (posedge-triggered)
    input  logic        read,       // Read enable (active high)
    input  logic        write,      // Write enable (active high)
    input  logic [4:0]  addr,       // Address (0–31)
    input  logic [7:0]  data_in,    // Data for write operation
    output logic [7:0]  data_out    // Data read from memory
);

    // ------------------------------------------------------------
    // Internal memory array
    // 32 entries, 8 bits each
    //
    // Aligned with testbench access convention:
    //      dut.u_mem.memory[i]
    // ------------------------------------------------------------
    logic [7:0] memory [0:31];


    // ------------------------------------------------------------
    // Synchronous Write:
    //   • Occurs only when write=1 and read=0
    //   • Data is stored at memory[addr]
    // ------------------------------------------------------------
    always_ff @(posedge clk) begin
        if (write && !read)
            memory[addr] <= data_in;
    end


    // ------------------------------------------------------------
    // Synchronous Read:
    //   • Occurs only when read=1 and write=0
    //   • data_out updates on the rising edge
    // ------------------------------------------------------------
    always_ff @(posedge clk) begin
        if (read && !write)
            data_out <= memory[addr];
    end

endmodule
