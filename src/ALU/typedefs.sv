package typedefs;
  typedef enum logic [2:0] {
    HLT = 3'b000, SKZ = 3'b001, ADD = 3'b010, AND = 3'b011,
    XOR = 3'b100, LDA = 3'b101, STO = 3'b110, JMP = 3'b111
  } opcode_t;

  typedef enum logic [2:0] {
    INST_ADDR = 3'd0, INST_FETCH = 3'd1, INST_LOAD = 3'd2,
    IDLE = 3'd3, OP_ADDR = 3'd4, OP_FETCH = 3'd5,
    ALU_OP = 3'd6, STORE = 3'd7
  } state_t;
endpackage
