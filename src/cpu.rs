use crate::cpu::decoder::{BType, IType, JType, RType, SType, UType};

mod decoder;

struct Memory {
    mem: Vec<u8>,
}
impl Memory {
    pub fn read_byte(&mut self, addr: u64) -> u8 {
        self.mem[addr as usize]
    }
    pub fn read_hword(&mut self, addr: u64) -> u16 {
        u16::from_le_bytes([self.read_byte(addr), self.read_byte(addr.wrapping_add(1))])
    }
    pub fn read_word(&mut self, addr: u64) -> u32 {
        u32::from_le_bytes([self.read_byte(addr), self.read_byte(addr.wrapping_add(1)), self.read_byte(addr.wrapping_add(2)), self.read_byte(addr.wrapping_add(3))])
    }
    pub fn read_dword(&mut self, addr: u64) -> u64 {
        u64::from_le_bytes([self.read_byte(addr), self.read_byte(addr.wrapping_add(1)), self.read_byte(addr.wrapping_add(2)), self.read_byte(addr.wrapping_add(3)), self.read_byte(addr.wrapping_add(4)), self.read_byte(addr.wrapping_add(5)), self.read_byte(addr.wrapping_add(6)), self.read_byte(addr.wrapping_add(7))])
    }
    pub fn write_byte(&mut self, addr: u64, val: u8) {
        self.mem[addr as usize] = val
    }
    pub fn write_hword(&mut self, addr: u64, val: u16) {
        for (i, byte) in val.to_le_bytes().into_iter().enumerate() {
            self.write_byte(addr.wrapping_add(i as u64), byte);
        }
    }
    pub fn write_word(&mut self, addr: u64, val: u32) {
        for (i, byte) in val.to_le_bytes().into_iter().enumerate() {
            self.write_byte(addr.wrapping_add(i as u64), byte);
        }
    }
    pub fn write_dword(&mut self, addr: u64, val: u64) {
        for (i, byte) in val.to_le_bytes().into_iter().enumerate() {
            self.write_byte(addr.wrapping_add(i as u64), byte);
        }
    }
}

fn sext8(x: u8) -> u64 {
    x as i8 as i64 as u64
}
fn sext16(x: u16) -> u64 {
    x as i16 as i64 as u64
}
fn sext32(x: u32) -> u64 {
    x as i32 as i64 as u64
}

pub struct Cpu {
    registers: [u64; 32],
    pc: u64,
    mem: Memory,
}
impl Cpu {
    pub fn new(rom: Vec<u8>) -> Cpu {
        Self { registers: [0; 32], pc: 0, mem: Memory { mem: rom } }
    }
    pub fn step(&mut self) {
        self.step_inner();
        self.registers[0] = 0;
    }
    fn step_inner(&mut self) {
        let instruction = self.mem.read_word(self.pc);

        let opcode = instruction & 0b111_1111;

        match opcode {
            0b0110111 => { // LUI
                let decoded = UType::decode(instruction);
                self.registers[decoded.rd as usize] = sext32(decoded.imm);
            }
            0b0010111 => { // AUIPC
                let decoded = UType::decode(instruction);
                self.registers[decoded.rd as usize] = self.pc.wrapping_add(sext32(decoded.imm));
            }
            0b1101111 => { // JAL
                let decoded = JType::decode(instruction);
                self.registers[decoded.rd as usize] = self.pc.wrapping_add(4);
                self.pc = self.pc.wrapping_add(sext32(decoded.imm));
            }
            0b1100111 => { // JALR
                let decoded = IType::decode(instruction);
                if decoded.funct3 != 0 {
                    panic!("invalid funct3 for JALR instruction");
                }
                let target = self.registers[decoded.rs1 as usize].wrapping_add(sext32(decoded.imm)) & (!1);
                self.registers[decoded.rd as usize] = self.pc.wrapping_add(4);
                self.pc = target;
            }
            0b1100011 => { // branch
                let decoded = BType::decode(instruction);
                let src1 = self.registers[decoded.rs1 as usize];
                let src2 = self.registers[decoded.rs2 as usize];
                let target = self.pc.wrapping_add(sext32(decoded.imm));
                let branch = match decoded.funct3 {
                    0 => { // BEQ
                        src1 == src2
                    }
                    1 => { // BNE
                        src1 != src2
                    }
                    4 => { // BLT
                        (src1 as i64) < (src2 as i64)
                    }
                    5 => { // BGE
                        (src1 as i64) >= (src2 as i64)
                    }
                    6 => { // BLTU
                        src1 < src2
                    }
                    7 => { // BGEU
                        src1 >= src2
                    }
                    _ => panic!("invalid funct3 for branch instruction")
                };
                if branch {
                    self.pc = target;
                }
            }
            0b0000011 => { // loads
                let decoded = IType::decode(instruction);
                let addr = self.registers[decoded.rs1 as usize].wrapping_add(sext32(decoded.imm));
                let val = match decoded.funct3 {
                    0 => { // LB
                        sext8(self.mem.read_byte(addr))
                    }
                    1 => { // LH
                        sext16(self.mem.read_hword(addr))
                    }
                    2 => { // LW
                        sext32(self.mem.read_word(addr))
                    }
                    3 => { // LD
                        self.mem.read_dword(addr)
                    }
                    4 => { // LBU
                        self.mem.read_byte(addr) as u64
                    }
                    5 => { // LHU
                        self.mem.read_hword(addr) as u64
                    }
                    6 => { // LWU
                        self.mem.read_word(addr) as u64
                    }
                    _ => panic!("invalid funct3 for load instruction")
                };
                self.registers[decoded.rd as usize] = val;
            }
            0b0100011 => { // stores
                let decoded = SType::decode(instruction);
                let addr = self.registers[decoded.rs1 as usize].wrapping_add(sext32(decoded.imm));
                let val = self.registers[decoded.rs2 as usize];
                match decoded.funct3 {
                    0 => { // SB
                        self.mem.write_byte(addr, val as u8);
                    }
                    1 => { // SH
                        self.mem.write_hword(addr, val as u16);
                    }
                    2 => { // SW
                        self.mem.write_word(addr, val as u32);
                    }
                    3 => { // SD
                        self.mem.write_dword(addr, val);
                    }
                    _ => panic!("invalid funct3 for store instruction")
                }
            }
            0b0010011 => { // register-immediate alu ops
                let decoded = IType::decode(instruction);
                let val = self.registers[decoded.rs1 as usize];
                let reg = &mut self.registers[decoded.rd as usize];
                match decoded.funct3 {
                    0 => { // ADDI
                        *reg = val.wrapping_add(sext32(decoded.imm));
                    }
                    1 => { // SLLI
                        if decoded.imm >= 64 {
                            panic!("invalid shamt for SLLI instruction")
                        }
                        *reg = val << decoded.imm;
                    }
                    2 => { // SLTI 
                        *reg = ((val as i64) < (sext32(decoded.imm) as i64)) as u64
                    }
                    3 => { // SLTIU
                        *reg = (val < sext32(decoded.imm)) as u64
                    }
                    4 => { // XORI
                        *reg = val ^ sext32(decoded.imm);
                    }
                    5 => { // SRLI + SRAI
                        let is_arith = (decoded.imm & 0b100_0000_0000) != 0;
                        let shamt = decoded.imm & (!0b100_0000_0000);
                        if shamt >= 64 {
                            panic!("invalid shamt for SRLI/SRAI instruction")
                        }
                        if is_arith {
                            *reg = ((val as i64) >> decoded.imm) as u64;
                        } else {
                            *reg = val >> decoded.imm;
                        }
                    }
                    6 => { // ORI
                        *reg = val | sext32(decoded.imm);
                    }
                    7 => { // ANDI
                        *reg = val & sext32(decoded.imm);
                    }
                    _ => panic!("invalid funct3 for register-immediate alu op")
                }
            }
            0b0011011 => { // 32-bit register-immediate alu ops
                let decoded = IType::decode(instruction);
                let val = self.registers[decoded.rs1 as usize] as u32;
                let reg = &mut self.registers[decoded.rd as usize];
                match decoded.funct3 {
                    0 => { // ADDIW
                        *reg = sext32(val.wrapping_add(decoded.imm))
                    }
                    1 => { // SLLIW
                        if decoded.imm >= 32 {
                            panic!("invalid shamt for SLLIW instruction")
                        }
                        *reg = sext32(val << decoded.imm);
                    }
                    5 => { // SRLIW + SRAIW
                        let is_arith = (decoded.imm & 0b100_0000_0000) != 0;
                        let shamt = decoded.imm & (!0b100_0000_0000);
                        if shamt >= 32 {
                            panic!("invalid shamt for SRLI/SRAI instruction")
                        }
                        if is_arith {
                            *reg = sext32(((val as i32) >> decoded.imm) as u32);
                        } else {
                            *reg = sext32(val >> decoded.imm);
                        }
                    }
                    _ => panic!("invalid funct3 for 32-bit register-immediate alu op")
                }
            }
            0b0110011 => { // register-register alu ops
                let decoded = RType::decode(instruction);
                let src1 = self.registers[decoded.rs1 as usize];
                let src2 = self.registers[decoded.rs2 as usize];
                let reg = &mut self.registers[decoded.rd as usize];
                match (decoded.funct7, decoded.funct3) {
                    (0, 0) => { // ADD
                        *reg = src1.wrapping_add(src2);
                    }
                    (0b0100000, 0) => { // SUB
                        *reg = src1.wrapping_sub(src2);
                    }
                    (0, 1) => { // SLL
                        *reg = src1 << (src2 & 0b11_1111);
                    }
                    (0, 2) => { // SLT
                        *reg = ((src1 as i64) < (src2 as i64)) as u64;
                    }
                    (0, 3) => { // SLTU
                        *reg = (src1 < src2) as u64;
                    }
                    (0, 4) => { // XOR
                        *reg = src1 ^ src2;
                    }
                    (0, 5) => { // SRL
                        *reg = src1 >> (src2 & 0b11_1111);
                    }
                    (0b0100000, 5) => { // SRA
                        *reg = ((src1 as i64) >> (src2 & 0b11_1111)) as u64;
                    }
                    (0, 6) => { // OR
                        *reg = src1 | src2;
                    }
                    (0, 7) => { // AND
                        *reg = src1 & src2;
                    }
                    (_, _) => {
                        panic!("invalid funct3 + funct7 combo for register-register alu op")
                    }
                }
            }
            0b0111011 => { // 32-bit register-register alu ops
                let decoded = RType::decode(instruction);
                let src1 = self.registers[decoded.rs1 as usize] as u32;
                let src2 = self.registers[decoded.rs2 as usize] as u32;
                let reg = &mut self.registers[decoded.rd as usize];
                match (decoded.funct7, decoded.funct3) {
                    (0, 0) => { // ADDW
                        *reg = sext32(src1.wrapping_add(src2));
                    }
                    (0b0100000, 0) => { // SUBW
                        *reg = sext32(src1.wrapping_sub(src2));
                    }
                    (0, 1) => { // SLLW
                        *reg = sext32(src1 << (src2 & 0b1_1111));
                    }
                    (0, 5) => { // SRLW
                        *reg = sext32(src1 >> (src2 & 0b1_1111));
                    }
                    (0b0100000, 5) => { // SRAW
                        *reg = sext32(((src1 as i32) >> (src2 & 0b1_1111)) as u32);
                    }
                    (_, _) => {
                        panic!("invalid funct3 + funct7 combo for 32-bit register-register alu op")
                    }
                }
            }
            0b0001111 => {} // fence stuff which is a NOP in this emulator
            0b1110011 => { // ECALL + EBREAK
                panic!("ECALL/EBREAK executed. instruction: {opcode:b}")
            }
            _ => {
                panic!("invalid opcode")
            }
        }

        self.pc += 4;
    }
}