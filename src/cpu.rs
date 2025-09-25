use crate::cpu::decoder::{BType, IType, JType, RType, SType, UType};

mod decoder;

#[derive(Default)]
struct Csrs {
    mtvec: u64,
    mepc: u64,
    mcause: u64,
    mtval: u64,
}
impl Csrs {
    fn new() -> Self {
        Self::default()
    }
    fn write_exception(&mut self, mepc: u64, mcause: u64, mtval: u64) {
        self.mepc = mepc;
        self.mcause = mcause;
        self.mtval = mtval;
    }
    fn mtvec(&self) -> u64 {
        self.mtvec
    }
    fn read(&mut self, addr: u64) -> u64 {
        match addr {
            0x305 => {
                // mtvec
                self.mtvec
            }
            0x341 => {
                self.mepc
            }
            0x342 => {
                self.mcause
            }
            0x343 => {
                self.mtval
            }
            _ => 0
        }
    }
    fn write(&mut self, addr: u64, val: u64) {
        match addr {
            0x305 => {
                self.mtvec = val;
            }
            0x341 => {
                self.mepc = val;
            }
            0x342 => {
                self.mcause = val;
            }
            0x343 => {
                self.mtval = val;
            }
            _ => {}
        }
    }
}

struct Memory {
    mem: Vec<u8>,
}
impl Memory {
    #[track_caller]
    pub fn read_byte(&mut self, addr: u64) -> u8 {
        if addr < 0x80000000 {
            panic!("read unmapped address {}", addr);
        }
        self.mem[addr as usize - 0x80000000]
    }
    #[track_caller]
    pub fn read_hword(&mut self, addr: u64) -> u16 {
        u16::from_le_bytes([self.read_byte(addr), self.read_byte(addr.wrapping_add(1))])
    }
    #[track_caller]
    pub fn read_word(&mut self, addr: u64) -> u32 {
        u32::from_le_bytes([
            self.read_byte(addr),
            self.read_byte(addr.wrapping_add(1)),
            self.read_byte(addr.wrapping_add(2)),
            self.read_byte(addr.wrapping_add(3)),
        ])
    }
    #[track_caller]
    pub fn read_dword(&mut self, addr: u64) -> u64 {
        u64::from_le_bytes([
            self.read_byte(addr),
            self.read_byte(addr.wrapping_add(1)),
            self.read_byte(addr.wrapping_add(2)),
            self.read_byte(addr.wrapping_add(3)),
            self.read_byte(addr.wrapping_add(4)),
            self.read_byte(addr.wrapping_add(5)),
            self.read_byte(addr.wrapping_add(6)),
            self.read_byte(addr.wrapping_add(7)),
        ])
    }
    pub fn write_byte(&mut self, addr: u64, val: u8) {
        self.mem[addr as usize - 0x80000000] = val
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

pub enum Exception {
    InstructionAddressMisaligned { pc: u64 },
    IllegalInstruction { pc: u64, instruction: u32 },
    Breakpoint { pc: u64 },
    LoadAccessFault { pc: u64, addr: u64 },
    StoreAccessFault { pc: u64, addr: u64 },
    Ecall { pc: u64 },
}

pub struct Cpu {
    pub registers: [u64; 32],
    pub pc: u64,
    csrs: Csrs,
    mem: Memory,
}
impl Cpu {
    pub fn new(mem: Vec<u8>) -> Cpu {
        Self {
            registers: [0; 32],
            pc: 0,
            mem: Memory { mem },
            csrs: Csrs::new(),
        }
    }
    /// returns all ECALL/EBREAK exceptions
    pub fn step(&mut self) -> Option<Exception> {
        let exception = self.step_inner();
        let ret = match exception {
            Err(Exception::Ecall { pc }) => {
                self.handle_exception(Exception::Ecall { pc });
                Some(Exception::Ecall { pc })
            }
            Err(exception) => {
                self.handle_exception(exception);
                None
            }
            Ok(()) => None,
        };
        self.registers[0] = 0;
        ret
    }
    fn handle_exception(&mut self, exception: Exception) {
        match exception {
            Exception::InstructionAddressMisaligned { pc } => {
                self.csrs.write_exception(pc, 0, 0);
            }
            Exception::IllegalInstruction { pc, instruction } => {
                self.csrs.write_exception(pc, 2, instruction as u64);
            }
            Exception::Breakpoint { pc } => {
                panic!("EBREAK: 0x{pc:x}");
            }
            Exception::LoadAccessFault { pc, addr } => {
                self.csrs.write_exception(pc, 5, addr);
            }
            Exception::StoreAccessFault { pc, addr } => {
                self.csrs.write_exception(pc, 7, addr);
            }
            Exception::Ecall { pc } => {
                self.csrs.write_exception(pc, 0, 0); // needs rework
            }
        }
        self.pc = self.csrs.mtvec();
    }
    fn read_csr(&mut self, addr: u64, pc: u64, instruction: u32) -> Result<u64, Exception> {
        Ok(self.csrs.read(addr))
    }
    fn write_csr(&mut self, addr: u64, val: u64, pc: u64, instruction: u32) -> Result<(), Exception> {
        if addr & 0b1100_0000_0000 == 0b1100_0000_0000 {
            return Err(Exception::IllegalInstruction { pc, instruction });
        }
        self.csrs.write(addr, val);
        Ok(())
    }
    fn step_inner(&mut self) -> Result<(), Exception> {
        let instruction = self.mem.read_word(self.pc);

        let opcode = instruction & 0b111_1111;

        match opcode {
            0b0110111 => {
                // LUI
                let decoded = UType::decode(instruction);
                self.registers[decoded.rd as usize] = sext32(decoded.imm);
            }
            0b0010111 => {
                // AUIPC
                let decoded = UType::decode(instruction);
                self.registers[decoded.rd as usize] = self.pc.wrapping_add(sext32(decoded.imm));
            }
            0b1101111 => {
                // JAL
                let decoded = JType::decode(instruction);
                self.registers[decoded.rd as usize] = self.pc.wrapping_add(4);
                self.pc = self.pc.wrapping_add(sext32(decoded.imm));
                return Ok(());
            }
            0b1100111 => {
                // JALR
                let decoded = IType::decode(instruction);
                if decoded.funct3 != 0 {
                    return Err(Exception::IllegalInstruction {
                        pc: self.pc,
                        instruction,
                    });
                }
                let target =
                    self.registers[decoded.rs1 as usize].wrapping_add(sext32(decoded.imm)) & (!1);
                self.registers[decoded.rd as usize] = self.pc.wrapping_add(4);
                self.pc = target;
                return Ok(());
            }
            0b1100011 => {
                // branch
                let decoded = BType::decode(instruction);
                let src1 = self.registers[decoded.rs1 as usize];
                let src2 = self.registers[decoded.rs2 as usize];
                let target = self.pc.wrapping_add(sext32(decoded.imm));
                let branch = match decoded.funct3 {
                    0 => {
                        // BEQ
                        src1 == src2
                    }
                    1 => {
                        // BNE
                        src1 != src2
                    }
                    4 => {
                        // BLT
                        (src1 as i64) < (src2 as i64)
                    }
                    5 => {
                        // BGE
                        (src1 as i64) >= (src2 as i64)
                    }
                    6 => {
                        // BLTU
                        src1 < src2
                    }
                    7 => {
                        // BGEU
                        src1 >= src2
                    }
                    _ => {
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction,
                        });
                    }
                };
                if branch {
                    self.pc = target;
                    return Ok(());
                }
            }
            0b0000011 => {
                // loads
                let decoded = IType::decode(instruction);
                let addr = self.registers[decoded.rs1 as usize].wrapping_add(sext32(decoded.imm));
                let val = match decoded.funct3 {
                    0 => {
                        // LB
                        sext8(self.mem.read_byte(addr))
                    }
                    1 => {
                        // LH
                        sext16(self.mem.read_hword(addr))
                    }
                    2 => {
                        // LW
                        sext32(self.mem.read_word(addr))
                    }
                    3 => {
                        // LD
                        self.mem.read_dword(addr)
                    }
                    4 => {
                        // LBU
                        self.mem.read_byte(addr) as u64
                    }
                    5 => {
                        // LHU
                        self.mem.read_hword(addr) as u64
                    }
                    6 => {
                        // LWU
                        self.mem.read_word(addr) as u64
                    }
                    _ => {
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction,
                        });
                    }
                };
                self.registers[decoded.rd as usize] = val;
            }
            0b0100011 => {
                // stores
                let decoded = SType::decode(instruction);
                let addr = self.registers[decoded.rs1 as usize].wrapping_add(sext32(decoded.imm));
                let val = self.registers[decoded.rs2 as usize];
                match decoded.funct3 {
                    0 => {
                        // SB
                        self.mem.write_byte(addr, val as u8);
                    }
                    1 => {
                        // SH
                        self.mem.write_hword(addr, val as u16);
                    }
                    2 => {
                        // SW
                        self.mem.write_word(addr, val as u32);
                    }
                    3 => {
                        // SD
                        self.mem.write_dword(addr, val);
                    }
                    _ => {
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction,
                        });
                    }
                }
            }
            0b0010011 => {
                // register-immediate alu ops
                let decoded = IType::decode(instruction);
                let val = self.registers[decoded.rs1 as usize];
                let reg = &mut self.registers[decoded.rd as usize];
                match decoded.funct3 {
                    0 => {
                        // ADDI
                        *reg = val.wrapping_add(sext32(decoded.imm));
                    }
                    1 => {
                        // SLLI
                        if decoded.imm >= 64 {
                            return Err(Exception::IllegalInstruction {
                                pc: self.pc,
                                instruction,
                            });
                        }
                        *reg = val << decoded.imm;
                    }
                    2 => {
                        // SLTI
                        *reg = ((val as i64) < (sext32(decoded.imm) as i64)) as u64
                    }
                    3 => {
                        // SLTIU
                        *reg = (val < sext32(decoded.imm)) as u64
                    }
                    4 => {
                        // XORI
                        *reg = val ^ sext32(decoded.imm);
                    }
                    5 => {
                        // SRLI + SRAI
                        let is_arith = (decoded.imm & 0b100_0000_0000) != 0;
                        let shamt = decoded.imm & (!0b100_0000_0000);
                        if shamt >= 64 {
                            return Err(Exception::IllegalInstruction {
                                pc: self.pc,
                                instruction,
                            });
                        }
                        if is_arith {
                            *reg = ((val as i64) >> shamt) as u64;
                        } else {
                            *reg = val >> shamt;
                        }
                    }
                    6 => {
                        // ORI
                        *reg = val | sext32(decoded.imm);
                    }
                    7 => {
                        // ANDI
                        *reg = val & sext32(decoded.imm);
                    }
                    _ => {
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction,
                        });
                    }
                }
            }
            0b0011011 => {
                // 32-bit register-immediate alu ops
                let decoded = IType::decode(instruction);
                let val = self.registers[decoded.rs1 as usize] as u32;
                let reg = &mut self.registers[decoded.rd as usize];
                match decoded.funct3 {
                    0 => {
                        // ADDIW
                        *reg = sext32(val.wrapping_add(decoded.imm))
                    }
                    1 => {
                        // SLLIW
                        if decoded.imm >= 32 {
                            return Err(Exception::IllegalInstruction {
                                pc: self.pc,
                                instruction,
                            });
                        }
                        *reg = sext32(val << decoded.imm);
                    }
                    5 => {
                        // SRLIW + SRAIW
                        let is_arith = (decoded.imm & 0b100_0000_0000) != 0;
                        let shamt = decoded.imm & (!0b100_0000_0000);
                        if shamt >= 32 {
                            return Err(Exception::IllegalInstruction {
                                pc: self.pc,
                                instruction,
                            });
                        }
                        if is_arith {
                            *reg = sext32(((val as i32) >> shamt) as u32);
                        } else {
                            *reg = sext32(val >> shamt);
                        }
                    }
                    _ => {
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction,
                        });
                    }
                }
            }
            0b0110011 => {
                // register-register alu ops
                let decoded = RType::decode(instruction);
                let src1 = self.registers[decoded.rs1 as usize];
                let src2 = self.registers[decoded.rs2 as usize];
                let reg = &mut self.registers[decoded.rd as usize];
                match (decoded.funct7, decoded.funct3) {
                    (0, 0) => {
                        // ADD
                        *reg = src1.wrapping_add(src2);
                    }
                    (0b0100000, 0) => {
                        // SUB
                        *reg = src1.wrapping_sub(src2);
                    }
                    (0, 1) => {
                        // SLL
                        *reg = src1 << (src2 & 0b11_1111);
                    }
                    (0, 2) => {
                        // SLT
                        *reg = ((src1 as i64) < (src2 as i64)) as u64;
                    }
                    (0, 3) => {
                        // SLTU
                        *reg = (src1 < src2) as u64;
                    }
                    (0, 4) => {
                        // XOR
                        *reg = src1 ^ src2;
                    }
                    (0, 5) => {
                        // SRL
                        *reg = src1 >> (src2 & 0b11_1111);
                    }
                    (0b0100000, 5) => {
                        // SRA
                        *reg = ((src1 as i64) >> (src2 & 0b11_1111)) as u64;
                    }
                    (0, 6) => {
                        // OR
                        *reg = src1 | src2;
                    }
                    (0, 7) => {
                        // AND
                        *reg = src1 & src2;
                    }
                    (_, _) => {
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction,
                        });
                    }
                }
            }
            0b0111011 => {
                // 32-bit register-register alu ops
                let decoded = RType::decode(instruction);
                let src1 = self.registers[decoded.rs1 as usize] as u32;
                let src2 = self.registers[decoded.rs2 as usize] as u32;
                let reg = &mut self.registers[decoded.rd as usize];
                match (decoded.funct7, decoded.funct3) {
                    (0, 0) => {
                        // ADDW
                        *reg = sext32(src1.wrapping_add(src2));
                    }
                    (0b0100000, 0) => {
                        // SUBW
                        *reg = sext32(src1.wrapping_sub(src2));
                    }
                    (0, 1) => {
                        // SLLW
                        *reg = sext32(src1 << (src2 & 0b1_1111));
                    }
                    (0, 5) => {
                        // SRLW
                        *reg = sext32(src1 >> (src2 & 0b1_1111));
                    }
                    (0b0100000, 5) => {
                        // SRAW
                        *reg = sext32(((src1 as i32) >> (src2 & 0b1_1111)) as u32);
                    }
                    (_, _) => {
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction,
                        });
                    }
                }
            }
            0b0001111 => {} // fence stuff which is a NOP in this emulator
            0b1110011 => {
                // ECALL + EBREAK + Zicsr stuff
                let mut decoded = IType::decode(instruction);
                decoded.imm &= 0b1111_1111_1111;
                let csr = decoded.imm as u64;
                match decoded.funct3 {
                    0 => {
                        if instruction == 0b00110000001000000000000001110011 {
                            self.pc = self.read_csr(0x341, self.pc, instruction)?;
                            return Ok(());
                        }
                        return Err(Exception::Ecall { pc: self.pc });
                    }
                    1 => {
                        // CSRRW
                        if decoded.rd != 0 {
                            self.registers[decoded.rd as usize] = self.read_csr(csr, self.pc, instruction)?;
                        }
                        self.write_csr(csr, self.registers[decoded.rs1 as usize], self.pc, instruction)?;
                    }
                    2 => {
                        // CSRRS
                        self.registers[decoded.rd as usize] = self.read_csr(csr, self.pc, instruction)?;
                        if decoded.rs1 != 0 {
                            self.write_csr(csr, self.registers[decoded.rd as usize] | self.registers[decoded.rs1 as usize], self.pc, instruction)?;
                        }
                    }
                    3 => {
                        // CSRRC
                        self.registers[decoded.rd as usize] = self.read_csr(csr, self.pc, instruction)?;
                        if decoded.rs1 != 0 {
                            self.write_csr(csr, self.registers[decoded.rd as usize] & !self.registers[decoded.rs1 as usize], self.pc, instruction)?;
                        }
                    }
                    5 => {
                        // CSRRWI
                        if decoded.rd != 0 {
                            self.registers[decoded.rd as usize] = self.read_csr(csr, self.pc, instruction)?;
                        }
                        self.write_csr(csr, decoded.rs1 as u64, self.pc, instruction)?;
                    }
                    6 => {
                        // CSRRSI
                        self.registers[decoded.rd as usize] = self.read_csr(csr, self.pc, instruction)?;
                        if decoded.rs1 != 0 {
                            self.write_csr(csr, self.registers[decoded.rd as usize] | decoded.rs1 as u64, self.pc, instruction)?;
                        }
                    }
                    7 => {
                        // CSRRCI
                        self.registers[decoded.rd as usize] = self.read_csr(csr, self.pc, instruction)?;
                        if decoded.rs1 != 0 {
                            self.write_csr(csr, self.registers[decoded.rd as usize] & !decoded.rs1 as u64, self.pc, instruction)?;
                        }
                    }
                    _ => {
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction,
                        });
                    }
                }
            }
            _ => {
                return Err(Exception::IllegalInstruction {
                    pc: self.pc,
                    instruction,
                });
            }
        }

        self.pc += 4;

        Ok(())
    }
}
