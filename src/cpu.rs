use crate::cpu::{
    csrs::Csrs,
    decoder::{
        BType, CAType, CBType, CIType, CIWType, CJType, CLType, CRType, CSSType, CSType, IType,
        JType, RType, SType, UType, sext,
    },
};

mod csrs;
mod decoder;

pub struct Memory {
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

#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Priviledge {
    #[default]
    Machine = 3,
    Hypervisor = 2,
    Supervisor = 1,
    User = 0,
}
impl From<u64> for Priviledge {
    fn from(value: u64) -> Self {
        use Priviledge::*;
        match value {
            3 => Machine,
            2 => Hypervisor,
            1 => Supervisor,
            0 => User,
            _ => panic!("invalid priviledge mode: {value} should be 0-3"),
        }
    }
}

pub struct Cpu {
    pub registers: [u64; 32],
    pub pc: u64,
    pub csrs: Csrs,
    priviledge: Priviledge,
    pub mem: Memory,
}
impl Cpu {
    pub fn new(mem: Vec<u8>) -> Cpu {
        Self {
            registers: [0; 32],
            pc: 0,
            mem: Memory { mem },
            priviledge: Priviledge::Machine,
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
        let (priviledge, tvec) = match exception {
            Exception::InstructionAddressMisaligned { pc } => {
                self.csrs.write_exception(self.priviledge, pc, 0, 0)
            }
            Exception::IllegalInstruction { pc, instruction } => {
                self.csrs
                    .write_exception(self.priviledge, pc, 2, instruction as u64)
            }
            Exception::Breakpoint { pc } => {
                self.csrs.write_exception(self.priviledge, pc, 3, 0) // needs rework
            }
            Exception::LoadAccessFault { pc, addr } => {
                self.csrs.write_exception(self.priviledge, pc, 5, addr)
            }
            Exception::StoreAccessFault { pc, addr } => {
                self.csrs.write_exception(self.priviledge, pc, 7, addr)
            }
            Exception::Ecall { pc } => {
                let cause = match self.priviledge {
                    Priviledge::Machine => 11,
                    Priviledge::Hypervisor => unimplemented!(),
                    Priviledge::Supervisor => 9,
                    Priviledge::User => 8,
                };
                self.csrs.write_exception(self.priviledge, pc, cause, 0)
            }
        };
        self.pc = tvec & !0b11;
        self.priviledge = priviledge;
    }
    fn read_csr(&mut self, addr: u64, pc: u64, instruction: u32) -> Result<u64, Exception> {
        if Priviledge::from((addr & 0b0011_0000_0000) >> 8) > self.priviledge {
            return Err(Exception::IllegalInstruction { pc, instruction });
        }
        Ok(self.csrs.read(addr))
    }
    fn write_csr(
        &mut self,
        addr: u64,
        val: u64,
        pc: u64,
        instruction: u32,
    ) -> Result<(), Exception> {
        if addr & 0b1100_0000_0000 == 0b1100_0000_0000 {
            return Err(Exception::IllegalInstruction { pc, instruction });
        }
        self.csrs.write(addr, val);
        Ok(())
    }
    fn step_inner(&mut self) -> Result<(), Exception> {
        let compressed_instruction = self.mem.read_hword(self.pc);

        if compressed_instruction & 0b11 != 0b11 {
            return self.execute_compressed(compressed_instruction);
        }

        let instruction = ((self.mem.read_hword(self.pc.wrapping_add(2)) as u32) << 16)
            | compressed_instruction as u32;

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
                    (1, 0) => {
                        // MUL
                        *reg = src1.wrapping_mul(src2);
                    }
                    (1, 1) => {
                        // MULH
                        *reg = ((src1 as i64 as i128 * src2 as i64 as i128) >> 64) as u64;
                    }
                    (1, 2) => {
                        // MULHSU
                        *reg = ((src1 as i64 as i128 * src2 as i128) >> 64) as u64;
                    }
                    (1, 3) => {
                        // MULHU
                        *reg = ((src1 as u128 * src2 as u128) >> 64) as u64;
                    }
                    (1, 4) => {
                        // DIV
                        if src2 == 0 {
                            *reg = u64::MAX;
                        } else {
                            *reg = (src1 as i64).checked_div(src2 as i64).unwrap_or(i64::MIN) as u64;
                        }
                    }
                    (1, 5) => {
                        // DIVU
                        if src2 == 0 {
                            *reg = u64::MAX;
                        } else {
                            *reg = src1 / src2;
                        }
                    }
                    (1, 6) => {
                        // REM
                        if src2 == 0 {
                            *reg = src1;
                        } else {
                            *reg = (src1 as i64).checked_rem(src2 as i64).unwrap_or(0) as u64;
                        }
                    }
                    (1, 7) => {
                        // REMU
                        if src2 == 0 {
                            *reg = src1
                        } else {
                            *reg = src1 % src2
                        }
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
                    (1, 0) => {
                        // MULW
                        *reg = sext32(src1.wrapping_mul(src2));
                    }
                    (1, 4) => {
                        // DIVW
                        if src2 == 0 {
                            *reg = u64::MAX;
                        } else {
                            *reg = sext32((src1 as i32).checked_div(src2 as i32).unwrap_or(i32::MIN) as u32);
                        }
                    }
                    (1, 5) => {
                        // DIVUW
                        if src2 == 0 {
                            *reg = u64::MAX;
                        } else {
                            *reg = sext32(src1 / src2);
                        }
                    }
                    (1, 6) => {
                        // REMW
                        if src2 == 0 {
                            *reg = sext32(src1);
                        } else {
                            *reg = sext32((src1 as i32).checked_rem(src2 as i32).unwrap_or(0) as u32);
                        }
                    }
                    (1, 7) => {
                        // REMUW
                        if src2 == 0 {
                            *reg = sext32(src1)
                        } else {
                            *reg = sext32(src1 % src2)
                        }
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
                // System instruction
                let mut decoded = IType::decode(instruction);
                decoded.imm &= 0b1111_1111_1111;
                let csr = decoded.imm as u64;
                match decoded.funct3 {
                    0 => {
                        let decoded = RType::decode(instruction);

                        match decoded.rs2 {
                            0 => {
                                // ECALL
                                if decoded.funct7 != 0 || decoded.rs1 != 0 || decoded.rd != 0 {
                                    return Err(Exception::IllegalInstruction {
                                        pc: self.pc,
                                        instruction,
                                    });
                                }

                                return Err(Exception::Ecall { pc: self.pc });
                            }
                            1 => {
                                // EBREAK
                                if decoded.funct7 != 0 || decoded.rs1 != 0 || decoded.rd != 0 {
                                    return Err(Exception::IllegalInstruction {
                                        pc: self.pc,
                                        instruction,
                                    });
                                }

                                return Err(Exception::Breakpoint { pc: self.pc });
                            }
                            2 => {
                                // interrupt return
                                if decoded.rs1 != 0 || decoded.rd != 0 {
                                    return Err(Exception::IllegalInstruction {
                                        pc: self.pc,
                                        instruction,
                                    });
                                }
                                match decoded.funct7 {
                                    0b0001000 => {
                                        // sret
                                        if self.priviledge < Priviledge::Supervisor {
                                            return Err(Exception::IllegalInstruction {
                                                pc: self.pc,
                                                instruction,
                                            });
                                        }
                                        todo!();
                                    }
                                    0b0011000 => {
                                        // mret
                                        if self.priviledge < Priviledge::Machine {
                                            return Err(Exception::IllegalInstruction {
                                                pc: self.pc,
                                                instruction,
                                            });
                                        }
                                        self.pc = self.read_csr(0x341, self.pc, instruction)?;
                                        self.priviledge = self.csrs.mret();
                                        return Ok(());
                                    }
                                    _ => {
                                        return Err(Exception::IllegalInstruction {
                                            pc: self.pc,
                                            instruction,
                                        });
                                    }
                                }
                            }
                            5 => {
                                // wfi
                                todo!("wfi");
                            }
                            _ => {
                                return Err(Exception::IllegalInstruction {
                                    pc: self.pc,
                                    instruction,
                                });
                            }
                        }
                    }
                    1 => {
                        // CSRRW
                        let val = if decoded.rd != 0 {
                            self.read_csr(csr, self.pc, instruction)?
                        } else {
                            0
                        };
                        self.write_csr(
                            csr,
                            self.registers[decoded.rs1 as usize],
                            self.pc,
                            instruction,
                        )?;
                        self.registers[decoded.rd as usize] = val;
                    }
                    2 => {
                        // CSRRS
                        let val = self.read_csr(csr, self.pc, instruction)?;
                        if decoded.rs1 != 0 {
                            self.write_csr(
                                csr,
                                val | self.registers[decoded.rs1 as usize],
                                self.pc,
                                instruction,
                            )?;
                        }
                        self.registers[decoded.rd as usize] = val;
                    }
                    3 => {
                        // CSRRC
                        let val = self.read_csr(csr, self.pc, instruction)?;
                        if decoded.rs1 != 0 {
                            self.write_csr(
                                csr,
                                val & !self.registers[decoded.rs1 as usize],
                                self.pc,
                                instruction,
                            )?;
                        }
                        self.registers[decoded.rd as usize] = val;
                    }
                    5 => {
                        // CSRRWI
                        if decoded.rd != 0 {
                            self.registers[decoded.rd as usize] =
                                self.read_csr(csr, self.pc, instruction)?;
                        }
                        self.write_csr(csr, decoded.rs1 as u64, self.pc, instruction)?;
                    }
                    6 => {
                        // CSRRSI
                        self.registers[decoded.rd as usize] =
                            self.read_csr(csr, self.pc, instruction)?;
                        if decoded.rs1 != 0 {
                            self.write_csr(
                                csr,
                                self.registers[decoded.rd as usize] | decoded.rs1 as u64,
                                self.pc,
                                instruction,
                            )?;
                        }
                    }
                    7 => {
                        // CSRRCI
                        self.registers[decoded.rd as usize] =
                            self.read_csr(csr, self.pc, instruction)?;
                        if decoded.rs1 != 0 {
                            self.write_csr(
                                csr,
                                self.registers[decoded.rd as usize] & !decoded.rs1 as u64,
                                self.pc,
                                instruction,
                            )?;
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
    fn execute_compressed(&mut self, instruction: u16) -> Result<(), Exception> {
        let quadrant = instruction & 0b11;
        let funct3 = instruction >> 13;
        match quadrant {
            0b00 => {
                match funct3 {
                    0 => {
                        // C.ADDI4SPN
                        let decoded = CIWType::decode(instruction);

                        if decoded.imm == 0 {
                            return Err(Exception::IllegalInstruction {
                                pc: self.pc,
                                instruction: instruction as u32,
                            });
                        }

                        self.registers[decoded.rd as usize] = self.registers[2] + decoded.imm as u64;
                    }
                    1 => {
                        // C.FLD
                        // TODO: D extension
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction: instruction as u32,
                        });
                    }
                    2 => {
                        // C.LW
                        let decoded = CLType::decode(instruction);

                        let imm = decoded.imm;
                        let offset = ((imm & 0b0001_1100_0000_0000) >> 7)
                            | ((imm & 0b0000_0000_0100_0000) >> 4)
                            | ((imm & 0b0000_0000_0010_0000) << 1);

                        self.registers[decoded.rd as usize] = sext32(
                            self.mem
                                .read_word(self.registers[decoded.rs1 as usize] + offset as u64),
                        );
                    }
                    3 => {
                        // C.LD
                        let decoded = CLType::decode(instruction);

                        let imm = decoded.imm;
                        let offset = ((imm & 0b0001_1100_0000_0000) >> 7)
                            | ((imm & 0b0000_0000_0110_0000) << 1);

                        self.registers[decoded.rd as usize] = self
                            .mem
                            .read_dword(self.registers[decoded.rs1 as usize] + offset as u64);
                    }
                    5 => {
                        // C.FSD
                        // TODO: D extension
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction: instruction as u32,
                        });
                    }
                    6 => {
                        // C.SW
                        let decoded = CSType::decode(instruction);

                        let imm = decoded.imm;
                        let offset = ((imm & 0b0001_1100_0000_0000) >> 7)
                            | ((imm & 0b0000_0000_0100_0000) >> 4)
                            | ((imm & 0b0000_0000_0010_0000) << 1);

                        self.mem.write_word(
                            self.registers[decoded.rs1 as usize] + offset as u64,
                            self.registers[decoded.rs2 as usize] as u32,
                        );
                    }
                    7 => {
                        // C.SD
                        let decoded = CSType::decode(instruction);

                        let imm = decoded.imm;
                        let offset = ((imm & 0b0001_1100_0000_0000) >> 7)
                            | ((imm & 0b0000_0000_0110_0000) << 1);

                        self.mem.write_dword(
                            self.registers[decoded.rs1 as usize] + offset as u64,
                            self.registers[decoded.rs2 as usize],
                        );
                    }
                    _ => {
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction: instruction as u32,
                        });
                    }
                }
            }
            0b01 => {
                match funct3 {
                    0 => {
                        // C.ADDI
                        let decoded = CIType::decode(instruction);

                        let imm = decoded.imm;
                        let imm = ((imm & 0b0001_0000_0000_0000) >> 7)
                            | ((imm & 0b0000_0000_0111_1100) >> 2);

                        self.registers[decoded.r1 as usize] = self.registers[decoded.r1 as usize]
                            .wrapping_add(sext32(sext(imm as u32, 6)));
                    }
                    1 => {
                        // C.ADDIW
                        let decoded = CIType::decode(instruction);

                        if decoded.r1 == 0 {
                            return Err(Exception::IllegalInstruction {
                                pc: self.pc,
                                instruction: instruction as u32,
                            });
                        }

                        let imm = decoded.imm;
                        let imm = ((imm & 0b0001_0000_0000_0000) >> 7)
                            | ((imm & 0b0000_0000_0111_1100) >> 2);

                        let val = (self.registers[decoded.r1 as usize] as u32)
                            .wrapping_add(sext(imm as u32, 6));

                        self.registers[decoded.r1 as usize] = sext32(val);
                    }
                    2 => {
                        // C.LI
                        let decoded = CIType::decode(instruction);

                        let imm = decoded.imm;
                        let imm = ((imm & 0b0001_0000_0000_0000) >> 7)
                            | ((imm & 0b0000_0000_0111_1100) >> 2);

                        self.registers[decoded.r1 as usize] = sext32(sext(imm as u32, 6));
                    }
                    3 => {
                        // C.ADDI16SP + C.LUI
                        let decoded = CIType::decode(instruction);

                        let imm = decoded.imm;
                        if imm == 0 {
                            return Err(Exception::IllegalInstruction {
                                pc: self.pc,
                                instruction: instruction as u32,
                            });
                        }
                        if decoded.r1 == 2 {
                            // C.ADDI16SP
                            let imm = ((imm & 0b0001_0000_0000_0000) >> 3)
                                | ((imm & 0b0000_0000_0100_0000) >> 2)
                                | ((imm & 0b0000_0000_0010_0000) << 1)
                                | ((imm & 0b0000_0000_0001_1000) << 4)
                                | ((imm & 0b0000_0000_0000_0100) << 3);
                            let imm = sext(imm as u32, 10);

                            self.registers[2] = self.registers[2].wrapping_add(sext32(imm));
                        } else {
                            // C.LUI
                            let imm = ((imm as u32 & 0b0001_0000_0000_0000) << 5)
                                | ((imm as u32 & 0b0000_0000_0111_1100) << 10);
                            let imm = sext(imm, 18);

                            self.registers[decoded.r1 as usize] = sext32(imm);
                        }
                    }
                    4 => {
                        let selector = (instruction & 0b0000_1100_0000_0000) >> 10;
                        match selector {
                            0 => {
                                // C.SRLI
                                let decoded = CBType::decode(instruction);

                                let imm = decoded.offset;
                                let shamt = ((imm & 0b0001_0000_0000_0000) >> 7)
                                    | ((imm & 0b0000_0000_0111_1100) >> 2);

                                self.registers[decoded.r1 as usize] >>= shamt;
                            }
                            1 => {
                                // C.SRAI
                                let decoded = CBType::decode(instruction);

                                let imm = decoded.offset;
                                let shamt = ((imm & 0b0001_0000_0000_0000) >> 7)
                                    | ((imm & 0b0000_0000_0111_1100) >> 2);

                                self.registers[decoded.r1 as usize] =
                                    ((self.registers[decoded.r1 as usize] as i64) >> shamt) as u64;
                            }
                            2 => {
                                // C.ANDI
                                let decoded = CBType::decode(instruction);

                                let imm = decoded.offset;
                                let imm = ((imm & 0b0001_0000_0000_0000) >> 7)
                                    | ((imm & 0b0000_0000_0111_1100) >> 2);

                                self.registers[decoded.r1 as usize] &= sext32(sext(imm as u32, 6))
                            }
                            3 => {
                                // the other stuff
                                let decoded = CAType::decode(instruction);

                                let rs2 = self.registers[decoded.rs2 as usize];
                                let r1 = &mut self.registers[decoded.r1 as usize];
                                match ((decoded.funct6 & 0b100) >> 2, decoded.funct2) {
                                    (0, 0) => {
                                        // C.SUB
                                        *r1 = r1.wrapping_sub(rs2);
                                    }
                                    (0, 1) => {
                                        // C.XOR
                                        *r1 ^= rs2
                                    }
                                    (0, 2) => {
                                        // C.OR
                                        *r1 |= rs2
                                    }
                                    (0, 3) => {
                                        // C.AND
                                        *r1 &= rs2
                                    }
                                    (1, 0) => {
                                        // C.SUBW
                                        *r1 = sext32(r1.wrapping_sub(rs2) as u32)
                                    }
                                    (1, 1) => {
                                        // C.ADDW
                                        *r1 = sext32(r1.wrapping_add(rs2) as u32)
                                    }
                                    _ => {
                                        return Err(Exception::IllegalInstruction {
                                            pc: self.pc,
                                            instruction: instruction as u32,
                                        });
                                    }
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                    5 => {
                        // C.J
                        let decoded = CJType::decode(instruction);

                        self.pc = self.pc.wrapping_add(sext32(decoded.target));

                        return Ok(());
                    }
                    6 => {
                        // C.BEQZ
                        let decoded = CBType::decode(instruction);

                        let offset = decoded.decode_branch_offset();

                        let branch = self.registers[decoded.r1 as usize] == 0;

                        if branch {
                            self.pc = self.pc.wrapping_add(sext32(offset));
                            return Ok(());
                        }
                    }
                    7 => {
                        // C.BNEZ
                        let decoded = CBType::decode(instruction);

                        let offset = decoded.decode_branch_offset();

                        let branch = self.registers[decoded.r1 as usize] != 0;

                        if branch {
                            self.pc = self.pc.wrapping_add(sext32(offset));
                            return Ok(());
                        }
                    }
                    _ => {
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction: instruction as u32,
                        });
                    }
                }
            }
            0b10 => {
                match funct3 {
                    0 => {
                        // C.SLLI
                        let decoded = CIType::decode(instruction);

                        let imm = decoded.imm;
                        let imm = ((imm & 0b0001_0000_0000_0000) >> 7)
                            | ((imm & 0b0000_0000_0111_1100) >> 2);

                        self.registers[decoded.r1 as usize] <<= imm;
                    }
                    1 => {
                        // C.FLDSP
                        // TODO: D extension
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction: instruction as u32,
                        });
                    }
                    2 => {
                        // C.LWSP
                        let decoded = CIType::decode(instruction);

                        let imm = decoded.imm;
                        let imm = ((imm & 0b0001_0000_0000_0000) >> 7)
                            | ((imm & 0b0000_0000_0111_0000) >> 2)
                            | ((imm & 0b0000_0000_0000_1100) << 4);

                        if decoded.r1 == 0 {
                            return Err(Exception::IllegalInstruction {
                                pc: self.pc,
                                instruction: instruction as u32,
                            });
                        }

                        self.registers[decoded.r1 as usize] = sext32(
                            self.mem
                                .read_word(self.registers[2].wrapping_add(imm as u64)),
                        );
                    }
                    3 => {
                        // C.LDSP
                        let decoded = CIType::decode(instruction);

                        let imm = decoded.imm;
                        let imm = ((imm & 0b0001_0000_0000_0000) >> 7)
                            | ((imm & 0b0000_0000_0110_0000) >> 2)
                            | ((imm & 0b0000_0000_0001_1100) << 4);

                        if decoded.r1 == 0 {
                            return Err(Exception::IllegalInstruction {
                                pc: self.pc,
                                instruction: instruction as u32,
                            });
                        }

                        self.registers[decoded.r1 as usize] = self
                            .mem
                            .read_dword(self.registers[2].wrapping_add(imm as u64));
                    }
                    4 => {
                        // bunch of stuff
                        let decoded = CRType::decode(instruction);
                        match (decoded.funct4 & 1, decoded.r1, decoded.rs2) {
                            (0, rs1, 0) => {
                                // C.JR
                                if rs1 == 0 {
                                    return Err(Exception::IllegalInstruction {
                                        pc: self.pc,
                                        instruction: instruction as u32,
                                    });
                                }
                                self.pc = self.registers[rs1 as usize];
                                return Ok(());
                            }
                            (0, rd, rs2) => {
                                // C.MV
                                self.registers[rd as usize] = self.registers[rs2 as usize]
                            }
                            (1, 0, 0) => {
                                // C.EBREAK
                                return Err(Exception::Breakpoint { pc: self.pc });
                            }
                            (1, rs1, 0) => {
                                // C.JALR
                                let target = self.registers[rs1 as usize];
                                self.registers[1] = self.pc.wrapping_add(2);
                                self.pc = target;
                                return Ok(());
                            }
                            (1, r1, rs2) => {
                                // C.ADD
                                self.registers[r1 as usize] = self.registers[r1 as usize]
                                    .wrapping_add(self.registers[rs2 as usize]);
                            }
                            _ => unreachable!(),
                        }
                    }
                    5 => {
                        // C.FSDSP
                        // TODO: D extension
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction: instruction as u32,
                        });
                    }
                    6 => {
                        // C.SWSP
                        let decoded = CSSType::decode(instruction);

                        self.mem.write_word(
                            self.registers[2].wrapping_add(decoded.imm as u64),
                            self.registers[decoded.rs2 as usize] as u32,
                        );
                    }
                    7 => {
                        // C.SDSP
                        let decoded = CSSType::decode(instruction);

                        self.mem.write_dword(
                            self.registers[2].wrapping_add(decoded.imm as u64),
                            self.registers[decoded.rs2 as usize],
                        );
                    }
                    _ => {
                        return Err(Exception::IllegalInstruction {
                            pc: self.pc,
                            instruction: instruction as u32,
                        });
                    }
                }
            }
            _ => unreachable!(),
        }

        self.pc += 2;

        Ok(())
    }
}
