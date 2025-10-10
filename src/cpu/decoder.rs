pub const fn sext(x: u32, bits: u8) -> u32 {
    let shift = 32 - bits as i8;
    (((x << shift) as i32) >> shift) as u32
}

#[derive(Debug)]
pub struct RType {
    pub rd: u8,
    pub rs1: u8,
    pub rs2: u8,
    pub funct3: u8,
    pub funct7: u8,
}
impl RType {
    pub const fn decode(x: u32) -> Self {
        Self {
            rd: ((x >> 7) & 0b1_1111) as u8,
            rs1: ((x >> 15) & 0b1_1111) as u8,
            rs2: ((x >> 20) & 0b1_1111) as u8,
            funct3: ((x >> 12) & 0b111) as u8,
            funct7: ((x >> 25) & 0b111_1111) as u8,
        }
    }
}

#[derive(Debug)]
pub struct IType {
    pub rd: u8,
    pub rs1: u8,
    pub funct3: u8,
    pub imm: u32,
}
impl IType {
    pub const fn decode(x: u32) -> Self {
        Self {
            rd: ((x >> 7) & 0b1_1111) as u8,
            rs1: ((x >> 15) & 0b1_1111) as u8,
            funct3: ((x >> 12) & 0b111) as u8,
            imm: sext(x >> 20, 12),
        }
    }
}

#[derive(Debug)]
pub struct SType {
    pub rs1: u8,
    pub rs2: u8,
    pub funct3: u8,
    pub imm: u32,
}
impl SType {
    pub const fn decode(x: u32) -> Self {
        Self {
            rs1: ((x >> 15) & 0b1_1111) as u8,
            rs2: ((x >> 20) & 0b1_1111) as u8,
            funct3: ((x >> 12) & 0b111) as u8,
            imm: sext(((x >> 20) & 0b1111_1110_0000) | ((x >> 7) & 0b1_1111), 12),
        }
    }
}
#[derive(Debug)]
pub struct BType {
    pub rs1: u8,
    pub rs2: u8,
    pub funct3: u8,
    pub imm: u32,
}
impl BType {
    pub const fn decode(x: u32) -> Self {
        #[rustfmt::skip]
        let mut imm =
            (x >> 7)  & 0b0_0000_0001_1110 |
            (x >> 20) & 0b0_0111_1110_0000 |
            (x << 4)  & 0b0_1000_0000_0000 |
            (x >> 19) & 0b1_0000_0000_0000;
        imm = sext(imm, 13);
        Self {
            rs1: ((x >> 15) & 0b1_1111) as u8,
            rs2: ((x >> 20) & 0b1_1111) as u8,
            funct3: ((x >> 12) & 0b111) as u8,
            imm,
        }
    }
}

#[derive(Debug)]
pub struct UType {
    pub rd: u8,
    pub imm: u32,
}
impl UType {
    pub const fn decode(x: u32) -> Self {
        Self {
            rd: ((x >> 7) & 0b1_1111) as u8,
            imm: x & 0xffff_f000,
        }
    }
}

#[derive(Debug)]
pub struct JType {
    pub rd: u8,
    pub imm: u32,
}
impl JType {
    pub const fn decode(x: u32) -> Self {
        #[rustfmt::skip]
        let mut imm =
            (x >> 20) & 0b0_0000_0000_0111_1111_1110 |
            (x >> 9)  & 0b0_0000_0000_1000_0000_0000 |
             x        & 0b0_1111_1111_0000_0000_0000 |
            (x >> 11) & 0b1_0000_0000_0000_0000_0000;
        imm = sext(imm, 21);
        Self {
            rd: ((x >> 7) & 0b1_1111) as u8,
            imm,
        }
    }
}

// Compressed instructions

#[derive(Debug)]
pub struct CRType {
    pub r1: u8,
    pub rs2: u8,
    pub funct4: u8,
}
impl CRType {
    pub const fn decode(x: u16) -> Self {
        Self {
            r1: ((x >> 7) & 0b1_1111) as u8,
            rs2: ((x >> 2) & 0b1_1111) as u8,
            funct4: ((x >> 12) & 0b1111) as u8,
        }
    }
}

#[derive(Debug)]
pub struct CIType {
    pub r1: u8,
    pub funct3: u8,
    pub imm: u16,
}
impl CIType {
    pub const fn decode(x: u16) -> Self {
        Self {
            r1: ((x >> 7) & 0b1_1111) as u8,
            funct3: ((x >> 13) & 0b111) as u8,
            imm: x & 0b0001_0000_0111_1100,
        }
    }
}

#[derive(Debug)]
pub struct CSSType {
    pub rs2: u8,
    pub funct3: u8,
    pub imm: u16,
}
impl CSSType {
    pub const fn decode(x: u16) -> Self {
        Self {
            rs2: ((x >> 2) & 0b1_1111) as u8, 
            funct3: ((x >> 13) & 0b111) as u8,
            imm: x & 0b0001_1111_1000_0000,
        }
    }
}

#[derive(Debug)]
pub struct CIWType {
    pub rd: u8,
    pub funct3: u8,
    pub imm: u16,
}
impl CIWType {
    pub const fn decode(x: u16) -> Self {
        Self {
            rd: 0b1000 | ((x >> 2) & 0b111) as u8,
            funct3: ((x >> 13) & 0b111) as u8,
            imm: x & 0b0001_1111_1110_0000,
        }
    }
}

#[derive(Debug)]
pub struct CLType {
    pub rs1: u8,
    pub rd: u8,
    pub funct3: u8,
    pub imm: u16,
}
impl CLType {
    pub const fn decode(x: u16) -> Self {
        Self {
            rs1: 0b1000 | ((x >> 7) & 0b111) as u8,
            rd: 0b1000 | ((x >> 2) & 0b111) as u8,
            funct3: ((x >> 13) & 0b111) as u8,
            imm: x & 0b0001_1100_0110_0000,
        }
    }
}

#[derive(Debug)]
pub struct CSType {
    pub rs1: u8,
    pub rs2: u8,
    pub funct3: u8,
    pub imm: u16,
}
impl CSType {
    pub const fn decode(x: u16) -> Self {
        Self {
            rs1: 0b1000 | ((x >> 7) & 0b111) as u8,
            rs2: 0b1000 | ((x >> 2) & 0b111) as u8,
            funct3: ((x >> 13) & 0b111) as u8,
            imm: x & 0b0001_1100_0110_0000,
        }
    }
}

#[derive(Debug)]
pub struct CAType {
    pub r1: u8,
    pub rs2: u8,
    pub funct2: u8,
    pub funct6: u8,
}
impl CAType {
    pub const fn decode(x: u16) -> Self {
        Self {
            r1: 0b1000 | ((x >> 7) & 0b111) as u8,
            rs2: 0b1000 | ((x >> 2) & 0b111) as u8,
            funct2: ((x >> 5) & 0b11) as u8,
            funct6: ((x >> 10) & 0b11_1111) as u8,
        }
    }
}

#[derive(Debug)]
pub struct CBType {
    pub r1: u8,
    pub funct3: u8,
    pub offset: u16,
}
impl CBType {
    pub const fn decode(x: u16) -> Self {
        Self {
            r1: 0b1000 | ((x >> 7) & 0b111) as u8,
            funct3: ((x >> 13) & 0b111) as u8,
            offset: x & 0b0001_1100_0111_1100,
        }
    }
}

#[derive(Debug)]
pub struct CJType {
    pub funct3: u8,
    pub target: u16,
}
impl CJType {
    pub const fn decode(x: u16) -> Self {
        Self {
            funct3: ((x >> 13) & 0b111) as u8,
            target: x & 0b0001_1111_1111_1100,
        }
    }
}

