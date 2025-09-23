pub const fn sext(x: u32, bits: u8) -> u32 {
    let shift = 32 - bits as i8;
    (((x << shift) as i32) >> shift) as u32
}

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
