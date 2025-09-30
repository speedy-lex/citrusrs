use crate::cpu::{Priviledge, csrs::mstatus::MStatus};

mod mstatus;

pub struct Csrs {
    mstatus: MStatus,
    pub mtvec: u64,

    // machine trap handling
    pub mscratch: u64,
    mepc: u64,
    mcause: u64,
    mtval: u64,

    // paged memory protection stuff (stubbed for now)
    pmpcfg: [u64; 16],
    pmpaddr: [u64; 64],
}
impl Default for Csrs {
    fn default() -> Self {
        Self {
            mstatus: Default::default(),
            mtvec: Default::default(),
            mscratch: Default::default(),
            mepc: Default::default(),
            mcause: Default::default(),
            mtval: Default::default(),
            pmpcfg: Default::default(),
            pmpaddr: [0; 64], // i hate this
        }
    }
}
impl Csrs {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn write_exception(&mut self, mpp: Priviledge, mepc: u64, mcause: u64, mtval: u64) {
        self.mstatus.machipe_previous_priviledge = mpp;
        self.mstatus.machine_previous_interrupt_enable = self.mstatus.machine_interrupt_enable;
        self.mstatus.machine_interrupt_enable = false;

        self.mepc = mepc;
        self.mcause = mcause;
        self.mtval = mtval;
    }
    pub fn read(&mut self, addr: u64) -> u64 {
        match addr {
            0x300 => self.mstatus.read(),
            0x301 => 0x80_00_00_00_00_00_01_00,
            0x305 => self.mtvec,
            0x340 => self.mscratch,
            0x341 => self.mepc,
            0x342 => self.mcause,
            0x343 => self.mtval,
            0x3a0..0x3b0 => self.pmpcfg[(addr - 0x3a0) as usize],
            0x3b0..0x3f0 => self.pmpaddr[(addr - 0x3b0) as usize],
            _ => 0,
        }
    }
    pub fn write(&mut self, addr: u64, val: u64) {
        match addr {
            0x300 => self.mstatus.write(val),
            0x305 => {
                self.mtvec = val;
            }
            0x340 => {
                self.mscratch = val;
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
            0x3a0..0x3b0 => {
                self.pmpcfg[(addr - 0x3a0) as usize] = val;
            }
            0x3b0..0x3f0 => {
                self.pmpaddr[(addr - 0x3b0) as usize] = val;
            }
            _ => {}
        }
    }
}
