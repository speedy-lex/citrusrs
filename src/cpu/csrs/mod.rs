use crate::cpu::{csrs::mstatus::MStatus, Priviledge};

mod mstatus;

#[derive(Default)]
pub struct Csrs {
    mstatus: MStatus,
    pub mtvec: u64,

    // machine trap handling
    pub mscratch: u64,
    mepc: u64,
    mcause: u64,
    mtval: u64,
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
            0x305 => self.mtvec,
            0x340 => self.mscratch,
            0x341 => self.mepc,
            0x342 => self.mcause,
            0x343 => self.mtval,
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
            _ => {}
        }
    }
}
