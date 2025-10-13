use std::mem;

use crate::cpu::{Priviledge, csrs::mstatus::MStatus};

mod mstatus;

pub struct Csrs {
    mstatus: MStatus,
    medeleg: u64,
    pub mtvec: u64,

    // machine trap handling
    pub mscratch: u64,
    mepc: u64,
    mcause: u64,
    mtval: u64,

    // paged memory protection stuff (stubbed for now)
    pmpcfg: [u64; 16],
    pmpaddr: [u64; 64],

    stvec: u64,

    // TODO: sstatus
    // supervisor trap handling
    sscratch: u64,
    sepc: u64,
    scause: u64,
    stval: u64,
}
impl Default for Csrs {
    fn default() -> Self {
        Self {
            mstatus: Default::default(),
            medeleg: Default::default(),
            mtvec: Default::default(),
            mscratch: Default::default(),
            mepc: Default::default(),
            mcause: Default::default(),
            mtval: Default::default(),
            pmpcfg: Default::default(),
            pmpaddr: [0; 64], // i hate this
            stvec: Default::default(),
            sscratch: Default::default(),
            sepc: Default::default(),
            scause: Default::default(),
            stval: Default::default(),
        }
    }
}
impl Csrs {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn write_exception(
        &mut self,
        pp: Priviledge,
        epc: u64,
        cause: u64,
        tval: u64,
    ) -> (Priviledge, u64) {
        let is_machine = pp >= Priviledge::Machine || ((self.medeleg >> cause) & 1 == 0);
        if is_machine {
            self.mstatus.machipe_previous_priviledge = pp;
            self.mstatus.machine_previous_interrupt_enable = self.mstatus.machine_interrupt_enable;
            self.mstatus.machine_interrupt_enable = false;

            self.mepc = epc;
            self.mcause = cause;
            self.mtval = tval;

            (Priviledge::Machine, self.mtvec)
        } else {
            self.sepc = epc;
            self.scause = cause;
            self.stval = tval;

            (Priviledge::Supervisor, self.stvec)
        }
    }
    /// Returns the new priviledge level
    pub fn mret(&mut self) -> Priviledge {
        self.mstatus.machine_interrupt_enable =
            mem::replace(&mut self.mstatus.machine_previous_interrupt_enable, true);
        mem::replace(
            &mut self.mstatus.machipe_previous_priviledge,
            Priviledge::Supervisor,
        )
    }
    pub fn read(&mut self, addr: u64) -> u64 {
        match addr {
            // machine
            0x300 => self.mstatus.read(),
            0x301 => 0x80_00_00_00_00_00_01_00,
            0x305 => self.mtvec,
            0x340 => self.mscratch,
            0x341 => self.mepc,
            0x342 => self.mcause,
            0x343 => self.mtval,
            0x3a0..0x3b0 => self.pmpcfg[(addr - 0x3a0) as usize],
            0x3b0..0x3f0 => self.pmpaddr[(addr - 0x3b0) as usize],

            // supervisor
            0x105 => self.stvec,
            0x140 => self.sscratch,
            0x141 => self.sepc,
            0x142 => self.scause,
            0x143 => self.stval,

            _ => 0,
        }
    }
    pub fn write(&mut self, addr: u64, val: u64) {
        match addr {
            // machine
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

            // supervisor
            0x105 => {
                self.stvec = val;
            }
            0x140 => {
                self.sscratch = val;
            }
            0x141 => {
                self.sepc = val;
            }
            0x142 => {
                self.scause = val;
            }
            0x143 => {
                self.stval = val;
            }

            _ => {}
        }
    }
}
