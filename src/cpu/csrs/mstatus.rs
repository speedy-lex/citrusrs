use crate::cpu::Priviledge;

#[derive(Default)]
pub struct MStatus {
    pub machine_disable_trap: bool,
    pub trap_sret: bool,
    pub timeout_wait: bool,
    pub machipe_previous_priviledge: Priviledge,
    pub supervisor_previous_priviledge: Priviledge,
    pub machine_previous_interrupt_enable: bool,
    pub supervisor_previous_interrupt_enable: bool,
    pub machine_interrupt_enable: bool,
    pub supervisor_interrupt_enable: bool,
}
impl MStatus {
    pub fn read(&self) -> u64 {
        self.encode()
    }
    pub fn write(&mut self, x: u64) {
        *self = Self::decode(x)
    }
    pub fn decode(x: u64) -> Self {
        Self {
            machine_disable_trap: (x >> 42) & 1 !=0,
            trap_sret: (x >> 22) & 1 !=0,
            timeout_wait: (x >> 21) & 1 !=0,
            machipe_previous_priviledge: Priviledge::from((x >> 11) & 0b11),
            supervisor_previous_priviledge: Priviledge::from((x >> 8) & 0b1),
            machine_previous_interrupt_enable: (x >> 7) & 1 !=0,
            supervisor_previous_interrupt_enable: (x >> 5) & 1 !=0,
            machine_interrupt_enable: (x >> 3) & 1 !=0,
            supervisor_interrupt_enable: (x >> 1) & 1 !=0,
        }
    }
    pub fn encode(&self) -> u64 {
        (0b1010 << 32) // sxl and uxl
            | (self.machine_disable_trap as u64) << 42
            | (self.trap_sret as u64) << 22
            | (self.timeout_wait as u64) << 21
            | (self.machipe_previous_priviledge as u64) << 11
            | (self.supervisor_previous_priviledge as u64 & 1) << 8
            | (self.machine_previous_interrupt_enable as u64) << 7
            | (self.supervisor_previous_interrupt_enable as u64) << 5
            | (self.machine_interrupt_enable as u64) << 3
            | (self.supervisor_interrupt_enable as u64) << 1
    }
}
