use std::fs;

use crate::cpu::Cpu;

mod cpu;

fn main() {
    let mut cpu = Cpu::new(fs::read("rom.bin").unwrap());
    loop {
        cpu.step();
    }
}
