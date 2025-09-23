use std::fs;

use citrusrs::Cpu;

fn main() {
    let file = fs::read("rom.elf").unwrap();
    let elf = goblin::elf::Elf::parse(&file).unwrap();
    let mut mem = vec![0; 1024 * 1024 * 32];
    for header in elf.program_headers {
        if header.p_memsz == 0 {
            continue;
        }
        let start = (header.vm_range().start - 0x80000000)..(header.vm_range().end - 0x80000000);
        mem[start].copy_from_slice(&file[header.file_range()]);
    }
    let mut cpu = Cpu::new(mem);
    cpu.pc = elf.entry;
    loop {
        cpu.step();
    }
}
