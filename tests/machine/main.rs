use std::fs;

use citrusrs::Cpu;

#[test]
fn run_machine_roms() {
    for rom in fs::read_dir("tests/machine/roms").unwrap() {
        let rom = rom.unwrap();
        if rom.file_type().unwrap().is_file() {
            let file = fs::read(rom.path()).unwrap();
            let elf = goblin::elf::Elf::parse(&file).unwrap();
            let mut mem = vec![0; 1024 * 1024 * 32];
            for header in elf.program_headers {
                if header.p_memsz == 0 {
                    continue;
                }
                let start =
                    (header.vm_range().start - 0x80000000)..(header.vm_range().end - 0x80000000);
                mem[start].copy_from_slice(&file[header.file_range()]);
            }
            let mut cpu = Cpu::new(mem);
            cpu.pc = elf.entry;
            // check x10 for error
            let mut cycles = 0;
            while cpu.step().is_none() && cycles < 1000000 {
                cycles += 1;
            }
            assert_ne!(cycles, 1000000, "pc: 0x{:x}, test failed: {}", cpu.pc, rom.file_name().to_string_lossy());
            let errcode = cpu.registers[10];
            assert_eq!(errcode, 0, "{}, mscratch: 0x{:x}, test failed: {}", rom.file_name().to_string_lossy(), cpu.csrs.mscratch, (errcode & !1) >> 1)
        }
    }
}
