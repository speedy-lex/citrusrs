use std::fs;

use citrusrs::Cpu;

#[test]
fn run_user_roms() {
    let mut errors = vec![];
    for rom in fs::read_dir("tests/user/roms").unwrap() {
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
                if rom.file_name().to_string_lossy().contains("rvc") {
                    println!("{:x}", cpu.pc);
                }
            }
            if cycles == 1000000 {
                errors.push(format!(
                    "{}, too many cycles, pc: 0x{:x}",
                    rom.file_name().to_string_lossy(),
                    cpu.pc
                ));
                continue;
            }
            let errcode = cpu.registers[10];
            if errcode != 0 {
                errors.push(format!(
                    "{}, test failed: {} ({errcode})",
                    rom.file_name().to_string_lossy(),
                    (errcode & !1) >> 1
                ));
            }
        }
    }
    if !errors.is_empty() {
        for e in errors {
            eprintln!("{e}");
        }
        panic!("one or more tests failed")
    }
}
