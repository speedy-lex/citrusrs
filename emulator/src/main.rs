use citrusrs::Cpu;

fn main() {
    let rom = include_bytes!("fw/fw_payload.bin");
    let mut mem = vec![0; 1024 * 1024 * 64];
    mem[..rom.len()].copy_from_slice(rom);
    let device_tree = include_bytes!("emulator.dtb");
    mem[32 * 1024 * 1024..32 * 1024 * 1024 + device_tree.len()].copy_from_slice(device_tree);
    let mut cpu = Cpu::new(mem);
    cpu.pc = 0x8000_0000;
    cpu.registers[11] = 0x8000_0000 + 32 * 1024 * 1024; // dt addr
    loop {
        cpu.step();
        if cpu.pc == 0 {
            panic!();
        }
        println!("{:x}", cpu.pc);
    }
}
