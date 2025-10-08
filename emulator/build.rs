use std::process::Command;

fn main() {
    assert!(Command::new("dtc").args(["-O", "dtb", "-o", "src/emulator.dtb", "src/emulator.dts"]).status().unwrap().success())
}
