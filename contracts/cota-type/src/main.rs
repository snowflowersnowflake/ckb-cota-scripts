#![no_std]
#![no_main]
#![feature(asm)]
#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(panic_info_message)]

mod define;
mod entry;
mod mint;
mod withdraw;

use ckb_std::default_alloc;

ckb_std::entry!(program_entry);
default_alloc!();

fn program_entry(_argc: u64, _argv: *const *const u8) -> i8 {
    match entry::main() {
        Ok(_) => 0,
        Err(err) => err as i8,
    }
}
