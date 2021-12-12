#![allow(dead_code)]

pub const TYPE: u8 = 1;

pub const REGISTRY_TYPE_CODE_HASH: [u8; 32] = [
    58, 104, 151, 171, 120, 173, 16, 208, 40, 208, 197, 239, 55, 85, 69, 230, 107, 253, 255, 208,
    31, 58, 54, 155, 91, 7, 144, 96, 120, 224, 79, 109,
];

pub const COTA_TYPE_CODE_HASH: [u8; 32] = [
    220, 167, 40, 178, 34, 13, 64, 38, 174, 66, 149, 145, 92, 163, 223, 181, 134, 189, 247, 93,
    171, 123, 241, 75, 32, 55, 56, 153, 88, 141, 134, 137,
];

pub const BYTE32_ZEROS: [u8; 32] = [0u8; 32];
pub const BYTE23_ZEROS: [u8; 23] = [0u8; 23];
pub const BYTE10_ZEROS: [u8; 10] = [0u8; 10];
pub const BYTE6_ZEROS: [u8; 6] = [0u8; 6];

pub const SMT_ROOT_LEN: usize = 32;

pub const DEFINE_NFT_SMT_TYPE: u16 = 33024u16; // 0x8100
pub const HOLD_NFT_SMT_TYPE: u16 = 33025u16; // 0x8101
pub const WITHDRAWAL_NFT_SMT_TYPE: u16 = 33026u16; // 0x8102
pub const CLAIM_NFT_SMT_TYPE: u16 = 33027u16; // 0x8103
