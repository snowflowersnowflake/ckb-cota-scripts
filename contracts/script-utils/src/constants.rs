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
pub const BYTE22_ZEROS: [u8; 22] = [0u8; 22];
pub const BYTE4_ZEROS: [u8; 4] = [0u8; 4];
pub const BYTE3_ZEROS: [u8; 3] = [0u8; 3];

pub const SMT_ROOT_LEN: usize = 32;