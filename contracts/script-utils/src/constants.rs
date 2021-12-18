pub const TYPE: u8 = 1;

pub const REGISTRY_TYPE_CODE_HASH: [u8; 32] = [
    243, 203, 255, 253, 75, 30, 160, 88, 156, 37, 90, 139, 32, 165, 158, 68, 15, 247, 40, 52, 161,
    143, 89, 63, 58, 129, 161, 86, 85, 241, 118, 253,
];

pub const COTA_TYPE_CODE_HASH: [u8; 32] = [
    29, 239, 55, 101, 172, 177, 221, 107, 228, 171, 42, 104, 75, 93, 44, 91, 41, 164, 181, 192,
    141, 174, 114, 229, 146, 76, 65, 206, 246, 187, 36, 186,
];

pub const BYTE32_ZEROS: [u8; 32] = [0u8; 32];
pub const BYTE23_ZEROS: [u8; 23] = [0u8; 23];
pub const BYTE10_ZEROS: [u8; 10] = [0u8; 10];
pub const BYTE6_ZEROS: [u8; 6] = [0u8; 6];

pub const DEFINE_NFT_SMT_TYPE: u16 = 33024u16; // 0x8100
pub const HOLD_NFT_SMT_TYPE: u16 = 33025u16; // 0x8101
pub const WITHDRAWAL_NFT_SMT_TYPE: u16 = 33026u16; // 0x8102
pub const CLAIM_NFT_SMT_TYPE: u16 = 33027u16; // 0x8103
