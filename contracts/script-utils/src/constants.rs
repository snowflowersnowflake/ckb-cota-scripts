pub const TYPE: u8 = 1;

pub const REGISTRY_TYPE_CODE_HASH: [u8; 32] = [
    56, 64, 214, 183, 26, 41, 31, 149, 67, 10, 36, 39, 66, 6, 170, 91, 99, 99, 25, 241, 124, 149,
    94, 120, 0, 17, 201, 125, 152, 96, 112, 227,
];

pub const COTA_TYPE_CODE_HASH: [u8; 32] = [
    6, 75, 9, 155, 134, 58, 108, 199, 233, 230, 71, 121, 117, 251, 144, 219, 209, 202, 105, 140,
    200, 178, 218, 174, 94, 243, 54, 87, 105, 32, 77, 151,
];

pub const BYTE32_ZEROS: [u8; 32] = [0u8; 32];
pub const BYTE23_ZEROS: [u8; 23] = [0u8; 23];
pub const BYTE10_ZEROS: [u8; 10] = [0u8; 10];
pub const BYTE6_ZEROS: [u8; 6] = [0u8; 6];

pub const DEFINE_NFT_SMT_TYPE: u16 = 33024u16; // 0x8100
pub const HOLD_NFT_SMT_TYPE: u16 = 33025u16; // 0x8101
pub const WITHDRAWAL_NFT_SMT_TYPE: u16 = 33026u16; // 0x8102
pub const CLAIM_NFT_SMT_TYPE: u16 = 33027u16; // 0x8103
