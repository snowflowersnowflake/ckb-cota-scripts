use crate::error::Error;
use core::result::Result;

/// CoTA NFT data structure
/// This structure contains the following information:
/// 1) configure: u8
/// 2) state: u8
/// 3) characteristic: [u8; 20]
#[derive(Debug, Clone)]
pub struct Nft {
    pub configure:      u8,
    pub state:          u8,
    pub characteristic: [u8; 20],
}

impl Nft {
    pub fn from_data(data: &[u8]) -> Result<Self, Error> {
        if data.len() != 22 {
            return Err(Error::LengthNotEnough);
        }

        let configure: u8 = data[0];
        let state: u8 = data[1];

        let mut characteristic = [0u8; 20];
        characteristic.copy_from_slice(&data[2..22]);

        Ok(Nft {
            state,
            configure,
            characteristic,
        })
    }

    pub fn allow_claim(&self) -> bool {
        self.configure & 0b0000_0001 == 0b0000_0000
    }

    pub fn allow_lock(&self) -> bool {
        self.configure & 0b0000_0010 == 0b0000_0000
    }

    pub fn allow_update_characteristic(&self) -> bool {
        self.configure & 0b0000_1000 == 0b0000_0000
    }

    pub fn allow_transfer_before_claim(&self) -> bool {
        self.configure & 0b0001_0000 == 0b0000_0000
    }

    pub fn allow_transfer_after_claim(&self) -> bool {
        self.configure & 0b0010_0000 == 0b0000_0000
    }

    pub fn allow_destroying_before_claim(&self) -> bool {
        self.configure & 0b0100_0000 == 0b0000_0000
    }

    pub fn allow_destroying_after_claim(&self) -> bool {
        self.configure & 0b1000_0000 == 0b0000_0000
    }

    pub fn is_claimed(&self) -> bool {
        self.state & 0b0000_0001 == 0b0000_0001
    }

    pub fn is_locked(&self) -> bool {
        self.state & 0b0000_0010 == 0b0000_0010
    }
}
