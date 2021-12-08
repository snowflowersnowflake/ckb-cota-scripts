use crate::error::Error;
use core::result::Result;

type Byte32Opt = Option<[u8; 32]>;

/// CoTA cell data structure
/// This structure contains the following information:
/// 1) version: u8
/// 2) smt_root: [u8; 32]
#[derive(Debug, Clone)]
pub struct Cota {
    pub version:           u8,
    pub smt_root: Byte32Opt,
}

impl Cota {
    pub fn from_data(data: &[u8]) -> Result<Self, Error> {
        if data.len() != 1 && data.len() != 33 {
            return Err(Error::RegistryDataInvalid);
        }

        let version: u8 = data[0];
        if version != 0 {
            return Err(Error::VersionInvalid);
        }

        let smt_root = if data.len() == 1 {
            None
        } else {
            let mut root = [0u8; 32];
            root.copy_from_slice(&data[1..33]);
            Some(root)
        };

        Ok(Cota {
            version,
            smt_root,
        })
    }
}
