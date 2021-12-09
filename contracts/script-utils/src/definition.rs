use crate::error::Error;
use crate::helper::u32_from_slice;
use core::result::Result;

/// Definition SMT value data structure
/// This structure contains the following information:
/// 1) total: u32
/// 2) issued: u32
/// 3) configure: u8
#[derive(Debug, Clone)]
pub struct Definition {
    pub total:     u32,
    pub issued:    u32,
    pub configure: u8,
}

impl Definition {
    pub fn from_data(data: &[u8]) -> Result<Self, Error> {
        if data.len() != 9 {
            return Err(Error::LengthNotEnough);
        }

        let total = u32_from_slice(&data[0..4]);
        let issued = u32_from_slice(&data[4..8]);

        if total > 0 && issued > total {
            return Err(Error::CoTADefineIssuedError);
        }

        let configure: u8 = data[9];

        Ok(Definition {
            total,
            issued,
            configure,
        })
    }

    pub fn check_immutable_fields(&self, other: &Definition) -> Result<(), Error> {
        if self.total != other.total || self.configure != other.configure {
            return Err(Error::CoTADefineImmutableFieldsError);
        }
        Ok(())
    }
}
