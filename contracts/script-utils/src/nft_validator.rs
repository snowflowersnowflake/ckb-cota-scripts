use crate::error::Error;
use crate::nft::Nft;
use core::result::Result;

pub fn validate_immutable_nft_fields(input_nft: &Nft, output_nft: &Nft) -> Result<(), Error> {
    if input_nft.characteristic != output_nft.characteristic {
        if !input_nft.allow_update_characteristic() {
            return Err(Error::CoTAImmutableFieldsError);
        }
        if input_nft.is_locked() {
            return Err(Error::CoTALockedNFTCannotUpdateInfo);
        }
    }
    if input_nft.configure != output_nft.configure {
        return Err(Error::CoTAImmutableFieldsError);
    }
    Ok(())
}

pub fn validate_nft_claim(input_nft: &Nft, output_nft: &Nft) -> Result<(), Error> {
    match (input_nft.is_claimed(), output_nft.is_claimed()) {
        (false, true) => {
            if input_nft.is_locked() {
                return Err(Error::CoTALockedNFTCannotClaim);
            }
            if !input_nft.allow_claim() {
                return Err(Error::CoTANFTClaimError);
            }
            Ok(())
        }
        (true, false) => Err(Error::CoTANFTClaimError),
        _ => Ok(()),
    }
}

pub fn validate_nft_lock(input_nft: &Nft, output_nft: &Nft) -> Result<(), Error> {
    match (input_nft.is_locked(), output_nft.is_locked()) {
        (false, true) => {
            if !input_nft.allow_lock() {
                return Err(Error::CoTANFTLockError);
            }
            Ok(())
        }
        (true, false) => Err(Error::CoTANFTLockError),
        _ => Ok(()),
    }
}
