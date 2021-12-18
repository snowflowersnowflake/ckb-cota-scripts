use ckb_std::error::SysError;

/// Error
#[repr(i8)]
pub enum Error {
    IndexOutOfBound = 1,
    ItemMissing,
    LengthInvalid,
    Encoding,
    TypeArgsInvalid = 5,
    VersionInvalid,
    GroupInputWitnessNoneError,
    WitnessTypeParseError,
    SMTProofVerifyFailed,
    RegistryCellSMTRootError = 10,
    RegistryCoTANFTExistError,
    RegistryDataInvalid,
    RegistryKeysNotEqualLockHashes,
    RegistryCellsCountError,
    RegistryCellLockNotSame = 15,
    CoTACellsCountError,
    CoTARegistryCellExistError,
    CoTATypeArgsNotEqualLockHash,
    CoTADataInvalid,
    CoTACellSMTRootError = 20,
    CoTADefineIssuedError,
    CoTAImmutableFieldsError,
    CoTANFTSmtTypeError,
    CoTANFTActionError,
    CoTACellLockNotSame = 25,
    CoTAIdInvalid,
    CoTANFTTokenIndexError,
    CoTAOutPointError,
    CoTALockedNFTCannotTransfer,
    CoTANFTCannotTransferBeforeClaim = 30,
    CoTANFTCannotTransferAfterClaim,
    CoTAWithdrawalNFTInfoError,
    CoTANFTWithdrawalDepError,
    ClaimedCoTAWithdrawalSMTVerifyFailed,
    CoTALockedNFTCannotUpdateInfo = 35,
    CoTALockedNFTCannotClaim,
    CoTANFTClaimError,
    CoTANFTLockError,
    CoTACellDataNotSame,
}

impl From<SysError> for Error {
    fn from(err: SysError) -> Self {
        use SysError::*;
        match err {
            IndexOutOfBound => Self::IndexOutOfBound,
            ItemMissing => Self::ItemMissing,
            LengthNotEnough(_) => Self::LengthInvalid,
            Encoding => Self::Encoding,
            Unknown(err_code) => panic!("unexpected sys error {}", err_code),
        }
    }
}
