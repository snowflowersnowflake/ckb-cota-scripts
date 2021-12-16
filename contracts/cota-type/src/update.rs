use alloc::vec::Vec;
use ckb_std::{
    ckb_constants::Source,
    ckb_types::{bytes::Bytes, prelude::*},
    dynamic_loading_c_impl::CKBDLContext,
    high_level::load_cell_data,
};
use core::result::Result;
use cota_smt::common::CotaNFTInfo;
use cota_smt::update::UpdateCotaNFTEntries;
use script_utils::{
    constants::{BYTE10_ZEROS, BYTE6_ZEROS, HOLD_NFT_SMT_TYPE},
    cota::Cota,
    error::Error,
    helper::u16_from_slice,
    nft::Nft,
    nft_validator::{validate_immutable_nft_fields, validate_nft_claim, validate_nft_lock},
    smt::LibCKBSmt,
};

fn validate_nft_info(
    hold_new_value: &CotaNFTInfo,
    hold_old_value: &CotaNFTInfo,
) -> Result<(), Error> {
    let output_nft = Nft::from_data(hold_new_value.as_slice())?;
    let input_nft = Nft::from_data(hold_old_value.as_slice())?;

    validate_immutable_nft_fields(&input_nft, &output_nft)?;
    validate_nft_claim(&input_nft, &output_nft)?;
    validate_nft_lock(&input_nft, &output_nft)?;

    Ok(())
}

pub fn verify_cota_update_smt(witness_args_input_type: Bytes) -> Result<(), Error> {
    let update_entries = UpdateCotaNFTEntries::from_slice(&witness_args_input_type[1..])
        .map_err(|_e| Error::WitnessTypeParseError)?;
    let hold_keys = update_entries.hold_keys();

    let mut cota_keys: Vec<u8> = Vec::new();
    let mut cota_values: Vec<u8> = Vec::new();
    let mut cota_old_values: Vec<u8> = Vec::new();

    for index in 0..hold_keys.len() {
        let hold_key = hold_keys.get(index).ok_or(Error::Encoding)?;
        if u16_from_slice(hold_key.smt_type().as_slice()) != HOLD_NFT_SMT_TYPE {
            return Err(Error::CoTANFTSmtTypeError);
        }
        cota_keys.extend(hold_key.as_slice());
        cota_keys.extend(&BYTE6_ZEROS);

        let hold_new_value = update_entries
            .hold_new_values()
            .get(index)
            .ok_or(Error::Encoding)?;
        let hold_old_value = update_entries
            .hold_old_values()
            .get(index)
            .ok_or(Error::Encoding)?;

        validate_nft_info(&hold_old_value, &hold_new_value)?;

        cota_values.extend(hold_new_value.as_slice());
        cota_values.extend(&BYTE10_ZEROS);
        cota_old_values.extend(hold_old_value.as_slice());
        cota_old_values.extend(&BYTE10_ZEROS);
    }

    let mut context = unsafe { CKBDLContext::<[u8; 128 * 1024]>::new() };
    let lib_ckb_smt = LibCKBSmt::load(&mut context);

    // Verify update smt proof of cota output
    let proof = update_entries.proof().raw_data().to_vec();
    let output_cota = Cota::from_data(&load_cell_data(0, Source::GroupOutput)?[..])?;
    if let Some(cota_smt_root) = output_cota.smt_root {
        lib_ckb_smt
            .smt_verify(&cota_smt_root, &cota_keys, &cota_values, &proof)
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }

    // Verify update smt proof of cota input
    let input_cota = Cota::from_data(&load_cell_data(0, Source::GroupInput)?[..])?;
    if let Some(cota_smt_root) = input_cota.smt_root {
        lib_ckb_smt
            .smt_verify(&cota_smt_root, &cota_keys, &cota_old_values, &proof)
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }
    Ok(())
}
