use alloc::vec::Vec;
use ckb_std::high_level::load_cell_lock_hash;
use ckb_std::{
    ckb_constants::Source,
    ckb_types::{bytes::Bytes, prelude::*},
    dynamic_loading_c_impl::CKBDLContext,
    high_level::{load_cell_data, load_input_out_point},
};
use core::result::Result;
use cota_smt::common::CotaNFTInfo;
use cota_smt::smt::blake2b_256;
use cota_smt::transfer::WithdrawalCotaNFTEntries;
use script_utils::constants::{
    BYTE10_ZEROS, BYTE6_ZEROS, HOLD_NFT_SMT_TYPE, WITHDRAWAL_NFT_SMT_TYPE,
};
use script_utils::cota::Cota;
use script_utils::helper::u16_from_slice;
use script_utils::nft::Nft;
use script_utils::{constants::BYTE32_ZEROS, error::Error, smt::LibCKBSmt};

fn check_nft_transferable(hold_value: &CotaNFTInfo, to_lock: &[u8]) -> Result<(), Error> {
    let nft = Nft::from_data(hold_value.as_slice())?;
    let input_compact_nft_lock = load_cell_lock_hash(0, Source::GroupInput)?;
    if &input_compact_nft_lock != to_lock {
        if nft.is_locked() {
            return Err(Error::CoTALockedNFTCannotTransfer);
        }
        if !nft.is_claimed() && !nft.allow_transfer_before_claim() {
            return Err(Error::CoTANFTCannotTransferBeforeClaim);
        }
        if nft.is_claimed() && !nft.allow_transfer_after_claim() {
            return Err(Error::CoTANFTCannotTransferAfterClaim);
        }
    }
    Ok(())
}

fn check_withdraw_action(withdraw_entries: &WithdrawalCotaNFTEntries) -> Result<(), Error> {
    if withdraw_entries.hold_keys().len() != 1 {
        return Ok(());
    }
    let action = withdraw_entries.action().raw_data().to_vec();
    let withdrawal_key = withdraw_entries
        .withdrawal_keys()
        .get(0)
        .ok_or(Error::Encoding)?;
    let withdrawal_value = withdraw_entries
        .withdrawal_values()
        .get(0)
        .ok_or(Error::Encoding)?;

    let mut action_vec: Vec<u8> = Vec::new();
    action_vec.extend("Transfer an NFT ".as_bytes());
    action_vec.extend(withdrawal_key.cota_id().as_slice());
    action_vec.extend(" to ".as_bytes());
    action_vec.extend(withdrawal_value.to_lock().raw_data().to_vec());
    if action_vec != action {
        return Err(Error::CoTANFTActionError);
    }
    Ok(())
}

pub fn verify_cota_withdraw_smt(witness_args_input_type: Bytes) -> Result<(), Error> {
    let withdraw_entries = WithdrawalCotaNFTEntries::from_slice(&witness_args_input_type[1..])
        .map_err(|_e| Error::WitnessTypeParseError)?;

    let hold_keys = withdraw_entries.hold_keys();
    if hold_keys.is_empty() {
        return Err(Error::LengthInvalid);
    }

    check_withdraw_action(&withdraw_entries)?;

    let mut withdraw_keys: Vec<u8> = Vec::new();
    let mut withdraw_new_values: Vec<u8> = Vec::new();
    let mut withdraw_old_values: Vec<u8> = Vec::new();
    let cota_input_out_point = load_input_out_point(0, Source::GroupInput)?;

    for index in 0..hold_keys.len() {
        let hold_key = hold_keys.get(index).ok_or(Error::Encoding)?;
        if u16_from_slice(hold_key.smt_type().as_slice()) != HOLD_NFT_SMT_TYPE {
            return Err(Error::CoTANFTSmtTypeError);
        }
        let withdrawal_key = withdraw_entries
            .withdrawal_keys()
            .get(index)
            .ok_or(Error::Encoding)?;
        if u16_from_slice(withdrawal_key.smt_type().as_slice()) != WITHDRAWAL_NFT_SMT_TYPE {
            return Err(Error::CoTANFTSmtTypeError);
        }
        withdraw_keys.extend(hold_key.as_slice());
        withdraw_keys.extend(&BYTE6_ZEROS);
        withdraw_keys.extend(withdrawal_key.as_slice());
        withdraw_keys.extend(&BYTE6_ZEROS);

        let withdrawal_value = withdraw_entries
            .withdrawal_values()
            .get(index)
            .ok_or(Error::Encoding)?;
        if &cota_input_out_point.as_slice()[12..] != withdrawal_value.out_point().as_slice() {
            return Err(Error::CoTAOutPointError);
        }
        let hold_value = withdraw_entries
            .hold_values()
            .get(index)
            .ok_or(Error::Encoding)?;
        check_nft_transferable(&hold_value, withdrawal_value.to_lock().as_slice())?;
        if hold_value.as_slice() != withdrawal_value.nft_info().as_slice() {
            return Err(Error::CoTAWithdrawalNFTInfoError);
        }
        withdraw_new_values.extend(&BYTE32_ZEROS);
        withdraw_new_values.extend(&blake2b_256(withdrawal_value.as_slice()));
        withdraw_old_values.extend(hold_value.as_slice());
        withdraw_old_values.extend(&BYTE10_ZEROS);
        withdraw_old_values.extend(&BYTE32_ZEROS);
    }

    let mut context = unsafe { CKBDLContext::<[u8; 128 * 1024]>::new() };
    let lib_ckb_smt = LibCKBSmt::load(&mut context);

    // Verify withdrawal smt proof of cota output
    let proof = withdraw_entries.proof().raw_data().to_vec();
    let output_cota = Cota::from_data(&load_cell_data(0, Source::GroupOutput)?[..])?;
    if let Some(cota_smt_root) = output_cota.smt_root {
        lib_ckb_smt
            .smt_verify(&cota_smt_root, &withdraw_keys, &withdraw_new_values, &proof)
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }

    // Verify withdrawal smt proof of cota input
    let input_cota = Cota::from_data(&load_cell_data(0, Source::GroupInput)?[..])?;
    if let Some(cota_smt_root) = input_cota.smt_root {
        lib_ckb_smt
            .smt_verify(&cota_smt_root, &withdraw_keys, &withdraw_old_values, &proof)
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }
    Ok(())
}
