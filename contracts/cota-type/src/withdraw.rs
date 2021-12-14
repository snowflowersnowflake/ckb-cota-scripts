use alloc::vec::Vec;
use ckb_std::high_level::load_cell_lock_hash;
use ckb_std::{
    ckb_constants::Source,
    ckb_types::{bytes::Bytes, prelude::*},
    dynamic_loading_c_impl::CKBDLContext,
    high_level::{load_cell_data, load_input_out_point},
};
use core::result::Result;
use cota_smt::common::{CotaNFTInfo, LockHashSlice};
use cota_smt::smt::blake2b_256;
use cota_smt::transfer::WithdrawalCotaNFTEntries;
use script_utils::constants::{
    BYTE10_ZEROS, BYTE6_ZEROS, HOLD_NFT_SMT_TYPE, WITHDRAWAL_NFT_SMT_TYPE,
};
use script_utils::cota::Cota;
use script_utils::helper::u16_from_slice;
use script_utils::nft::Nft;
use script_utils::{constants::BYTE32_ZEROS, error::Error, smt::LibCKBSmt};

fn check_nft_transferable(hold_value: &CotaNFTInfo, to: LockHashSlice) -> Result<(), Error> {
    let nft = Nft::from_data(hold_value.as_slice())?;
    let input_compact_nft_lock = load_cell_lock_hash(0, Source::GroupInput)?;
    if &input_compact_nft_lock[0..20] != to.as_slice() {
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

const FIXED_ACTION_LEN: usize = 40;
fn check_withdraw_action(withdraw_entries: &WithdrawalCotaNFTEntries) -> Result<(), Error> {
    if withdraw_entries.hold_keys().len() != 1 {
        return Ok(());
    }
    let action = withdraw_entries.action().raw_data().to_vec();
    if action.len() <= FIXED_ACTION_LEN {
        return Err(Error::CoTANFTActionError);
    }
    let receiver_lock_bytes = &action[FIXED_ACTION_LEN..];
    let receiver_lock_hash = blake2b_256(receiver_lock_bytes);
    let withdrawal_value = withdraw_entries
        .withdrawal_values()
        .get(0)
        .ok_or(Error::Encoding)?;
    if &receiver_lock_hash[0..20] != withdrawal_value.to().as_slice() {
        return Err(Error::CoTANFTActionError);
    }

    let withdrawal_key = withdraw_entries
        .withdrawal_keys()
        .get(0)
        .ok_or(Error::Encoding)?;
    let cota_id = withdrawal_key.cota_id().as_slice().to_vec();
    let mut action_vec: Vec<u8> = Vec::new();
    action_vec.extend("Transfer an NFT ".as_bytes());
    action_vec.extend(cota_id);
    action_vec.extend(" to ".as_bytes());
    action_vec.extend(receiver_lock_bytes);
    if action_vec != action {
        return Err(Error::CoTANFTActionError);
    }
    Ok(())
}

pub fn verify_cota_withdraw_smt(witness_args_input_type: Bytes) -> Result<(), Error> {
    let cota_input_out_point = load_input_out_point(0, Source::GroupInput)?;

    let withdraw_entries = WithdrawalCotaNFTEntries::from_slice(&witness_args_input_type[1..])
        .map_err(|_e| Error::WitnessTypeParseError)?;

    check_withdraw_action(&withdraw_entries)?;

    let mut cota_keys: Vec<u8> = Vec::new();
    let mut cota_values: Vec<u8> = Vec::new();
    let mut cota_old_values: Vec<u8> = Vec::new();

    let hold_keys = withdraw_entries.hold_keys();
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
        cota_keys.extend(hold_key.as_slice());
        cota_keys.extend(&BYTE6_ZEROS);
        cota_keys.extend(withdrawal_key.as_slice());
        cota_keys.extend(&BYTE6_ZEROS);

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
        check_nft_transferable(&hold_value, withdrawal_value.to())?;
        if hold_value.as_slice() != withdrawal_value.nft_info().as_slice() {
            return Err(Error::CoTAWithdrawalNFTInfoError);
        }
        cota_values.extend(&BYTE32_ZEROS);
        cota_values.extend(&blake2b_256(withdrawal_value.as_slice()));
        cota_old_values.extend(hold_value.as_slice());
        cota_old_values.extend(&BYTE10_ZEROS);
        cota_old_values.extend(&BYTE32_ZEROS);
    }

    let mut context = unsafe { CKBDLContext::<[u8; 128 * 1024]>::new() };
    let lib_ckb_smt = LibCKBSmt::load(&mut context);

    // Verify withdrawal smt proof of cota output
    let proof = withdraw_entries.proof().raw_data().to_vec();
    let output_cota = Cota::from_data(&load_cell_data(0, Source::GroupOutput)?[..])?;
    if let Some(cota_smt_root) = output_cota.smt_root {
        lib_ckb_smt
            .smt_verify(
                &cota_smt_root[..],
                &cota_keys[..],
                &cota_values[..],
                &proof[..],
            )
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }

    // Verify withdrawal smt proof of cota input
    let input_cota = Cota::from_data(&load_cell_data(0, Source::GroupInput)?[..])?;
    if let Some(cota_smt_root) = input_cota.smt_root {
        lib_ckb_smt
            .smt_verify(
                &cota_smt_root[..],
                &cota_keys[..],
                &cota_old_values[..],
                &proof[..],
            )
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }
    Ok(())
}
