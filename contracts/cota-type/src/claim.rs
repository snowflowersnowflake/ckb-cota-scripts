use alloc::vec::Vec;
use ckb_std::high_level::{load_cell_data, load_cell_lock_hash};
use ckb_std::{
    ckb_constants::Source,
    ckb_types::{bytes::Bytes, packed::*, prelude::*},
    dynamic_loading_c_impl::CKBDLContext,
    high_level::load_cell,
};
use core::result::Result;
use cota_smt::common::{LockHashSlice, WithdrawalCotaNFTValueBuilder};
use cota_smt::smt::blake2b_256;
use cota_smt::transfer::ClaimCotaNFTEntries;
use script_utils::constants::{
    BYTE10_ZEROS, BYTE6_ZEROS, CLAIM_NFT_SMT_TYPE, HOLD_NFT_SMT_TYPE, WITHDRAWAL_NFT_SMT_TYPE,
};
use script_utils::cota::Cota;
use script_utils::helper::u16_from_slice;
use script_utils::{constants::BYTE32_ZEROS, error::Error, smt::LibCKBSmt};

fn check_claim_action(action: Bytes, claimed_count: u32) -> Result<(), Error> {
    let mut action_vec: Vec<u8> = Vec::new();
    action_vec.extend("Claim ".as_bytes());
    action_vec.extend(claimed_count.to_be_bytes());
    action_vec.extend(" NFTs".as_bytes());
    let action_bytes: Bytes = action_vec.into();
    if action_bytes != action {
        return Err(Error::CoTANFTActionError);
    }
    Ok(())
}

fn load_withdrawal_smt_root_from_cell_dep(cota_type: &Script) -> Result<[u8; 32], Error> {
    let withdrawal_cota_cell_dep = load_cell(0, Source::CellDep)?;
    if let Some(dep_cota_type) = withdrawal_cota_cell_dep.type_().to_opt() {
        if dep_cota_type.code_hash().as_slice() == cota_type.code_hash().as_slice()
            && dep_cota_type.hash_type() == cota_type.hash_type()
        {
            let cota_data = load_cell_data(0, Source::CellDep)?;
            let cota = Cota::from_data(&cota_data)?;
            return Ok(cota.smt_root.ok_or(Error::Encoding)?);
        }
        return Err(Error::CoTANFTWithdrawalDepError);
    }
    Err(Error::CoTANFTWithdrawalDepError)
}

pub fn verify_cota_claim_smt(
    cota_type: &Script,
    witness_args_input_type: Bytes,
) -> Result<(), Error> {
    let claim_entries = ClaimCotaNFTEntries::from_slice(&witness_args_input_type[1..])
        .map_err(|_e| Error::WitnessTypeParseError)?;
    let withdrawal_cota_smt_root = load_withdrawal_smt_root_from_cell_dep(&cota_type)?;

    let claimed_count = claim_entries.claim_keys().len() as u32;
    check_claim_action(claim_entries.action().raw_data(), claimed_count)?;

    let to_lock_hash_160 = &load_cell_lock_hash(0, Source::GroupOutput)?[0..20];

    let mut withdrawal_keys: Vec<u8> = Vec::new();
    let mut withdrawal_values: Vec<u8> = Vec::new();
    let mut claimed_keys: Vec<u8> = Vec::new();
    let mut claimed_values: Vec<u8> = Vec::new();

    for index in 0..claim_entries.hold_keys().len() {
        let hold_key = claim_entries
            .hold_keys()
            .get(index)
            .ok_or(Error::Encoding)?;
        if u16_from_slice(hold_key.smt_type().as_slice()) != HOLD_NFT_SMT_TYPE {
            return Err(Error::CoTANFTSmtTypeError);
        }
        let claimed_key = claim_entries
            .claim_keys()
            .get(index)
            .ok_or(Error::Encoding)?;
        if u16_from_slice(claimed_key.nft_id().smt_type().as_slice()) != CLAIM_NFT_SMT_TYPE {
            return Err(Error::CoTANFTSmtTypeError);
        }

        // collect hold and claimed keys for claimed smt proof
        claimed_keys.extend(hold_key.as_slice());
        claimed_keys.extend(&BYTE6_ZEROS);
        claimed_keys.extend(&blake2b_256(claimed_key.as_slice()));

        // collect hold and claimed values for claimed smt proof
        let hold_value = claim_entries
            .hold_values()
            .get(index)
            .ok_or(Error::Encoding)?;
        let claimed_value = claim_entries
            .claim_values()
            .get(index)
            .ok_or(Error::Encoding)?;
        claimed_values.extend(hold_value.as_slice());
        claimed_values.extend(&BYTE10_ZEROS);
        claimed_values.extend(claimed_value.as_slice());

        // collect withdrawal keys for withdrawal smt proof
        withdrawal_keys.extend(&WITHDRAWAL_NFT_SMT_TYPE.to_be_bytes());
        withdrawal_keys.extend(hold_key.cota_id().as_slice());
        withdrawal_keys.extend(hold_key.index().as_slice());
        withdrawal_keys.extend(&BYTE6_ZEROS);

        // collect withdrawal values for withdrawal smt proof
        let to = LockHashSlice::from_slice(to_lock_hash_160).map_err(|_e| Error::Encoding)?;
        let withdrawal_cota_value = WithdrawalCotaNFTValueBuilder::default()
            .nft_info(hold_value)
            .to(to)
            .out_point(claimed_key.out_point())
            .build();
        withdrawal_values.extend(&blake2b_256(withdrawal_cota_value.as_slice()));
    }

    let mut context = unsafe { CKBDLContext::<[u8; 128 * 1024]>::new() };
    let lib_ckb_smt = LibCKBSmt::load(&mut context);

    // Verify claimed smt proof of cota output
    let proof = claim_entries.proof().raw_data().to_vec();
    let output_cota = Cota::from_data(&load_cell_data(0, Source::GroupOutput)?[..])?;
    if let Some(cota_smt_root) = output_cota.smt_root {
        lib_ckb_smt
            .smt_verify(&cota_smt_root, &claimed_keys, &claimed_values, &proof)
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }

    // Verify withdrawal smt proof of cota cell_dep
    if !withdrawal_keys.is_empty() {
        let withdrawal_proof = claim_entries.withdrawal_proof().raw_data().to_vec();
        lib_ckb_smt
            .smt_verify(
                &withdrawal_cota_smt_root,
                &withdrawal_keys,
                &withdrawal_values,
                &withdrawal_proof,
            )
            .map_err(|_| Error::ClaimedCoTAWithdrawalSMTVerifyFailed)?;
    }

    // Verify claimed smt proof of cota input
    let input_cota = Cota::from_data(&load_cell_data(0, Source::GroupInput)?[..])?;
    if let Some(cota_smt_root) = input_cota.smt_root {
        claimed_values.clear();
        for _ in 0..(claim_entries.hold_values().len() * 2) {
            claimed_values.extend(&BYTE32_ZEROS);
        }
        lib_ckb_smt
            .smt_verify(&cota_smt_root, &claimed_keys, &claimed_values, &proof)
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }
    Ok(())
}
