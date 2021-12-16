use alloc::vec;
use alloc::vec::Vec;
use ckb_std::ckb_types::bytes::Bytes;
use ckb_std::high_level::load_input_out_point;
use ckb_std::{
    ckb_constants::Source, ckb_types::prelude::*, dynamic_loading_c_impl::CKBDLContext,
    high_level::load_cell_data,
};
use core::result::Result;
use cota_smt::common::DefineCotaNFTId;
use cota_smt::mint::MintCotaNFTEntries;
use cota_smt::smt::blake2b_256;
use script_utils::constants::{BYTE6_ZEROS, WITHDRAWAL_NFT_SMT_TYPE};
use script_utils::definition::Definition;
use script_utils::helper::u32_from_slice;
use script_utils::{
    constants::{BYTE10_ZEROS, BYTE23_ZEROS, BYTE32_ZEROS, DEFINE_NFT_SMT_TYPE},
    cota::Cota,
    error::Error,
    helper::u16_from_slice,
    smt::LibCKBSmt,
};

const FIXED_ACTION_LEN: usize = 36;
fn check_mint_action(mint_entries: &MintCotaNFTEntries) -> Result<(), Error> {
    if mint_entries.withdrawal_keys().len() != 1 || mint_entries.define_keys().len() != 1 {
        return Ok(());
    }
    let action = mint_entries.action().raw_data().to_vec();
    if action.len() <= FIXED_ACTION_LEN {
        return Err(Error::CoTANFTActionError);
    }
    let withdrawal_value = mint_entries
        .withdrawal_values()
        .get(0)
        .ok_or(Error::Encoding)?;
    let receiver_lock_bytes = &action[FIXED_ACTION_LEN..];
    let receiver_lock_hash = blake2b_256(receiver_lock_bytes);
    if &receiver_lock_hash[0..20] != withdrawal_value.to().as_slice() {
        return Err(Error::CoTANFTActionError);
    }

    let withdrawal_key = mint_entries
        .withdrawal_keys()
        .get(0)
        .ok_or(Error::Encoding)?;
    let cota_id = withdrawal_key.cota_id().as_slice().to_vec();

    let mut action_vec: Vec<u8> = Vec::new();
    action_vec.extend("Mint an NFT ".as_bytes());
    action_vec.extend(cota_id);
    action_vec.extend(" to ".as_bytes());
    action_vec.extend(receiver_lock_bytes);
    if action_vec != action {
        return Err(Error::CoTANFTActionError);
    }
    Ok(())
}

fn check_cota_definition_and_withdrawal(mint_entries: &MintCotaNFTEntries) -> Result<(), Error> {
    let define_key = mint_entries.define_keys().get(0).ok_or(Error::Encoding)?;
    if u16_from_slice(define_key.smt_type().as_slice()) != DEFINE_NFT_SMT_TYPE {
        return Err(Error::CoTANFTSmtTypeError);
    }

    let define_old_values = mint_entries.define_old_values();
    let define_new_values = mint_entries.define_new_values();
    let define_new_value = define_new_values.get(0).ok_or(Error::Encoding)?;
    let define_old_value = define_old_values.get(0).ok_or(Error::Encoding)?;
    let new_definition = Definition::from_data(define_new_value.as_slice())?;
    let old_definition = Definition::from_data(define_old_value.as_slice())?;

    old_definition.check_immutable_fields(&new_definition)?;
    if old_definition.issued >= new_definition.issued {
        return Err(Error::CoTADefineIssuedError);
    }

    let withdrawal_count = mint_entries.withdrawal_keys().len();
    if withdrawal_count as u32 != (new_definition.issued - old_definition.issued) {
        return Err(Error::CoTADefineIssuedError);
    }

    let cota_input_out_point = load_input_out_point(0, Source::GroupInput)?;
    let mut token_indexes: Vec<u32> = vec![];
    for index in 0..withdrawal_count {
        let withdrawal_key = mint_entries
            .withdrawal_keys()
            .get(index)
            .ok_or(Error::Encoding)?;
        if u16_from_slice(withdrawal_key.smt_type().as_slice()) != WITHDRAWAL_NFT_SMT_TYPE {
            return Err(Error::CoTANFTSmtTypeError);
        }
        let token_index = u32_from_slice(withdrawal_key.index().as_slice());
        token_indexes.push(token_index);

        let withdrawal_value = mint_entries
            .withdrawal_values()
            .get(index)
            .ok_or(Error::Encoding)?;
        if withdrawal_value.nft_info().configure() != define_old_value.configure() {
            return Err(Error::CoTAImmutableFieldsError);
        }
        if withdrawal_value.out_point().as_slice() != &cota_input_out_point.as_slice()[12..] {
            return Err(Error::CoTAOutPointError);
        }
    }
    let mut mint_token_indexes = Vec::new();
    for token_id in old_definition.issued..new_definition.issued {
        mint_token_indexes.push(token_id);
    }
    if token_indexes != mint_token_indexes {
        return Err(Error::CoTANFTTokenIndexError);
    }

    Ok(())
}

pub fn verify_cota_mint_smt(witness_args_input_type: Bytes) -> Result<(), Error> {
    let mint_entries = MintCotaNFTEntries::from_slice(&witness_args_input_type[1..])
        .map_err(|_e| Error::WitnessTypeParseError)?;

    if mint_entries.define_keys().len() != 1 {
        return Err(Error::LengthInvalid);
    }

    check_cota_definition_and_withdrawal(&mint_entries)?;
    check_mint_action(&mint_entries)?;

    let mut mint_keys: Vec<u8> = Vec::new();
    let mut mint_new_values: Vec<u8> = Vec::new();
    let mut mint_old_values: Vec<u8> = Vec::new();

    let define_key: DefineCotaNFTId = mint_entries.define_keys().get(0).ok_or(Error::Encoding)?;
    let define_old_values = mint_entries.define_old_values();
    let define_new_values = mint_entries.define_new_values();
    let define_new_value = define_new_values.get(0).ok_or(Error::Encoding)?;
    let define_old_value = define_old_values.get(0).ok_or(Error::Encoding)?;

    mint_keys.extend(define_key.as_slice());
    mint_keys.extend(&BYTE10_ZEROS);
    mint_old_values.extend(define_old_value.as_slice());
    mint_old_values.extend(&BYTE23_ZEROS);
    mint_new_values.extend(define_new_value.as_slice());
    mint_new_values.extend(&BYTE23_ZEROS);

    for index in 0..mint_entries.withdrawal_keys().len() {
        let withdrawal_key = mint_entries
            .withdrawal_keys()
            .get(index)
            .ok_or(Error::Encoding)?;
        let withdrawal_value = mint_entries
            .withdrawal_values()
            .get(index)
            .ok_or(Error::Encoding)?;
        mint_keys.extend(withdrawal_key.as_slice());
        mint_keys.extend(&BYTE6_ZEROS);
        mint_old_values.extend(BYTE32_ZEROS);
        mint_new_values.extend(blake2b_256(withdrawal_value.as_slice()));
    }

    let mut context = unsafe { CKBDLContext::<[u8; 128 * 1024]>::new() };
    let lib_ckb_smt = LibCKBSmt::load(&mut context);

    // Verify mint smt proof of cota output
    let proof = mint_entries.proof().raw_data().to_vec();
    let output_cota = Cota::from_data(&load_cell_data(0, Source::GroupOutput)?[..])?;
    if let Some(mint_smt_root) = output_cota.smt_root {
        lib_ckb_smt
            .smt_verify(&mint_smt_root, &mint_keys, &mint_new_values, &proof)
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }

    // Verify mint smt proof of cota input
    let input_cota = Cota::from_data(&load_cell_data(0, Source::GroupInput)?[..])?;
    if let Some(mint_smt_root) = input_cota.smt_root {
        lib_ckb_smt
            .smt_verify(&mint_smt_root, &mint_keys, &mint_old_values, &proof)
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }
    Ok(())
}
