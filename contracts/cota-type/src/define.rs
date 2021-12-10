use alloc::vec::Vec;
use ckb_std::high_level::load_input;
use ckb_std::{
    ckb_constants::Source,
    ckb_types::{bytes::Bytes, prelude::*},
    dynamic_loading_c_impl::CKBDLContext,
    high_level::load_cell_data,
};
use core::result::Result;
use cota_smt::common::Uint32;
use cota_smt::define::DefineCotaNFTEntries;
use cota_smt::smt::Blake2bBuilder;
use script_utils::helper::u32_from_slice;
use script_utils::{
    constants::{BYTE10_ZEROS, BYTE23_ZEROS, BYTE32_ZEROS, DEFINE_NFT_SMT_TYPE},
    cota::Cota,
    error::Error,
    helper::u16_from_slice,
    smt::LibCKBSmt,
};

fn generate_cota_type_id(index: u8) -> Result<[u8; 20], Error> {
    let first_input = load_input(0, Source::Input)?;
    let mut blake2b = Blake2bBuilder::new(32)
        .personal(b"ckb-default-hash")
        .build();
    blake2b.update(first_input.as_slice());
    blake2b.update(&[index]);
    let mut ret = [0; 32];
    blake2b.finalize(&mut ret);

    let mut cota_type_id = [0u8; 20];
    cota_type_id.copy_from_slice(&ret[0..20]);

    Ok(cota_type_id)
}

fn check_define_action(action: Bytes, total: Uint32) -> Result<(), Error> {
    let mut action_vec: Vec<u8> = Vec::new();
    action_vec.extend("Create a new NFT collection with ".as_bytes());
    action_vec.extend(total.as_slice());
    action_vec.extend(" edition".as_bytes());
    let action_bytes: Bytes = action_vec.into();
    if action_bytes != action {
        return Err(Error::CoTANFTActionError);
    }
    Ok(())
}

pub fn verify_cota_define_smt(witness_args_input_type: Bytes) -> Result<(), Error> {
    let mut define_keys: Vec<u8> = Vec::new();
    let mut define_values: Vec<u8> = Vec::new();

    let define_entries = DefineCotaNFTEntries::from_slice(&witness_args_input_type[1..])
        .map_err(|_e| Error::WitnessTypeParseError)?;

    if define_entries.define_keys().len() > 1 {
        return Err(Error::LengthInvalid);
    }

    for index in 0..define_entries.define_keys().len() {
        let define_key = define_entries
            .define_keys()
            .get(index)
            .ok_or(Error::Encoding)?;
        if u16_from_slice(define_key.smt_type().as_slice()) != DEFINE_NFT_SMT_TYPE {
            return Err(Error::CoTANFTSmtTypeError);
        }
        let cota_type_id = generate_cota_type_id(index as u8)?;
        if &cota_type_id != define_key.cota_id().as_slice() {
            return Err(Error::CoTAIdInvalid);
        }

        let define_value = define_entries
            .define_values()
            .get(index)
            .ok_or(Error::Encoding)?;

        check_define_action(define_entries.action().as_bytes(), define_value.total())?;
        if u32_from_slice(define_value.as_slice()) != 0u32 {
            return Err(Error::CoTADefineIssuedError);
        }

        define_keys.extend(define_key.as_slice());
        define_keys.extend(&BYTE10_ZEROS);

        define_values.extend(define_value.as_slice());
        define_values.extend(&BYTE23_ZEROS);
    }

    let mut context = unsafe { CKBDLContext::<[u8; 128 * 1024]>::new() };
    let lib_ckb_smt = LibCKBSmt::load(&mut context);

    // Verify definition smt proof of cota nft output
    let proof = define_entries.proof().raw_data().to_vec();
    let output_cota = Cota::from_data(&load_cell_data(0, Source::Output)?[..])?;
    if let Some(define_smt_root) = output_cota.smt_root {
        lib_ckb_smt
            .smt_verify(
                &define_smt_root[..],
                &define_keys[..],
                &define_values[..],
                &proof[..],
            )
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }

    // Verify definition smt proof of cota nft input
    let input_cota = Cota::from_data(&load_cell_data(0, Source::Output)?[..])?;
    define_values.clear();
    for _ in 0..define_keys.len() {
        define_values.extend(&BYTE32_ZEROS);
    }
    if let Some(define_smt_root) = input_cota.smt_root {
        lib_ckb_smt
            .smt_verify(
                &define_smt_root[..],
                &define_keys[..],
                &define_values[..],
                &proof[..],
            )
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }
    Ok(())
}
