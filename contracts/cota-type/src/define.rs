use alloc::vec::Vec;
use ckb_std::{
    ckb_constants::Source,
    ckb_types::{bytes::Bytes, prelude::*},
    dynamic_loading_c_impl::CKBDLContext,
    high_level::load_cell_data,
};
use core::result::Result;
use cota_smt::define::DefineCotaNFTEntries;
use script_utils::{
    constants::{
        BYTE10_ZEROS, BYTE23_ZEROS, BYTE32_ZEROS, BYTE6_ZEROS, DEFINE_NFT_SMT_TYPE,
        HOLD_NFT_SMT_TYPE,
    },
    cota::Cota,
    definition::Definition,
    error::Error,
    helper::u16_from_slice,
    smt::LibCKBSmt,
};

pub fn verify_cota_define_smt(witness_args_input_type: Bytes) -> Result<(), Error> {
    let mut cota_keys: Vec<u8> = Vec::new();
    let mut cota_new_values: Vec<u8> = Vec::new();
    let mut cota_old_values: Vec<u8> = Vec::new();

    let define_entries = DefineCotaNFTEntries::from_slice(&witness_args_input_type[1..])
        .map_err(|_e| Error::WitnessTypeParseError)?;
    let define_old_values = define_entries.define_old_values();
    let define_new_values = define_entries.define_new_values();
    if define_old_values.len() > 1 || define_new_values.len() != 1 {
        return Err(Error::Encoding);
    }
    let define_new_value = define_new_values.get(0).ok_or(Error::Encoding)?;
    let new_definition = Definition::from_data(define_new_value.as_slice())?;
    let mut increased_issued = new_definition.issued;
    if let Some(define_old_value) = define_old_values.get(0) {
        let old_definition = Definition::from_data(define_old_value.as_slice())?;
        old_definition.check_immutable_fields(&new_definition)?;
        if old_definition.issued >= new_definition.issued {
            return Err(Error::CoTADefineIssuedError);
        }
        increased_issued -= old_definition.issued;

        cota_old_values.extend(define_old_value.as_slice());
        cota_old_values.extend(&BYTE23_ZEROS);
    }

    if define_entries.hold_keys().len() as u32 != increased_issued {
        return Err(Error::CoTADefineIssuedError);
    }

    let define_key = define_entries.define_keys().get(0).ok_or(Error::Encoding)?;
    if u16_from_slice(define_key.smt_type().as_slice()) != DEFINE_NFT_SMT_TYPE {
        return Err(Error::CoTANFTSmtTypeError);
    }

    cota_keys.extend(define_entries.define_keys().as_slice());
    cota_keys.extend(&BYTE10_ZEROS);
    cota_new_values.extend(define_new_value.as_slice());
    cota_new_values.extend(&BYTE23_ZEROS);

    for index in 0..define_entries.hold_keys().len() {
        let hold_key = define_entries
            .hold_keys()
            .get(index)
            .ok_or(Error::Encoding)?;
        if u16_from_slice(hold_key.smt_type().as_slice()) != HOLD_NFT_SMT_TYPE {
            return Err(Error::CoTANFTSmtTypeError);
        }

        let hold_value = define_entries
            .hold_values()
            .get(index)
            .ok_or(Error::Encoding)?;
        if hold_value.configure() != define_new_value.configure() {
            return Err(Error::CoTADefineImmutableFieldsError);
        }

        cota_keys.extend(hold_key.as_slice());
        cota_keys.extend(&BYTE6_ZEROS);

        cota_old_values.extend(BYTE32_ZEROS);
        cota_new_values.extend(hold_value.as_slice());
        cota_new_values.extend(&BYTE10_ZEROS);
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
                &cota_keys[..],
                &cota_new_values[..],
                &proof[..],
            )
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }

    // Verify definition smt proof of cota nft input
    let input_cota = Cota::from_data(&load_cell_data(0, Source::Output)?[..])?;
    if let Some(define_smt_root) = input_cota.smt_root {
        lib_ckb_smt
            .smt_verify(
                &define_smt_root[..],
                &cota_keys[..],
                &cota_old_values[..],
                &proof[..],
            )
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }
    Ok(())
}
