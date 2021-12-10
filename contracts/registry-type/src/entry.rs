use alloc::vec::Vec;
use blake2b_rs::Blake2bBuilder;
use ckb_std::high_level::{load_cell_lock_hash, load_input};
use ckb_std::{
    ckb_constants::Source,
    ckb_types::{bytes::Bytes, packed::*, prelude::*},
    dynamic_loading_c_impl::CKBDLContext,
    high_level::{load_cell_data, load_script, load_witness_args},
};
use core::result::Result;
use cota_smt::registry::CotaNFTRegistryEntries;
use script_utils::helper::{
    check_cota_cell_exist, count_cells_by_type, load_output_cota_lock_hashes,
    load_output_index_by_type, Action,
};
use script_utils::registry::Registry;
use script_utils::{constants::BYTE32_ZEROS, error::Error, smt::LibCKBSmt};

const TYPE_ARGS_LEN: usize = 20;

fn check_registry<'a>(registry_type: &'a Script) -> impl Fn(&Script) -> bool + 'a {
    move |type_: &Script| registry_type.as_slice() == type_.as_slice()
}

fn parse_registry_action(registry_type: &Script) -> Result<Action, Error> {
    let inputs_count = count_cells_by_type(Source::Input, &check_registry(registry_type));
    let outputs_count = count_cells_by_type(Source::Output, &check_registry(registry_type));
    match (inputs_count, outputs_count) {
        (0, 1) => Ok(Action::Create),
        (1, 1) => Ok(Action::Update),
        _ => Err(Error::RegistryCellsCountError),
    }
}

fn handle_creation(registry_type: &Script) -> Result<(), Error> {
    let first_input = load_input(0, Source::Input)?;
    let first_output_index = load_output_index_by_type(registry_type).ok_or(Error::Encoding)?;
    let mut blake2b = Blake2bBuilder::new(32)
        .personal(b"ckb-default-hash")
        .build();
    blake2b.update(first_input.as_slice());
    blake2b.update(&(first_output_index as u64).to_le_bytes());
    let mut ret = [0; 32];
    blake2b.finalize(&mut ret);

    let registry_args: Bytes = registry_type.args().unpack();
    if registry_args[..] != ret[0..TYPE_ARGS_LEN] {
        return Err(Error::TypeArgsInvalid);
    }
    let output_registry = Registry::from_data(&load_cell_data(0, Source::Output)?[..])?;
    // Registry cell data only has version filed
    if output_registry.smt_root.is_some() {
        return Err(Error::RegistryDataInvalid);
    }
    Ok(())
}

fn handle_update() -> Result<(), Error> {
    let input_lock_hash = load_cell_lock_hash(0, Source::Input)?;
    let output_lock_hash = load_cell_lock_hash(0, Source::Output)?;
    if input_lock_hash != output_lock_hash {
        return Err(Error::RegistryCellDisallowTransfer);
    }
    // Parse cell data to get registry smt root hash
    let output_registry = Registry::from_data(&load_cell_data(0, Source::Output)?[..])?;
    let input_registry = Registry::from_data(&load_cell_data(0, Source::Input)?[..])?;
    if output_registry.smt_root.is_none() {
        return Err(Error::RegistryCellSMTRootError);
    }

    // Parse witness_args.input_type to get smt leaves and proof to verify smt proof
    let registry_witness_type = load_witness_args(0, Source::Input)?.input_type();
    let registry_entries = registry_witness_type
        .to_opt()
        .ok_or(Error::ItemMissing)
        .map(|witness_type| {
            let witness_type_: Bytes = witness_type.unpack();
            CotaNFTRegistryEntries::from_slice(&witness_type_[..])
        })?
        .map_err(|_| Error::WitnessTypeParseError)?;

    let mut context = unsafe { CKBDLContext::<[u8; 128 * 1024]>::new() };

    let mut lock_hashes: Vec<[u8; 32]> = Vec::new();
    let mut lock_hash_bytes = [0u8; 32];
    let mut keys: Vec<u8> = Vec::new();
    let mut values: Vec<u8> = Vec::new();
    for registry in registry_entries.registries() {
        keys.extend(registry.lock_hash().as_slice());
        values.extend(registry.state().as_slice());
        lock_hash_bytes.copy_from_slice(registry.lock_hash().as_slice());
        lock_hashes.push(lock_hash_bytes);
    }

    let proof: Vec<u8> = registry_entries.proof().raw_data().to_vec();

    let lib_ckb_smt = LibCKBSmt::load(&mut context);

    if let Some(smt_root) = output_registry.smt_root {
        lib_ckb_smt
            .smt_verify(&smt_root, &keys[..], &values[..], &proof[..])
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }

    if let Some(smt_root) = input_registry.smt_root {
        values.clear();
        for _ in registry_entries.registries() {
            values.extend(&BYTE32_ZEROS);
        }
        lib_ckb_smt
            .smt_verify(&smt_root[..], &keys[..], &values[..], &proof[..])
            .map_err(|_| Error::SMTProofVerifyFailed)?;
    }

    if check_cota_cell_exist(Source::Input) || !check_cota_cell_exist(Source::Output) {
        return Err(Error::RegistryCoTANFTExistError);
    }

    let cota_lock_hashes = load_output_cota_lock_hashes();
    lock_hashes.sort_unstable();
    if lock_hashes != cota_lock_hashes {
        return Err(Error::RegistryKeysNotEqualLockHashes);
    }

    Ok(())
}

pub fn main() -> Result<(), Error> {
    let registry_type = load_script()?;
    let type_args: Bytes = registry_type.args().unpack();
    if type_args.len() != TYPE_ARGS_LEN {
        return Err(Error::TypeArgsInvalid);
    }

    match parse_registry_action(&registry_type)? {
        Action::Create => handle_creation(&registry_type)?,
        Action::Update => handle_update()?,
    }

    Ok(())
}
