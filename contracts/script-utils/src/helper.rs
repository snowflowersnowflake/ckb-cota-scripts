use crate::constants::{COTA_TYPE_CODE_HASH, REGISTRY_TYPE_CODE_HASH, TYPE};
use crate::error::Error;
use alloc::vec::Vec;
use ckb_std::{
    ckb_constants::Source,
    ckb_types::{bytes::Bytes, packed::*, prelude::*},
    high_level::{
        load_cell, load_cell_lock, load_cell_lock_hash, load_cell_type, load_witness_args,
        QueryIter,
    },
};
use core::result::Result;
use cota_smt::smt::blake2b_256;

const TYPE_ARGS_LEN: usize = 20;

pub enum Action {
    Create,
    Update,
}

fn parse_type_opt(type_opt: &Option<Script>, predicate: &dyn Fn(&Script) -> bool) -> bool {
    match type_opt {
        Some(type_) => predicate(type_),
        None => false,
    }
}

pub fn count_cells_by_type(source: Source, predicate: &dyn Fn(&Script) -> bool) -> usize {
    QueryIter::new(load_cell_type, source)
        .filter(|type_opt| parse_type_opt(&type_opt, predicate))
        .count()
}

pub fn load_output_index_by_type(type_script: &Script) -> Option<usize> {
    QueryIter::new(load_cell_type, Source::Output).position(|type_opt| {
        type_opt.map_or(false, |type_| type_.as_slice() == type_script.as_slice())
    })
}

pub fn load_group_input_witness_args_with_type(type_script: &Script) -> Result<WitnessArgs, Error> {
    let lock_script: Script = QueryIter::new(load_cell_type, Source::Input)
        .position(|type_opt| {
            type_opt.map_or(false, |type_| type_.as_slice() == type_script.as_slice())
        })
        .map(|index| load_cell_lock(index, Source::Input).map_or(Err(Error::Encoding), Ok))
        .map_or(Err(Error::Encoding), |lock_| lock_)?;

    QueryIter::new(load_cell_lock, Source::Input)
        .position(|lock| lock.as_slice() == lock_script.as_slice())
        .map(|index| {
            load_witness_args(index, Source::Input).map_err(|_e| Error::GroupInputWitnessNoneError)
        })
        .map_or(Err(Error::GroupInputWitnessNoneError), |witness_args| {
            witness_args
        })
}

pub fn check_group_input_witness_is_none_with_type(type_script: &Script) -> Result<(), Error> {
    let witness_args = load_group_input_witness_args_with_type(type_script)?;
    if witness_args.lock().to_opt().is_none() {
        return Err(Error::GroupInputWitnessNoneError);
    }
    Ok(())
}

pub fn u32_from_slice(data: &[u8]) -> u32 {
    let mut buf = [0u8; 4];
    buf.copy_from_slice(data);
    u32::from_be_bytes(buf)
}

pub fn u16_from_slice(data: &[u8]) -> u16 {
    let mut buf = [0u8; 2];
    buf.copy_from_slice(data);
    u16::from_be_bytes(buf)
}

pub fn check_cota_cell_exist(source: Source) -> bool {
    QueryIter::new(load_cell_type, source).any(|type_opt| {
        if let Some(type_) = type_opt {
            return type_.code_hash().as_slice() == &COTA_TYPE_CODE_HASH
                && type_.hash_type().as_slice() == &[TYPE];
        }
        return false;
    })
}

pub fn load_output_cota_lock_hashes() -> Vec<[u8; 32]> {
    let mut lock_hashes = QueryIter::new(load_cell, Source::Output)
        .filter(|cell| {
            if let Some(type_) = cell.type_().to_opt() {
                return type_.code_hash().as_slice() == &COTA_TYPE_CODE_HASH
                    && type_.hash_type().as_slice() == &[TYPE];
            }
            return false;
        })
        .map(|cell| blake2b_256(cell.lock().as_slice()))
        .collect::<Vec<[u8; 32]>>();
    lock_hashes.sort_unstable();
    lock_hashes
}

pub fn check_registry_cells_exist() -> Result<bool, Error> {
    Ok([
        load_cell_type(0, Source::Input)?,
        load_cell_type(0, Source::Output)?,
    ]
    .iter()
    .all(|type_opt| {
        if let Some(type_) = type_opt {
            return type_.code_hash().as_slice() == &REGISTRY_TYPE_CODE_HASH
                && type_.hash_type().as_slice() == &[TYPE];
        }
        return false;
    }))
}

pub fn check_type_args_not_equal_lock_hash(type_: &Script, source: Source) -> Result<bool, Error> {
    let lock_hash = load_cell_lock_hash(0, source)?;
    let type_args: Bytes = type_.args().unpack();
    Ok(type_args[..] != lock_hash[0..TYPE_ARGS_LEN])
}
